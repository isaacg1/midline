use image::{Rgb, RgbImage};
use rand::prelude::*;

use std::collections::{HashMap, HashSet};
use std::f64::consts::PI;

type Color = [u8; 3];
type Location = [u32; 2];

struct SetRand<T> {
    vec: Vec<T>,
    map: HashMap<T, usize>,
}
impl<T> SetRand<T>
where
    T: std::cmp::Eq + std::hash::Hash + Copy,
{
    fn new(vec: Vec<T>) -> Self {
        let map = vec.iter().enumerate().map(|(i, t)| (*t, i)).collect();
        SetRand { vec, map }
    }
    fn choose<R: Rng>(&self, rng: &mut R) -> Option<&T> {
        self.vec.choose(rng)
    }
    fn remove(&mut self, t: &T) {
        let maybe_removal_index = self.map.remove(t);
        if let Some(removal_index) = maybe_removal_index {
            if removal_index != self.vec.len() - 1 {
                let old_last = self.vec.last().expect("At least one left");
                self.map.insert(*old_last, removal_index);
                self.vec.swap_remove(removal_index);
            } else {
                self.vec.pop();
            }
        } else {
            assert!(false)
        }
    }
    fn len(&self) -> usize {
        assert_eq!(self.vec.len(), self.map.len());
        self.vec.len()
    }
}

fn modulo(x: i64, y: u32) -> u32 {
    let bad_mod = x % y as i64;
    (bad_mod + y as i64) as u32 % y
}

fn pixel_line(loc1: [i64; 2], loc2: [i64; 2]) -> Vec<[i64; 2]> {
    if loc1[0] > loc2[0] {
        return pixel_line(loc2, loc1);
    };
    let dx = loc2[0] - loc1[0];
    let dy = (loc2[1] - loc1[1]).abs();
    let ydir = loc1[1] < loc2[1];
    if dx < dy {
        let swapped_line = pixel_line([loc1[1], loc1[0]], [loc2[1], loc2[0]]);
        return swapped_line.into_iter().map(|l| [l[1], l[0]]).collect();
    }
    let yi = if ydir { 1 } else { -1 };
    let mut delta = 2 * dy - dx;
    let mut y = loc1[1];

    let mut pixels = vec![];
    for x in loc1[0]..=loc2[0] {
        pixels.push([x, y]);
        if delta > 0 {
            y += yi;
            delta += 2 * (dy - dx);
        } else {
            delta += 2 * dy;
        }
    }
    pixels
}

// Number of pixels is 1 << (size_exp * 6).
fn make_image(size: u32, starter: usize, num_probes: u64, seed: u64) -> RgbImage {
    assert!(size <= 16);
    let mut rng = StdRng::seed_from_u64(seed);
    let side = size.pow(3);
    let mut img = RgbImage::new(side, side);
    let num_colors_per_channel: i16 = size.pow(2) as i16;
    let color_multiplier = 256 / num_colors_per_channel;
    let mut colors_to_locations: HashMap<Color, Location> = HashMap::new();
    let mut locations: HashSet<Location> = HashSet::new();
    let remaining_locations_vec: Vec<Location> = (0..side)
        .flat_map(|x| (0..side).map(move |y| [x, y]))
        .collect();
    let mut remaining_locations: SetRand<Location> =
        SetRand::new(remaining_locations_vec);
    let offset_range =
        || -(num_colors_per_channel - 1) as i16..num_colors_per_channel as i16;
    let mut offsets: Vec<[i64; 3]> = offset_range()
        .flat_map(|r| {
            offset_range().flat_map(move |g| {
                offset_range().map(move |b| {
                    [
                        (r * color_multiplier) as i64,
                        (g * color_multiplier) as i64,
                        (b * color_multiplier) as i64,
                    ]
                })
            })
        })
        .collect();
    offsets.sort_by_key(|offset| offset.iter().map(|coord| coord.pow(2)).sum::<i64>());
    let mut colors: Vec<Color> = (0..num_colors_per_channel)
        .flat_map(|r| {
            (0..num_colors_per_channel).flat_map(move |g| {
                (0..num_colors_per_channel).map(move |b| {
                    [
                        (r * color_multiplier) as u8,
                        (g * color_multiplier) as u8,
                        (b * color_multiplier) as u8,
                    ]
                })
            })
        })
        .collect();
    colors.shuffle(&mut rng);
    assert_eq!(colors.len(), remaining_locations.len());
    for (i, color) in colors.into_iter().enumerate() {
        if i % 100_000 == 0 && i > 0 {
            println!("{}", i)
        }
        let mut from = None;
        let location = if i < starter {
            loop {
                let location: Location = [rng.gen_range(0..side), rng.gen_range(0..side)];
                if !locations.contains(&location) {
                    from = Some("Starter");
                    break location;
                }
            }
        } else {
            // Find midline, generate random thing.
            let best_two_colors: Vec<Color> = offsets
                .iter()
                .filter_map(|&offset| {
                    let candidate_color = [
                        color[0] as i64 + offset[0],
                        color[1] as i64 + offset[1],
                        color[2] as i64 + offset[2],
                    ];
                    for &c in &candidate_color {
                        if c < 0 || c > 255 {
                            return None;
                        }
                    }
                    let other_color = [
                        candidate_color[0] as u8,
                        candidate_color[1] as u8,
                        candidate_color[2] as u8,
                    ];
                    Some(other_color)
                })
                .filter(|other_color| colors_to_locations.contains_key(other_color))
                .take(2)
                .collect();
            let best_two_locations: Vec<Location> = best_two_colors
                .iter()
                .map(|color| *colors_to_locations.get(color).expect("Just checked"))
                .collect();
            let loc1 = [
                best_two_locations[0][0] as i64,
                best_two_locations[0][1] as i64,
            ];
            let loc2 = [
                best_two_locations[1][0] as i64,
                best_two_locations[1][1] as i64,
            ];
            let nine_directions = (-1..=1).flat_map(|x| {
                (-1..=1)
                    .map(move |y| [x * side as i64 + loc2[0], y * side as i64 + loc2[1]])
            });
            let best_direction = nine_directions
                .min_by_key(|dir| (dir[0] - loc1[0]).pow(2) + (dir[1] - loc1[1]).pow(2))
                .expect("There were nine");
            let line = pixel_line(loc1, best_direction);
            let fixed_line: Vec<Location> = line
                .iter()
                .map(|pix| [modulo(pix[0], side), modulo(pix[1], side)])
                .collect();
            let open_on_line: Vec<Location> = fixed_line
                .into_iter()
                .filter(|pix| !locations.contains(pix))
                .collect();
            if !open_on_line.is_empty() {
                from = Some("Main");
                *open_on_line.choose(&mut rng).expect("Checked nonempty")
            } else {
                let mut maybe_location = None;
                'outer: for radius_exp in 0..((size as f64).log(2.0) * 3.0).floor() as u32
                {
                    let max_radius = 1 << radius_exp;
                    for _ in 0..num_probes {
                        let center = line.choose(&mut rng).expect("Line nonempty");
                        let radius = max_radius as f64 * rng.gen::<f64>().sqrt();
                        let theta = rng.gen::<f64>() * 2.0 * PI;
                        let offset_x = radius * theta.cos();
                        let offset_y = radius * theta.sin();
                        let target = [
                            center[0] + offset_x.round() as i64,
                            center[1] + offset_y.round() as i64,
                        ];
                        let fixed_target =
                            [modulo(target[0], side), modulo(target[1], side)];
                        if !locations.contains(&fixed_target) {
                            from = Some("Circles");
                            maybe_location = Some(fixed_target);
                            break 'outer;
                        }
                    }
                }
                if let Some(location) = maybe_location {
                    location
                } else {
                    from = Some("Fallback");
                    *remaining_locations
                        .choose(&mut rng)
                        .expect("At least one spot left")
                }
            }
        };
        let was_present = colors_to_locations.insert(color, location);
        assert!(was_present.is_none());
        let was_absent = locations.insert(location);
        if !was_absent {
            println!("{:?}", from);
            assert!(was_absent);
        }
        remaining_locations.remove(&location);
        img.put_pixel(location[0], location[1], Rgb(color));
    }
    img
}

fn main() {
    let mut args = std::env::args();
    args.next();
    let size = args.next().expect("Size").parse().expect("Integer");
    let starter = args.next().expect("Starter").parse().expect("Integer");
    let num_probes = args.next().expect("Num probes").parse().expect("Integer");
    let seed = args.next().expect("Seed").parse().expect("Integer");
    let img = make_image(size, starter, num_probes, seed);
    let filename = format!("img_{}_{}_{}_{}.png", size, starter, num_probes, seed);
    img.save(&filename).expect("Successful");
    println!("{}", filename);
}
