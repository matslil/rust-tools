//! This modules is about everything related to directions.

/// Straight directions goes straight to any of the four directions:
/// north, south, east, west.
/// It can translate coordinates to directions, translate coordinates
/// given direction and distance, turn etc.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum StraightDirection {
    North,
    East,
    South,
    West
}

impl StraightDirection {
    /// Translate from and to coordinates into a direction pointing
    /// from `from` to `to`. If the coordinates are the same, or
    /// if they do not go strictly in any direction, None is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::from_pos((0, 0), (13, 0)) == Some(StraightDirection::West));
    /// assert!(StraightDirection::from_pos((0, 0), (13, 13)) == None);
    pub fn from_pos(from: (usize, usize), to: (usize, usize)) -> Option<Self> {
        let north_south = match to.1.cmp(&from.1) {
            std::cmp::Ordering::Greater => Some(StraightDirection::North),
            std::cmp::Ordering::Less => Some(StraightDirection::South),
            _ => None,
        };
        let east_west = match to.0.cmp(&from.0) {
            std::cmp::Ordering::Greater => Some(StraightDirection::West),
            std::cmp::Ordering::Less => Some(StraightDirection::East),
            _ => None,
        };

        println!("{:?} {:?}", north_south, east_west);
        match (north_south, east_west) {
            (None, None) => None,
            (Some(_), Some(_)) => None,
            (Some(d), None) => Some(d),
            (None, Some(d)) => Some(d),
        }
    }

    /// Calculate a new coordinate given a `from` coordinate, direction and a
    /// distance. Returns None if any coordinate becomes negative.
    ///
    /// # Examples
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// let dir = StraightDirection::North;
    /// assert!(dir.follow((13, 13), 3) == Some((13usize, 10usize)));
    /// assert!(dir.follow((0, 0), 1) == None);
    pub fn follow(&self, from: (usize, usize), distance: usize) -> Option<(usize, usize)> {
        match self {
            StraightDirection::North => if from.1 >= distance {
                Some((from.0, from.1 - distance))
            } else {
                None
            }
            StraightDirection::East => Some((from.0 + 1, from.1)),
            StraightDirection::South => Some((from.0, from.1 + 1)),
            StraightDirection::West => if from.0 >= distance {
                Some((from.0 - distance, from.1))
            } else {
                None
            }
        }
    }

    /// Give the opposite direction.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::North.opposite() == StraightDirection::South);
    /// assert!(StraightDirection::West.opposite() == StraightDirection::East);
    pub fn opposite(&self) -> StraightDirection {
        match self {
            StraightDirection::North => StraightDirection::South,
            StraightDirection::East => StraightDirection::West,
            StraightDirection::South => StraightDirection::North,
            StraightDirection::West => StraightDirection::East,
        }
    }

    /// Give the new direction if turning right.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::North.right() == StraightDirection::East);
    /// assert!(StraightDirection::West.right() == StraightDirection::North);
    pub fn right(&self) -> StraightDirection {
        match self {
            StraightDirection::North => StraightDirection::East,
            StraightDirection::East => StraightDirection::South,
            StraightDirection::South => StraightDirection::West,
            StraightDirection::West => StraightDirection::North,
        }
    }

    /// Give the new direction if turning left.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::StraightDirection;
    /// assert!(StraightDirection::North.left() == StraightDirection::West);
    /// assert!(StraightDirection::West.left() == StraightDirection::South);
    pub fn left(&self) -> StraightDirection {
        match self {
            StraightDirection::North => StraightDirection::West,
            StraightDirection::East => StraightDirection::North,
            StraightDirection::South => StraightDirection::East,
            StraightDirection::West => StraightDirection::South,
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Dir {
    EastWest,   // |
    NorthSouth, // -
    NorthEast,  // L
    NorthWest,  // J
    SouthWest,  // 7
    SouthEast,  // F
    Ground,     // .
    Start,      // S
}

impl std::convert::From<char> for Dir {
    fn from(value: char) -> Self {
        match value {
            '|' => Dir::NorthSouth,
            '-' => Dir::EastWest,
            'L' => Dir::NorthEast,
            'J' => Dir::NorthWest,
            '7' => Dir::SouthWest,
            'F' => Dir::SouthEast,
            '.' => Dir::Ground,
            'S' => Dir::Start,
            _   => panic!("{}: Unknown character", value),
        }
    }
}

impl std::convert::From<[StraightDirection;2]> for Dir {
    fn from(value: [StraightDirection;2]) -> Self {
        if value.contains(&StraightDirection::North) {
            if value.contains(&StraightDirection::East) {
                Dir::NorthEast
            } else if value.contains(&StraightDirection::South) {
                Dir::NorthSouth
            } else {
                Dir::NorthWest
            }
        } else if value.contains(&StraightDirection::South) {
            if value.contains(&StraightDirection::East) {
                Dir::SouthEast
            } else {
                Dir::SouthWest
            }
        } else {
            Dir::EastWest
        }
    }
}

impl std::fmt::Display for Dir {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Dir::EastWest   => write!(f, "{}", '─'),
            Dir::NorthSouth => write!(f, "{}", '│'),
            Dir::NorthEast  => write!(f, "{}", '╰'),
            Dir::NorthWest  => write!(f, "{}", '╯'),
            Dir::SouthWest  => write!(f, "{}", '╮'),
            Dir::SouthEast  => write!(f, "{}", '╭'),
            Dir::Ground     => write!(f, "{}", '.'),
            Dir::Start      => write!(f, "{}", '▒'),
        }
    }
}

impl Dir {
    fn next(&self, prev: &(usize, usize), curr: &(usize, usize)) -> (usize, usize) {
        let diff: (isize, isize) =
            (prev.0 as isize - curr.0 as isize,
             prev.1 as isize - curr.1 as isize);

        let apply: (isize, isize) = match self {
            Dir::EastWest   => if diff == (-1, 0) {
                (2, 0)
            } else {
                (-2, 0)
            }
            Dir::NorthSouth => if diff == (0, -1) {
                (0, 2)
            } else {
                (0, -2)
            }
            Dir::NorthEast  => if diff == (0, -1) {
                (1, 1)
            } else {
                (-1, -1)
            }
            Dir::NorthWest  => if diff == (0, -1) {
                (-1, 1)
            } else {
                (1, -1)
            }
            Dir::SouthWest  => if diff == (-1, 0) {
                (1, 1)
            } else {
                (-1, -1)
            }
            Dir::SouthEast  => if diff == (1, 0) {
                (-1, 1)
            } else {
                (1, -1)
            }
            _               => panic!("{:?}: StraightDirection not supported!", self),
        };

        ((prev.0 as isize + apply.0) as usize, (prev.1 as isize + apply.1) as usize)
    }

    // Returns from <-> to directions
    fn directions(&self) -> Vec<StraightDirection> {
        match self {
            Dir::EastWest   => vec![StraightDirection::East, StraightDirection::West],
            Dir::NorthSouth => vec![StraightDirection::North, StraightDirection::South],
            Dir::NorthEast  => vec![StraightDirection::North, StraightDirection::East],
            Dir::NorthWest  => vec![StraightDirection::North, StraightDirection::West],
            Dir::SouthWest  => vec![StraightDirection::South, StraightDirection::West],
            Dir::SouthEast  => vec![StraightDirection::South, StraightDirection::East],
            Dir::Ground     => Vec::new(),
            Dir::Start      => Vec::new(),
        }
    }
}



struct Map {
    map: Vec<Vec<Dir>>,
}

fn prev(visited: &Vec<(usize, usize)>) -> &(usize, usize) {
    assert!(visited.len() > 1);
    &visited[visited.len() - 2]
}

fn curr(visited: &Vec<(usize, usize)>) -> &(usize, usize) {
    assert!(visited.len() > 0);
    &visited[visited.len() -1]
}

