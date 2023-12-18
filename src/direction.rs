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

/// Type declaring whether to turn left or right or keep straight ahead
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Turn {
    Left,
    Right,
    Straight,
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

    /// Give the new direction after doing a turn.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Turn, StraightDirection};
    /// assert!(StraightDirection::North.turn(Turn::Right) == StraightDirection::East);
    /// assert!(StraightDirection::West.turn(Turn::Right) == StraightDirection::North);
    /// assert!(StraightDirection::North.turn(Turn::Left) == StraightDirection::West);
    /// assert!(StraightDirection::West.turn(Turn::Left) == StraightDirection::South);
    pub fn turn(&self, way: Turn) -> StraightDirection {
        match way {
            Turn::Straight => *self,
            Turn::Left => {
                match self {
                    StraightDirection::North => StraightDirection::West,
                    StraightDirection::East => StraightDirection::North,
                    StraightDirection::South => StraightDirection::East,
                    StraightDirection::West => StraightDirection::South,
                }
            }
            Turn::Right => {
                match self {
                    StraightDirection::North => StraightDirection::East,
                    StraightDirection::East => StraightDirection::South,
                    StraightDirection::South => StraightDirection::West,
                    StraightDirection::West => StraightDirection::North,
                }
            }
        }
    }
}

/// Bi-directional straight pipes
///
/// Pipes can go straight north to/from south or east to/from west, or can bend
/// 90 degrees left or right.
#[derive(PartialEq, Eq, Debug)]
pub enum Pipe {
    EastWest,
    NorthSouth,
    NorthEast,
    NorthWest,
    SouthWest,
    SouthEast,
}

impl std::convert::Into<[StraightDirection;2]> for Pipe {
    /// Returns an array of which direction each end of the pipe is
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let directions: [StraightDirection;2] = Pipe::EastWest.into();
    /// assert!(directions.contains(&StraightDirection::East) &&
    ///     directions.contains(&StraightDirection::West));
    fn into(self) -> [StraightDirection;2] {
        match self {
            Pipe::EastWest => [StraightDirection::East, StraightDirection::West],
            Pipe::NorthSouth => [StraightDirection::North, StraightDirection::South],
            Pipe::NorthEast => [StraightDirection::North, StraightDirection::East],
            Pipe::NorthWest => [StraightDirection::North, StraightDirection::West],
            Pipe::SouthWest => [StraightDirection::South, StraightDirection::West],
            Pipe::SouthEast => [StraightDirection::South, StraightDirection::East],
        }
    }
}

impl std::convert::TryFrom<[StraightDirection;2]> for Pipe {
    type Error = String;

    /// Given two straight directions, try to make a pipe
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let pipe_valid = Pipe::try_from([StraightDirection::South, StraightDirection::East]);
    /// let pipe_invalid = Pipe::try_from([StraightDirection::North, StraightDirection::North]);
    /// assert!(pipe_valid == Ok(Pipe::SouthEast));
    /// assert!(pipe_invalid.is_err())
    fn try_from(value: [StraightDirection;2]) -> Result<Self, Self::Error> {
        if value.contains(&StraightDirection::North) {
            if value.contains(&StraightDirection::West) {
                Ok(Pipe::NorthWest)
            } else if value.contains(&StraightDirection::South) {
                Ok(Pipe::NorthSouth)
            } else if value.contains(&StraightDirection::East) {
                Ok(Pipe::NorthEast)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
        } else if value.contains(&StraightDirection::South) {
            if value.contains(&StraightDirection::West) {
                Ok(Pipe::SouthWest)
            } else if value.contains(&StraightDirection::East) {
                Ok(Pipe::SouthEast)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
        } else if value.contains(&StraightDirection::East) &&
            value.contains(&StraightDirection::West) {
                Ok(Pipe::EastWest)
            } else {
                Err(format!("{:?}: Cannot translate into pipe", value))
            }
    }
}

impl std::fmt::Display for Pipe {
    /// Draw the pipe using Unicode characters
    ///
    /// # Examples
    ///
    ///```
    /// use rust_tools::direction::Pipe;
    /// println!("{}", Pipe::SouthWest);
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Pipe::EastWest   => write!(f, "{}", '─'),
            Pipe::NorthSouth => write!(f, "{}", '│'),
            Pipe::NorthEast  => write!(f, "{}", '╰'),
            Pipe::NorthWest  => write!(f, "{}", '╯'),
            Pipe::SouthWest  => write!(f, "{}", '╮'),
            Pipe::SouthEast  => write!(f, "{}", '╭'),
        }
    }
}

impl Pipe {
    /// Follow the pipe. Since the pipe is bidirectional, `dir` is used to
    /// determine in which direction to go through the pipe. `dir` is the
    /// direction of the last move.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// assert!(Pipe::NorthEast.follow(StraightDirection::North, (2,3)) ==
    ///     Some((StraightDirection::East, (3,3))));
    /// assert!(Pipe::NorthSouth.follow(StraightDirection::North, (2,3)) ==
    ///     Some((StraightDirection::North, (2,2))));
    /// assert!(Pipe::EastWest.follow(StraightDirection::North, (2,3)) == None);
    /// ```
    pub fn follow(&self, from: StraightDirection, curr: (usize, usize)) -> Option<(StraightDirection, (usize, usize))> {
        let other = self.directions().into_iter().filter(|&e| e != from).collect::<Vec<_>>();
        if other.len() != 1 {
            return None;
        }

        let to = match (from, other[0]) {
            (StraightDirection::North, StraightDirection::South) => StraightDirection::North,
            (StraightDirection::South, StraightDirection::North) => StraightDirection::South,
            (_, dir) => dir,
        };

        if let Some(result) = to.follow(curr, 1) {
            Some((to, result))
        } else {
            None
        }
    }

    /// Returns from <-> to directions.
    ///
    /// # Examples
    ///
    /// ```
    /// use rust_tools::direction::{Pipe, StraightDirection};
    /// let dir = Pipe::NorthEast.directions();
    /// assert!(dir.contains(&StraightDirection::North));
    /// assert!(dir.contains(&StraightDirection::East));
    /// ```
    pub fn directions(&self) -> [StraightDirection;2] {
        match self {
            Pipe::EastWest   => [StraightDirection::East, StraightDirection::West],
            Pipe::NorthSouth => [StraightDirection::North, StraightDirection::South],
            Pipe::NorthEast  => [StraightDirection::North, StraightDirection::East],
            Pipe::NorthWest  => [StraightDirection::North, StraightDirection::West],
            Pipe::SouthWest  => [StraightDirection::South, StraightDirection::West],
            Pipe::SouthEast  => [StraightDirection::South, StraightDirection::East],
        }
    }
}

