
pub struct XorShift128 {
    x: u32,
    y: u32,
    z: u32,
    w: u32,
}

impl XorShift128 {
    pub fn new_with_seed(seed: u32) -> XorShift128 {
        let mut res = XorShift128 {
            x: 123456789,
            y: 362436069,
            z: 521288629,
            w: seed,
        };
        for _ in 0..10 {
            for _ in 0..res.gen_mod(32) {
                res.gen();
            }
        }
        res
    }
    pub fn new() -> XorShift128 {
        Self::new_with_seed(88675123)
    }
    pub fn gen(&mut self) -> u32 {
        let t = self.x ^ (self.x << 11);
        self.x = self.y;
        self.y = self.z;
        self.z = self.w;
        self.w = (self.w ^ (self.w >> 19)) ^ (t ^ (t >> 8));
        self.w
    }
    pub fn gen_u64(&mut self) -> u64 {
        let high = (self.gen() as u64) << 32;
        let low = self.gen() as u64;
        high | low
    }
    pub fn gen_mod(&mut self, n: usize) -> usize {
        (self.gen() % (n as u32)) as usize
    }
    pub fn gen_range(&mut self, i: usize, k: usize) -> usize {
        self.gen_mod(k - i) + i
    }
    pub fn gen_f64(&mut self) -> f64 {
        self.gen() as f64 / (1i64 << 32) as f64
    }
    pub fn shuffle<T>(&mut self, xs: &mut [T]) {
        let n = xs.len();
        for i in (1..n).rev() {
            let k = self.gen_mod(i) as usize;
            xs.swap(i, k);
        }
    }
}
