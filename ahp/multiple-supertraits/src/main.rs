/*
class Top a where
  fun1 :: a -> a

class Top a => Left a where
  fun2 :: a -> a

class Top a => Right a where
  fun3 :: a -> a

class Left a, Right a => Bottom a where
  fun4 :: a -> a
*/

trait Top<A> {
    fn fun1(&self, a: A) -> A;
}

trait Left<A>: Top<A> {
    fn fun2(&self, a: A) -> A;
}

trait Right<A>: Top<A> {
    fn fun3(&self, a: A) -> A;
}

trait Bottom<A>: Left<A> + Right<A> {
    fn fun4(&self, a: A) -> A;
}

struct Example;

impl Top<i32> for Example {
    fn fun1(&self, a: i32) -> i32 {
        println!("Top {a}");
        a + 1
    }
}

impl Left<i32> for Example {
    fn fun2(&self, a: i32) -> i32 {
        println!("Left {a}");
        self.fun1(a + 2)
    }
}

impl Right<i32> for Example {
    fn fun3(&self, a: i32) -> i32 {
        println!("Right {a}");
        self.fun1(a + 3)
    }
}

impl Bottom<i32> for Example {
    fn fun4(&self, a: i32) -> i32 {
        println!("Bottom {a}");
        self.fun3(self.fun2(a + 4))
    }
}

fn main() {
    let a = Example;
    println!("main {}", a.fun4(42));
}
