open class Foo<X> { open fun x(): X = x() }
fun <X> m(other: Any, v: X): Foo<X> {
    class MyFoo : Foo<X>() { override fun x(): X = v }
    if (other !is MyFoo) { return MyFoo() }
    return other
}
fun main() {
    var r1 : Foo<Int> = m<Int>("anything", 5)
    var r2 : Foo<String> = m<String>(r1, "Hi")
    System.out.println(r1.x())
    System.out.println(r2.x())
}
// $ kotlinc example1.kt
// example1.kt:4:19: error: cannot check for instance of erased type 'MyFoo<X (of fun <X> m)>'.
//     if (other !is MyFoo) { return MyFoo() }
