open class Foo<X> { open fun x(): X = x() }
fun <X> m(other: Any, v: X): Foo<X> {
    class MyFoo : Foo<X>() { override fun x(): X = v }
    var l : List<MyFoo> = listOf(other).filterIsInstance<MyFoo>()
    for (mf in l) { // If 'other' was retained as MyFoo, we'll return it
        return mf
    }
    return MyFoo()
}
fun main() {
    var r1 : Foo<Int> = m<Int>("anything", 5)
    var r2 : Foo<String> = m<String>(r1, "Hi")
    System.out.println(r1.x())
    System.out.println(r2.x())
}
// This code doesn't warn, but still crashes
