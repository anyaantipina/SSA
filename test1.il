export function w $main(l %fmt) {
@start
  %p =l alloc4 4
  %t =w call $scanf(l %fmt, l %p)
  %x =w loadw %p
@loop
  %x =w sub %x, 1
  jnz %x, @loop, @end
@end
  ret %x
}
