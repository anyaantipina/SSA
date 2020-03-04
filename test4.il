export function w $main(l %fmt) {
@start
  %p =l alloc4 4
  %t =w call $scanf(l %fmt, l %p)
  %x =w loadw %p
  %y =w copy 0
  jnz %x, @block1, @end
@block1
  %p =l alloc4 4
  %t =w call $scanf(l %fmt, l %p)
  %y =w loadw %p
  jnz %y, @block2, @end
@block2
  %x =w sub %x, 1
@end
  %y =w add %x, %y
  ret %y
}
