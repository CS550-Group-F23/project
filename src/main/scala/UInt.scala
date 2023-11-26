import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.proof.check

case class SystemState(
  a: UIntReg,
  b: UIntReg
)

case class SystemInput(
  enable: UIntWire
)

case class (
  enable: UIntWire
)

case class UInt(
    width: Int,
    data: Long
) {
  require(width > 0 && width < 63)
  require(data >= 0 && data < (1L << width))

  def get(idx: Int): UInt = {
    require(idx >= 0 && idx < width)

    if (((data >> idx) & 1L) == 1)
      UInt(1, 1)
    else
      UInt(1, 0)
  }

  def get(to: Int, from: Int): UInt = {
    require(to >= from)
    require(from >= 0 && from < width)
    require(to >= 0 && to < width)

    if (to == from) {
      get(to)
    } else {
      val mask = (1L << (to - from + 1)) - 1
      UInt(to - from + 1, (data >> from) & mask)
    }
  }

  def concat(rhs: UInt): UInt = {
    require(width + rhs.width < 63)
    UInt(
      width + rhs.width,
      (data << rhs.width) | rhs.data
    )
  }

  def ##(rhs: UInt): UInt = {
    require(width + rhs.width < 63)
    concat(rhs)
  }

  def &(rhs: UInt): UInt = {
    require(width == rhs.width)
    UInt(width, data & rhs.data)
  }

  def |(rhs: UInt): UInt = {
    require(width == rhs.width)
    UInt(width, data | rhs.data)
  }

  def ^(rhs: UInt): UInt = {
    require(width == rhs.width)
    UInt(width, data ^ rhs.data)
  }

}

class UIntReg extends UInt

class UIntWire extends UInt