import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

theorem UpperTheory.Reformulated.B.Qf14.phi_mul :
    ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp] [inst_2 : Field K₀] [inst_3 : Field K]
      [inst_4 :
        @Algebra Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2)))]
      [inst_5 :
        @Algebra Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3)))]
      [inst_6 :
        @Algebra K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3)))]
      [inst_7 :
        @IsScalarTower Qp K₀ K
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_6)
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_5)]
      {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR]
      [inst_10 :
        @Algebra Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8))]
      [inst_11 :
        @Algebra K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8))]
      [inst_12 :
        @IsScalarTower Qp K₀ B
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_11)
          (@Algebra.toSMul Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)]
      [inst_13 :
        @Algebra Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_14 :
        @Algebra K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_15 :
        @Algebra K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9))]
      [inst_16 :
        @IsScalarTower Qp K BdR
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_5)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_15)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_13)]
      [inst_17 :
        @IsScalarTower K₀ K BdR
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_3))) inst_6)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_15)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_14)]
      [inst_18 :
        @IsScalarTower Qp K₀ BdR
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_2))) inst_4)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_14)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_9)) inst_13)]
      (PD :
        @Formalism.WeaklyAdmissibleFiltrations.PeriodData G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
          inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18)
      {E : Type} [inst_19 : Field E]
      [inst_20 :
        @Algebra Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))]
      (x y :
        @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
          (@Semiring.toAddCommMonoid E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
          (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
          (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
          (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)),
      @Eq
        (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
          (@AddCommGroup.toAddCommMonoid E
            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
          (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
          (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
          (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
        (@DFunLike.coe
          (@LinearMap E E (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@RingHom.id E
              (@Semiring.toNonAssocSemiring E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20))))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (fun
              (x :
                @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
            @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@LinearMap.instFunLike E E
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20 E
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                  inst_20)))
            (@RingHom.id E
              (@Semiring.toNonAssocSemiring E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
          (@Formalism.WeaklyAdmissibleFiltrations.φVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10 inst_11
            inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
            (@Semiring.toModule E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20))
          (@HMul.hMul
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@Semiring.toAddCommMonoid E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@instHMul
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@Algebra.TensorProduct.instMul Qp E B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                      (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_19)))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.to_smulCommClass Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring B
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing B
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing B (@CommRing.toNonUnitalCommRing B inst_8))))
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@Algebra.to_smulCommClass Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.right Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)))
            x y))
        (@HMul.hMul
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
            (@AddCommGroup.toAddCommMonoid E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
            (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
            (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
            (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
          (@instHMul
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@Algebra.TensorProduct.instMul Qp E B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E
                    (@CommRing.toNonUnitalCommRing E (@Field.toCommRing E inst_19)))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.to_smulCommClass Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring B
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing B
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing B (@CommRing.toNonUnitalCommRing B inst_8))))
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@Algebra.to_smulCommClass Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
              (@IsScalarTower.right Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)))
          (@DFunLike.coe
            (@LinearMap E E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (fun
                (x :
                  @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                    (@AddCommGroup.toAddCommMonoid E
                      (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                    (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                    (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                      inst_20)
                    (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
              @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@LinearMap.instFunLike E E
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
            (@Formalism.WeaklyAdmissibleFiltrations.φVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20))
            x)
          (@DFunLike.coe
            (@LinearMap E E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20))))
            (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
              (@AddCommGroup.toAddCommMonoid E
                (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
              (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (fun
                (x :
                  @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                    (@AddCommGroup.toAddCommMonoid E
                      (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                    (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                    (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                      inst_20)
                    (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                      (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)) ↦
              @TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
            (@LinearMap.instFunLike E E
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.addCommMonoid Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@TensorProduct.leftModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) E B
                (@AddCommGroup.toAddCommMonoid E
                  (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                (@Semiring.toAddCommMonoid B (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)))
                (@Semiring.toModule E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
                (@Algebra.toModule Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                  (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_8)) inst_10)
                (@IsScalarTower.to_smulCommClass Qp (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1)) E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20
                  E
                  (@AddCommGroup.toAddCommMonoid E
                    (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19))))
                  (@Semiring.toModule E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
                  (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)
                  (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19)))
                    inst_20)))
              (@RingHom.id E
                (@Semiring.toNonAssocSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))))
            (@Formalism.WeaklyAdmissibleFiltrations.φVB G inst Qp K₀ K inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 B BdR inst_8 inst_9 inst_10
              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 PD E inst_19 inst_20 E
              (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_19)))
              (@Semiring.toModule E
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))))
              (@Algebra.toModule Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20)
              (@IsScalarTower.right Qp E (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_1))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_19))) inst_20))
            y)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ x y
  have h : ∀ z : TensorProduct Qp E B,
      Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := E) (V := E) z
        = Algebra.TensorProduct.map (AlgHom.id E E) PD.φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact (h (x * y)).trans ((map_mul _ x y).trans (congrArg₂ (· * ·) (h x).symm (h y).symm))
