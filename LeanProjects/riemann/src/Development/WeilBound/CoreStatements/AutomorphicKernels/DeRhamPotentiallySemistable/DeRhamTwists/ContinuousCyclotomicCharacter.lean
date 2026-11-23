import Development.WeilBound.CoreStatements.AutomorphicKernels.DeRhamPotentiallySemistable.DeRhamPlusCondition.IsDRPlus

noncomputable section

namespace DeRhamTwist.Twist

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst

variable {l : ℕ} [Fact l.Prime]

def chi0 (l : ℕ) [Fact l.Prime] : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (PadicAlgCl l) l).comp
    (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l))

theorem continuous_cyclotomic_character : Continuous (chi0 l) :=
  cyclotomicCharacter.continuous l ℚ_[l] (PadicAlgCl l)

theorem cycloChar_toBot (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    cycloChar ⊥ (toBot g) = chi0 l g := rfl

theorem tQ_eq : tQ l = algebraMap (BdRp l) (BdR l) (tBdR l) := by
  show algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
  rw [tA, ACris.iota_periodT]
  rfl

theorem tQ_ne : tQ l ≠ 0 := by
  rw [tQ_eq]
  exact algebraMap_tBdR_ne_zero

theorem σD_tQ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    σD g (tQ l) = qQ l ((chi0 l g : ℤ_[l]) : ℚ_[l]) * tQ l := by
  rw [tQ_eq]
  show galBdRField (toBot g) _ = _
  rw [galBdRField_algebraMap, gal_smul_tBdR, map_mul]
  rfl

def sv (n : ℕ) (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : ℚ_[l] :=
  ((((chi0 l g)⁻¹ ^ n : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])

def sc (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (n : ℕ) : K.fixingSubgroup →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    (((chi0 l).comp K.fixingSubgroup.subtype)⁻¹ ^ n)

def twist (K : IntermediateField ℚ_[l] (PadicAlgCl l)) {d : ℕ}
    (ρ : K.fixingSubgroup →* GL (Fin d) ℚ_[l]) (n : ℕ) : K.fixingSubgroup →* GL (Fin d) ℚ_[l] where
  toFun σ := Units.map (algebraMap ℚ_[l] (Matrix (Fin d) (Fin d) ℚ_[l])).toMonoidHom (sc K n σ) * ρ σ
  map_one' := by simp
  map_mul' σ τ := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, Units.coe_map, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Algebra.commutes _ _

end DeRhamTwist.Twist
