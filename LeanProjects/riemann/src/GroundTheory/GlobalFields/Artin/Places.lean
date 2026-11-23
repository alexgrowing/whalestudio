import Mathlib
import GroundTheory.GlobalFields.Artin.MackeyFrobeniusEmbed
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField

namespace GroundTheory.Global.Artin

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := ⟨σ • w.asIdeal, Ideal.IsPrime.smul σ, fun h ↦ w.ne_bot (by
    rw [← inv_smul_smul σ w.asIdeal, h, Ideal.smul_bot])⟩
  one_smul w := HeightOneSpectrum.ext (one_smul _ w.asIdeal)
  mul_smul σ τ w := HeightOneSpectrum.ext (mul_smul σ τ w.asIdeal)

@[simp]
theorem asIdeal_smul (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal :=
  rfl

end Action

section FixedField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

instance isGaloisGroup_fixedField : IsGaloisGroup H (fixedField H) L :=
  IsGaloisGroup.subgroup Gal(L/K) K L H

instance isGaloisGroup_ringOfIntegers_fixedField : IsGaloisGroup H (𝓞 (fixedField H)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (fixedField H)) (𝓞 L) (fixedField H) L

end FixedField

section Finite

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))

def subfieldPlace (x : Gal(L/K)) : HeightOneSpectrum (𝓞 (fixedField H)) :=
  (x • w).under (𝓞 (fixedField H))

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem asIdeal_subfieldPlace (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal = (x • w.asIdeal).under (𝓞 (fixedField H)) :=
  rfl

instance liesOver_subfieldPlace (x : Gal(L/K)) :
    (x • w.asIdeal).LiesOver (subfieldPlace H w x).asIdeal :=
  ⟨rfl⟩

theorem subfieldPlace_liesOver [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlace H w x).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot (x • w.asIdeal) _ v.asIdeal

theorem subfieldPlace_eq_iff (x y : Gal(L/K)) :
    subfieldPlace H w x = subfieldPlace H w y ↔
      DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) x =
        DoubleCoset.mk H (MulAction.stabilizer Gal(L/K) w.asIdeal) y := by
  rw [DoubleCoset.eq, HeightOneSpectrum.ext_iff, asIdeal_subfieldPlace, asIdeal_subfieldPlace]
  constructor
  · intro hxy
    have : (y • w.asIdeal).LiesOver ((x • w.asIdeal).under (𝓞 (fixedField H))) := ⟨hxy⟩
    obtain ⟨h, hh⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      ((x • w.asIdeal).under (𝓞 (fixedField H))) (x • w.asIdeal) (y • w.asIdeal) H
    have hh' : (h : Gal(L/K)) • x • w.asIdeal = y • w.asIdeal := hh
    refine ⟨h, h.2, (y⁻¹ * h * x)⁻¹, Subgroup.inv_mem _ ?_, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hh', inv_smul_smul]
  · rintro ⟨h, hh, d, hd, rfl⟩
    rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.1 hd,
      show h • x • w.asIdeal = (⟨h, hh⟩ : H) • (x • w.asIdeal) from rfl]
    exact (Ideal.under_smul (𝓞 (fixedField H)) (x • w.asIdeal) (⟨h, hh⟩ : H)).symm

theorem exists_subfieldPlace_eq [w.asIdeal.LiesOver v.asIdeal]
    (u : HeightOneSpectrum (𝓞 (fixedField H))) [u.asIdeal.LiesOver v.asIdeal] :
    ∃ x : Gal(L/K), subfieldPlace H w x = u := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) u.asIdeal
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q u.asIdeal v.asIdeal
  obtain ⟨x, hx⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal Q Gal(L/K)
  refine ⟨x, HeightOneSpectrum.ext ?_⟩
  rw [asIdeal_subfieldPlace, hx, ← hQ.over]

def subfieldPlaceEquiv [w.asIdeal.LiesOver v.asIdeal] :
    DoubleCoset.Quotient (H : Set Gal(L/K)) (MulAction.stabilizer Gal(L/K) w.asIdeal) ≃
      {u : HeightOneSpectrum (𝓞 (fixedField H)) // u.asIdeal.LiesOver v.asIdeal} :=
  Equiv.ofBijective
    (Quotient.lift (fun x ↦ ⟨subfieldPlace H w x, subfieldPlace_liesOver H v w x⟩)
      (fun a b hab ↦ Subtype.ext ((subfieldPlace_eq_iff H w a b).2 (Quotient.sound hab))))
    ⟨by
      rintro ⟨a⟩ ⟨b⟩ hab
      exact (subfieldPlace_eq_iff H w a b).1 (congrArg Subtype.val hab),
    by
      rintro ⟨u, hu⟩
      obtain ⟨x, hx⟩ := exists_subfieldPlace_eq H v w u
      exact ⟨DoubleCoset.mk _ _ x, Subtype.ext hx⟩⟩

@[simp]
theorem subfieldPlaceEquiv_mk [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    (subfieldPlaceEquiv H v w (DoubleCoset.mk _ _ x) : HeightOneSpectrum (𝓞 (fixedField H))) =
      subfieldPlace H w x :=
  rfl

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem stabilizer_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    MulAction.stabilizer H (x • P) =
      (MulAut.conj x • MulAction.stabilizer Gal(L/K) P : Subgroup Gal(L/K)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
  change (h : Gal(L/K)) • x • P = x • P ↔ x⁻¹ • (h : Gal(L/K)) • x • P = P
  rw [inv_smul_eq_iff]

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem inertia_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    (x • P).inertia H =
      (MulAut.conj x • P.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff, ← Ideal.coe_mem_inertia, mem_inertia_smul_iff]

end Finite

end GroundTheory.Global.Artin
