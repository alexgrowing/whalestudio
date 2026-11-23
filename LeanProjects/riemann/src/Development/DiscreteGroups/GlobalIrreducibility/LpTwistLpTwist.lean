import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section W

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist (x : WD h) (α β : Weil h →* ℂˣ) (hα : IsSmooth α) (hβ : IsSmooth β) (hαβ : IsSmooth (α * β)) :
    (x.lpTwist α hα).lpTwist β hβ = x.lpTwist (α * β) hαβ := by
  induction x using WD.ind with
  | hP m a =>
    rw [WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk]
    refine WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
    simp [smul_smul, mul_comm]

variable (h) in

def degDvd (n : ℕ) : Subgroup (Weil h) where
  carrier := {σ | (n : ℤ) ∣ deg σ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    show (n : ℤ) ∣ deg (a * b)
    rw [deg_mul]; exact dvd_add ha hb
  inv_mem' := fun {a} ha => by
    show (n : ℤ) ∣ deg a⁻¹
    rw [deg_inv]; exact (dvd_neg).mpr ha

theorem mem_degDvd {n : ℕ} {σ : Weil h} : σ ∈ degDvd h n ↔ (n : ℤ) ∣ deg σ := Iff.rfl

theorem index_degDvd {n : ℕ} (hn : 0 < n) : (degDvd h n).index = n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let f : Weil h →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp (degHom h)
  have hker : f.ker = degDvd h n := by
    ext σ
    rw [MonoidHom.mem_ker, mem_degDvd]
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
    obtain ⟨σ, hσ⟩ := deg_surjective (h := h) k
    refine ⟨σ, ?_⟩
    show Multiplicative.ofAdd ((deg σ : ℤ) : ZMod n) = z
    rw [hσ, hk]; rfl
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  show Nat.card (ZMod n) = n
  exact Nat.card_zmod n

end W

theorem gs_scaled {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type} [Field K] [Finite K]
    [Algebra (ZMod g) K] (η : Kˣ →* ℂˣ) (β : Kˣ) :
    ∑ᶠ z : Kˣ, (((η z)⁻¹ : ℂˣ) : ℂ) * (ψ₀ (Algebra.trace (ZMod g) K ((β : K) * z)) : ℂ) =
      (η β : ℂ) * gs ψ₀ η⁻¹ := by
  classical
  haveI := Fintype.ofFinite K
  haveI : Fintype Kˣ := inferInstance
  rw [gs, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft β⁻¹)]
  refine Finset.sum_congr rfl fun z _ => ?_
  have e1 : (β : K) * ((β⁻¹ * z : Kˣ) : K) = (z : K) := by
    rw [Units.val_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [Equiv.coe_mulLeft, e1]
  simp only [map_mul, map_inv, mul_inv, inv_inv, MonoidHom.inv_apply, Units.val_mul]
  ring

end DiscreteGroups.sglob.DzType

end
