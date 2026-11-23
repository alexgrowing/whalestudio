import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IwSemistable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatumAOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsStrictlySemistableBase

noncomputable section
open CategoryTheory AlgebraicGeometry

open scoped NumberField TensorProduct
open GlobalTheory.UPel.HT

namespace GlobalTheory.IwLevel.IwInhab

theorem five_not_unit : ¬ IsUnit ((5 : ℕ) : 𝓞 gaussOneDatum.F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ)
  have h2 : Algebra.norm ℤ ((5 : ℕ) : 𝓞 gaussOneDatum.F) = (5 : ℤ) ^ Module.finrank ℤ (𝓞 gaussOneDatum.F) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 gaussOneDatum.F)), Algebra.norm_algebraMap]; norm_num
  rw [h2] at h1
  have hpos : Module.finrank ℤ (𝓞 gaussOneDatum.F) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hpos, Int.isUnit_iff] at h1
  omega

def wG : Ideal (𝓞 gaussOneDatum.F) :=
  Classical.choose (Ideal.exists_le_maximal (Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact five_not_unit))

theorem wG_spec : Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)} ≤ wG ∧ wG.IsMaximal :=
  (Classical.choose_spec (Ideal.exists_le_maximal (Ideal.span {((5 : ℕ) : 𝓞 gaussOneDatum.F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact five_not_unit))).symm

theorem five_mem : ((5 : ℕ) : 𝓞 gaussOneDatum.F) ∈ wG := wG_spec.1 (Ideal.mem_span_singleton_self _)

instance wG_max : wG.IsMaximal := wG_spec.2
instance wG_prime : wG.IsPrime := wG_max.isPrime

theorem five_ne_zero : ((5 : ℕ) : 𝓞 gaussOneDatum.F) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)

theorem wG_ne_bot : wG ≠ ⊥ := fun h => by
  have := five_mem
  rw [h, Ideal.mem_bot] at this
  exact five_ne_zero this

abbrev RG : Type := Localization.AtPrime wG

instance : IsDiscreteValuationRing RG :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ wG_ne_bot _

def ϖG : RG := Classical.choose (IsDiscreteValuationRing.exists_irreducible RG)

theorem ϖG_irr : Irreducible ϖG := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible RG)

theorem natCast_not_mem (k : ℕ) (hk : k.Coprime 5) : ((k : ℕ) : 𝓞 gaussOneDatum.F) ∉ wG := by
  intro hkw
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hk)
  have h1 : ((u * (k : ℤ) + v * ((5 : ℕ) : ℤ) : ℤ) : 𝓞 gaussOneDatum.F) = 1 := by rw [huv]; simp
  have : (1 : 𝓞 gaussOneDatum.F) ∈ wG := by
    rw [← h1]; push_cast
    exact wG.add_mem (wG.mul_mem_left _ (by exact_mod_cast hkw)) (wG.mul_mem_left _ (by exact_mod_cast five_mem))
  exact wG_max.ne_top ((Ideal.eq_top_iff_one _).2 this)

def bG : Base gaussOneDatum RG where
  unit k hk := by
    rw [← map_natCast (algebraMap (𝓞 gaussOneDatum.F) RG), IsLocalization.AtPrime.isUnit_to_map_iff RG wG]
    exact natCast_not_mem k hk
  ρ := algebraMap (𝓞 gaussOneDatum.F) RG gaussOneDatum.ω
  ρ_root := by
    have h : gaussOneDatum.ω ^ 2 - (gaussOneDatum.tr : 𝓞 gaussOneDatum.F) * gaussOneDatum.ω +
        (gaussOneDatum.nm : 𝓞 gaussOneDatum.F) = 0 := by
      rw [← gaussOneDatum.tr_eq, ← gaussOneDatum.nm_eq]; ring
    have h' := congrArg (algebraMap (𝓞 gaussOneDatum.F) RG) h
    simpa only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero] using h'
  t _ := algebraMap (𝓞 gaussOneDatum.F) RG
  t_ω _ := rfl
  comax i j h := (h (Fin.ext (by have hi := i.isLt; have hj := j.isLt; change _ < 1 at hi hj; omega))).elim
  apart i j h := (h (Fin.ext (by have hi := i.isLt; have hj := j.isLt; change _ < 1 at hi hj; omega))).elim

def i0 : Fin gaussOneDatum.a := ⟨0, Nat.one_pos⟩

example : GlobalTheory.Et.IsStrictlySemistable ϖG (𝟙 (Spec (CommRingCat.of RG))) :=
  GlobalTheory.SemistableModel.isStrictlySemistable_base RG ϖG

end GlobalTheory.IwLevel.IwInhab
