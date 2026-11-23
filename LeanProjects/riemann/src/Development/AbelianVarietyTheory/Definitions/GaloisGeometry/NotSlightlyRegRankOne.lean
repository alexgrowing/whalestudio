import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OddOrSlightlyRegIffOfEven

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec
open GlobalTheory.CBGal

namespace GlobalTheory.CBGal.Model
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem not_slightlyReg_rank_one (π : CuspSub E 1) : ¬ SlightlyReg π := by
  rintro ⟨τ, z, -, -, i, j, -, hj, -⟩
  have := j.2; omega

theorem triv_oddOr : OddOrSlightlyReg (CuspSub.triv E (le_refl 1)) ∧ ¬ SlightlyReg (CuspSub.triv E (le_refl 1)) :=
  ⟨OddOrSlightlyReg.of_odd _ odd_one, not_slightlyReg_rank_one _⟩

theorem not_slightlyReg_of_not_hasInfChar (π : CuspSub E a) (ha : 2 ≤ a) (h : ∀ τ m, ¬ (CG.mk π).HasInfChar τ m) : ¬ SlightlyReg π := by
  rintro ⟨τ, z, hz, hs, -⟩
  have e : (CG.mk π).infChar τ = Multiset.replicate a 0 := by
    unfold CG.infChar; rw [dif_neg (by simpa using h τ)]
  rw [e] at hz
  have h0 : z ⟨0, by omega⟩ ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
  have h1 : z ⟨1, by omega⟩ ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
  rw [← hz] at h0 h1
  have := hs (show (⟨0, by omega⟩ : Fin a) < ⟨1, by omega⟩ from by simp [Fin.lt_def])
  simp only at this
  rw [Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1] at this
  exact lt_irrefl _ this

theorem slightlyReg_twist_of (π : CuspSub E a) (χ : HChar E) (h : SlightlyReg π) : SlightlyReg (π.twist χ) := by
  obtain ⟨τ, z, hz, hs, i, j, hi, hj, hg⟩ := h
  by_cases hm : ∃ m, (CG.mk π).HasInfChar τ m
  · obtain ⟨m, hm⟩ := hm
    refine ⟨τ, fun k => z k + expo χ τ, ?_, ?_, i, j, hi, hj, ?_⟩
    · have h2 := (hm.twist χ).infChar_eq
      rw [CG.twist_mk] at h2
      rw [h2, ← hm.infChar_eq, hz, Multiset.map_map]; rfl
    · intro x y hxy; simpa using hs hxy
    · simp; linarith
  · exfalso
    have e : (CG.mk π).infChar τ = Multiset.replicate a 0 := by
      unfold CG.infChar; rw [dif_neg hm]
    rw [e] at hz
    have h0 : z i ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    have h1 : z j ∈ Finset.univ.val.map z := Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)
    rw [← hz] at h0 h1
    rw [Multiset.eq_of_mem_replicate h0, Multiset.eq_of_mem_replicate h1] at hg
    norm_num at hg

theorem slightlyReg_twist (π : CuspSub E a) (χ : HChar E) : SlightlyReg (π.twist χ) ↔ SlightlyReg π := by
  refine ⟨fun h => ?_, slightlyReg_twist_of π χ⟩
  have e : (π.twist χ).twist χ⁻¹ = π := by rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]
  simpa [e] using slightlyReg_twist_of _ χ⁻¹ h

theorem oddOrSlightlyReg_twist (π : CuspSub E a) (χ : HChar E) :
    OddOrSlightlyReg (π.twist χ) ↔ OddOrSlightlyReg π := or_congr Iff.rfl (slightlyReg_twist π χ)

end GlobalTheory.CBGal.Model

end
