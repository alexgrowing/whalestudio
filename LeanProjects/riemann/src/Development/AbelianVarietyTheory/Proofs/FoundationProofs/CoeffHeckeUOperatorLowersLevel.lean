import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetPropertiesStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.LevelLower

def idx (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) : Fin l :=
  ⟨(((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩

lemma idx_cast (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) :
    ((idx l b d j : ℕ) : ZMod l) = (((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l) := by
  simp [idx, ZMod.natCast_zmod_val]

lemma idx_inj (l : ℕ) [NeZero l] (a b d : ℤ) (had : ((a * d : ℤ) : ZMod l) = 1) :
    Function.Injective (idx l b d) := by
  intro j₁ j₂ h
  have h' := congrArg (fun x : Fin l => ((x : ℕ) : ZMod l)) h
  simp only [idx_cast] at h'
  push_cast at h' had
  have e : ((j₁ : ℕ) : ZMod l) = ((j₂ : ℕ) : ZMod l) := by
    linear_combination (a : ZMod l) ^ 2 * h' -
      (((j₁ : ℕ) : ZMod l) - ((j₂ : ℕ) : ZMod l)) * (1 + (a : ZMod l) * d) * had
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at e
  simpa [Nat.mod_eq_of_lt j₁.2, Nat.mod_eq_of_lt j₂.2] using e

lemma coset (L l : ℕ) [NeZero l] (hlL : l ∣ L) (γ : SL(2, ℤ)) (hc : (L : ℤ) ∣ γ 1 0) (j : Fin l) :
    ∃ γ' : SL(2, ℤ), ((L * l : ℕ) : ℤ) ∣ γ' 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) ∧
      repU l j * (γ : M2) = (γ' : M2) * repU l (idx l (γ 0 1) (γ 1 1) j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
  have hdiv : (l : ℤ) ∣ γ 0 1 + ((j : ℕ) : ℤ) * γ 1 1 -
      (γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0) * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have hj' := idx_cast l (γ 0 1) (γ 1 1) j
    have hd1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at hj' hd1 ⊢
    rw [hj']
    linear_combination (-((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l))) * hd1 -
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) *
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) * hc0
  obtain ⟨B, hB⟩ := hdiv
  obtain ⟨m, hm⟩ := hc
  refine ⟨⟨!![γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0, B; (l : ℤ) * γ 1 0,
      γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 1 0 * hB
  · refine ⟨m, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hm]; push_cast; ring
  · simp
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [repU, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB | linear_combination -hB

end GlobalTheory.LevelLower

namespace GlobalTheory.LevelLower

lemma slz_sum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (F : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => ∑ i, F i τ) τ = ∑ i, slz k δ (F i) τ := by
  simp only [slz, Finset.mul_sum]

lemma slz_smul (k : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => c * f τ) τ = c * slz k δ f τ := by
  simp only [slz]; ring

lemma per (L : ℕ) (χ : ℤ → ℂ) (hχ : ∀ d, χ (d + L) = χ d) (m : ℤ) : ∀ d : ℤ, χ (d + m * L) = χ d := by
  refine Int.induction_on m ?_ ?_ ?_
  · intro d; simp
  · intro i ih d
    rw [show d + ((i : ℤ) + 1) * (L : ℤ) = (d + (i : ℤ) * L) + L by ring, hχ, ih]
  · intro i ih d
    have := hχ (d + (-(i : ℤ) - 1) * L)
    rw [show d + (-(i : ℤ) - 1) * (L : ℤ) + L = d + -(i : ℤ) * L by ring, ih] at this
    exact this.symm

end GlobalTheory.LevelLower

theorem GlobalTheory.Uo_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L →
    (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  intro k L l χ a hk hl hlL hχ hMF
  obtain ⟨hP, hI⟩ := hMF
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨hPU, hqs⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hl.pos hP
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hI' := (hinv (L * l) χ).mp hI
  refine ⟨hPU, ?_⟩
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (qs (Uo l a)) hk).2.2.1]
  intro γ hc
  have hg : qs (Uo l a) = fun τ => ∑ j : Fin l, slz k (repU l j) (qs a) τ := funext hqs
  have hdU : ∀ j : Fin l, 0 < (repU l j).det := by
    intro j; simp [repU, Matrix.det_fin_two_of]; exact hl.pos
  have hdγ : ∀ γ : SL(2, ℤ), 0 < (γ : M2).det := by
    intro γ; rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos

  have had : ((γ 0 0 * γ 1 1 : ℤ) : ZMod l) = 1 := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at h1 hc0 ⊢
    rw [hc0, mul_zero, sub_zero] at h1
    exact h1
  let e : Fin l ≃ Fin l := Equiv.ofBijective (GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1))
    (Finite.injective_iff_bijective.mp (GlobalTheory.LevelLower.idx_inj l _ _ _ had))
  have key : ∀ (τ : ℍ) (j : Fin l), slz k (γ : M2) (slz k (repU l j) (qs a)) τ =
      χ (γ 1 1) * slz k (repU l (e j)) (qs a) τ := by
    intro τ j
    obtain ⟨γ', h1, h2, h3⟩ := GlobalTheory.LevelLower.coset L l hlL γ hc j
    rw [← hcoc _ _ (hdU j) (hdγ γ), h3, hcoc _ _ (hdγ γ') (hdU _), hI' γ' h1,
      GlobalTheory.LevelLower.slz_smul, h2]
    obtain ⟨m, hm⟩ := hc
    have : χ (γ 1 1 - γ 1 0 * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)) = χ (γ 1 1) := by
      rw [hm, show γ 1 1 - (L : ℤ) * m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) =
        γ 1 1 + (-(m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ))) * L by ring,
        GlobalTheory.LevelLower.per L χ hχ]
    rw [this]
    rfl
  rw [hg]
  funext τ
  rw [GlobalTheory.LevelLower.slz_sum]
  simp_rw [key τ]
  rw [← Finset.mul_sum, Equiv.sum_comp e (fun j => slz k (repU l j) (qs a) τ)]
