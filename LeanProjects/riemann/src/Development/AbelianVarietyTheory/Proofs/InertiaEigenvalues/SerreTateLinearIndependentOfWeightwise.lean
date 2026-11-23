import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.SerreTateIndep

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)}

theorem chiC_add (i j : ℤ) (g : GQ l) : chiC χ (i + j) g = chiC χ i g * chiC χ j g := by
  simp [chiC, zpow_add]

theorem twAct_twist (i j : ℤ) (g : GQ l) (y : Fin r → PadicComplex l) :
    twAct act χ (i + j) U g y = chiC χ i g • twAct act χ j U g y := by
  unfold twAct
  rw [chiC_add, mul_smul]

theorem twAct_comb {n : ℕ} (i : ℤ) (g : GQ l) (c : Fin n → PadicComplex l)
    (x : Fin n → Fin r → PadicComplex l) :
    twAct act χ i U g (∑ k, c k • x k) = ∑ k, act g (c k) • twAct act χ i U g (x k) := by
  unfold twAct
  have : (fun b => act g ((∑ k, c k • x k) b)) = ∑ k, act g (c k) • fun b => act g (x k b) := by
    funext b; simp [Finset.sum_apply]
  rw [this, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul, smul_comm]

theorem twAct_zero (i : ℤ) (g : GQ l) : twAct act χ i U g 0 = 0 := by
  unfold twAct
  have : (fun b => act g ((0 : Fin r → PadicComplex l) b)) = 0 := by
    funext b; simp
  rw [this, Matrix.mulVec_zero, smul_zero]

theorem linearIndependent_of_weightwise (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l))
    (hinv : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ)
    (he : ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k)
    (hE : ∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) →
      ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) :
    LinearIndependent (PadicComplex l) e := by
  classical
  have key : ∀ (s : Finset (Fin n)) (c : Fin n → PadicComplex l), (∀ k, k ∉ s → c k = 0) →
      ∑ k, c k • e k = 0 → ∀ k, c k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c hc _ k; exact hc k (by simp)
    | insert k0 s hk0 ih =>
      intro c hc hsum
      by_cases h0 : c k0 = 0
      · refine ih c (fun k hk => ?_) hsum
        by_cases hkk : k = k0
        · rw [hkk]; exact h0
        · exact hc k (by simp [hkk, hk])
      exfalso
      set d : Fin n → PadicComplex l := fun k => (c k0)⁻¹ * c k with hd
      have hd0 : d k0 = 1 := inv_mul_cancel₀ h0
      have hds : ∑ k, d k • e k = 0 := by
        simp only [hd, mul_smul]
        rw [← Finset.smul_sum, hsum, smul_zero]
      have hfix : ∀ k, ∀ g ∈ G, chiC χ (u k0 - u k) g * act g (d k) = d k := by
        intro k g hg
        have h1 : ∑ k, (chiC χ (u k0 - u k) g * act g (d k)) • e k = 0 := by
          have h := twAct_comb (act := act) (χ := χ) (U := U) (u k0) g d e
          rw [hds, twAct_zero] at h
          rw [h]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [← sub_add_cancel (u k0) (u k), twAct_twist, he g hg k]
          rw [smul_smul, mul_comm]
        have h2 := ih (fun k => chiC χ (u k0 - u k) g * act g (d k) - d k) (fun k hk => ?_) ?_ k
        · exact sub_eq_zero.1 h2
        · by_cases hkk : k = k0
          · subst hkk
            simp [hd0, chiC]
          · have : c k = 0 := hc k (by simp [hkk, hk])
            simp [hd, this]
        · simp only [sub_smul, Finset.sum_sub_distrib, h1, hds, sub_self]
      have hex : ∀ k, ∃ x : ↥E, (((x : ↥E) : Om l) : PadicComplex l) = d k ∧ (u k ≠ u k0 → x = 0) := by
        intro k
        by_cases hu : u k = u k0
        · obtain ⟨x, hx, hxd⟩ := (hinv _ _ (hfix k)).2 (by rw [hu, sub_self])
          exact ⟨⟨x, hx⟩, hxd, fun h => (h hu).elim⟩
        · refine ⟨0, ?_, fun _ => rfl⟩
          rw [(hinv _ _ (hfix k)).1 (sub_ne_zero.2 (Ne.symm hu))]
          simp
      choose x hx hx0 using hex
      have h3 := hE (u k0) x hx0 (by simp only [hx, hds]) k0
      have h4 := hx k0
      rw [h3, hd0] at h4
      simp at h4
  exact Fintype.linearIndependent_iff.2 fun c hc => key Finset.univ c (by simp) hc

end GlobalTheory.SerreTateIndep
