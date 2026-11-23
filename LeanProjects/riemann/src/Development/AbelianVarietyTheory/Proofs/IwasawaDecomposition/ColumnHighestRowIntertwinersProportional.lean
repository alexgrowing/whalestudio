import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointHighestProportional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

variable {ι : Type} {m n : ℕ}

def rowDer (n : ℕ) (τ : ι) (k l : Fin m) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ c : Fin n, (X (τ, k, c) : Pol ι m n) • pderiv (τ, l, c)

theorem rowDer_apply (τ : ι) (k l : Fin m) (P : Pol ι m n) :
    rowDer n τ k l P = rowLie n τ k l P := by
  rw [rowLie_apply, rowDer]
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]; simp

open Classical in
theorem rowLie_X (τ : ι) (k l : Fin m) (v : ι × Fin m × Fin n) :
    rowLie n τ k l (X v) = if v.1 = τ ∧ v.2.1 = l then X (τ, k, v.2.2) else 0 := by
  obtain ⟨t, i, c⟩ := v
  rw [rowLie_apply, Finset.sum_eq_single c]
  · by_cases h : t = τ ∧ i = l
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [pderiv_X_of_ne (by simpa using h)]
      simp [h]
  · intro b _ hb
    rw [pderiv_X_of_ne (by simp [hb.symm]), mul_zero]
  · simp

open Classical in

theorem rowLie_diag_comm (t t' : ι) (i k l : Fin m) :
    rowLie n t i i * rowLie n t' k l - rowLie n t' k l * rowLie n t i i =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowLie n t' k l := by
  have h : ⁅rowDer n t i i, rowDer n t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        rowDer n t' k l := by
    refine derivation_ext fun v => ?_
    obtain ⟨s, j, c⟩ := v
    simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowLie_X,
      apply_ite (rowLie n t i i), apply_ite (rowLie n t' k l), map_zero]
    by_cases h1 : t = t' <;> by_cases h2 : s = t' <;> by_cases h3 : j = l <;>
      by_cases h4 : i = k <;> by_cases h5 : i = l <;> simp_all [eq_comm]
  refine LinearMap.ext fun P => ?_
  have := DFunLike.congr_fun h P
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at this
  exact this

theorem iSup_iInf_eigenspace_rowLie :
    ⨆ κ : ι → Fin m → ℤ, (⨅ t, ⨅ i,
      Module.End.eigenspace (rowLie n t i i : Module.End ℂ (Pol ι m n)) (κ t i : ℂ)) = ⊤ := by
  rw [eq_top_iff]
  rintro P -
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => exact add_mem hP hQ
  | monomial s a =>
    refine Submodule.mem_iSup_of_mem (fun t i => ∑ c, (s (t, i, c) : ℤ)) ?_
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro t i
    rw [rowLie_apply]
    simp only [X_mul_pderiv_monomial]
    push_cast
    rw [Finset.sum_smul]
    simp only [Nat.cast_smul_eq_nsmul]

theorem exists_totalDegree_le_of_finiteDimensional {X : Type} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (Φ : X →ₗ[ℂ] Pol ι m n) : ∃ d, ∀ x, (Φ x).totalDegree ≤ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun j => (Φ (b j)).totalDegree, fun x => ?_⟩
  rw [← b.sum_repr x, map_sum]
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [map_smul]
  exact (totalDegree_smul_le _ _).trans
    (Finset.le_sup (f := fun j => (Φ (b j)).totalDegree) (Finset.mem_univ j))

theorem colHighest_intertwiner_proportional :
    ∀ (ι : Type) [Fintype ι] (m n : ℕ), n ≤ m → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X), IrrFam π →
      ∀ (Φ Ψ : X →ₗ[ℂ] Pol ι m n) (μ μ' : ι → Fin n → ℤ), Φ ≠ 0 →
      (∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x) ∧ Ψ (π τ u x) = rowSub n τ u (Ψ x)) →
      (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0 ∧ colLie m τ k l ∘ₗ Ψ = 0) →
      (∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ ∧ colLie m τ k k ∘ₗ Ψ = (μ' τ k : ℂ) • Ψ) →
      ∃ r : ℂ, Ψ = r • Φ := by
  classical
  intro ι _ m n hnm X _ _ _ π hπ Φ Ψ μ μ' hΦ heq hup hwt
  have hker : LinearMap.ker Φ = ⊥ := by
    refine (hπ _ fun τ u x hx => ?_).resolve_right fun h => hΦ (LinearMap.ker_eq_top.1 h)
    rw [LinearMap.mem_ker] at hx ⊢
    rw [(heq τ u x).1, hx, map_zero]
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  obtain ⟨d₁, hd₁⟩ := exists_totalDegree_le_of_finiteDimensional Φ
  obtain ⟨d₂, hd₂⟩ := exists_totalDegree_le_of_finiteDimensional Ψ
  have hA : ∀ τ k l x, ∃ y, Φ y = rowLie n τ k l (Φ x) ∧ Ψ y = rowLie n τ k l (Ψ x) := by
    intro τ k l x
    obtain ⟨s, c, hc⟩ := GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie ι m n (max d₁ d₂) τ k l
    refine ⟨∑ u ∈ s, c u • π τ u x, ?_, ?_⟩
    · rw [← hc _ ((hd₁ x).trans (le_max_left _ _)), map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).1]
    · rw [← hc _ ((hd₂ x).trans (le_max_right _ _)), map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_smul, (heq τ u x).2]
  obtain ⟨_, ⟨x, rfl⟩, hx0, hhi, κ, hκ⟩ := GlobalTheory.exists_highest_vector
    (fun τ k l => (rowLie n τ k l : Module.End ℂ (Pol ι m n)))
    (fun t t' i k l => by convert rowLie_diag_comm (n := n) t t' i k l)
    iSup_iInf_eigenspace_rowLie (LinearMap.range Φ)
    (by
      rintro τ k l _ ⟨x, rfl⟩
      obtain ⟨y, hy, -⟩ := hA τ k l x
      exact ⟨y, hy⟩)
    (fun h => hΦ (LinearMap.range_eq_bot.1 h))
  obtain ⟨r, hr⟩ := GlobalTheory.DefLift.joint_highest_proportional ι m n hnm (Φ x) (Ψ x) κ μ μ' hx0
    (fun τ k l hkl => ⟨hhi τ k l hkl, by
      obtain ⟨y, hy, hy'⟩ := hA τ k l x
      have : y = 0 := hinj (by rw [hy, map_zero]; exact hhi τ k l hkl)
      rw [← hy', this, map_zero]⟩)
    (fun τ k => ⟨hκ τ k, by
      obtain ⟨y, hy, hy'⟩ := hA τ k k x
      have : y = (κ τ k : ℂ) • x := hinj (by rw [hy, map_smul]; exact hκ τ k)
      rw [← hy', this, map_smul]⟩)
    (fun τ k l hkl => ⟨LinearMap.congr_fun (hup τ k l hkl).1 x,
      LinearMap.congr_fun (hup τ k l hkl).2 x⟩)
    (fun τ k => ⟨LinearMap.congr_fun (hwt τ k).1 x, LinearMap.congr_fun (hwt τ k).2 x⟩)
  refine ⟨r, sub_eq_zero.1 (LinearMap.ker_eq_top.1 ((hπ _ fun τ u y hy => ?_).resolve_left
    fun h => hx0 ?_))⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hy ⊢
    rw [(heq τ u y).1, (heq τ u y).2, hy, map_smul]
  · have : x ∈ LinearMap.ker (Ψ - r • Φ) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, hr, sub_self]
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]

end GlobalTheory.DefLift

end
