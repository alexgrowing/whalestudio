import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LmuNumNonneg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConjugateEigenSubDegreeEqStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDualStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeSumEigenSubDegreesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExistsStatement

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg

theorem dot_bijective (K : Type) [Field K] (d : ℕ) :
    Function.Bijective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
  have hi : Function.Injective
      (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext r
    have := LinearMap.congr_fun hx (Pi.single r 1)
    simpa [dotProductBilin_apply_apply] using this
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    simp [Subspace.dual_finrank_eq])).1 hi

noncomputable def endAct {K : Type} [Field K] {O : Type} [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Module.End K (Fin d → K) where
  toFun a := Matrix.toLin' (ρ a)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' a b := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  map_zero' := by simp
  map_add' a b := by simp

theorem isHom_lie {K : Type} [Field K] {C : ACurve K} {p : ℕ} {O : Type} [CommRing O] [StarRing O]
    {d : ℕ} (D : ConjData C p O d) (a : O) : IsHom C D.lie D.lie (endAct D.ρ a) := by
  intro i x hx
  obtain ⟨y, hy, rfl⟩ := (D.hodge.2.2.2.2 i x).1 hx
  have h2 : (D.ρH a y).1 ∈ D.lie i :=
    (D.hodge.2.2.2.2 i _).2 ⟨_, D.ρH_hom a i y hy, rfl⟩
  rw [D.ρH_fst] at h2
  simpa [endAct] using h2

theorem lmuNum_nonneg_of_conjData : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  intro K _ C p _ _ O k S T _ _ _ _ _ _ χ d D ι κ j q μ W L hp hs hc hbij hconj hj hq hW0 hL0 hWj hLq hgap
  classical
  obtain ⟨hbot, W₀, hW₀⟩ := GlobalTheory.T.sub_degree_bot_and_max_exists K C (Fin d → K) D.lie D.lie_bun
  obtain ⟨he0, hC2⟩ := GlobalTheory.T.lie_sub_degree_bound_by_dual K C p O d D hp
  have hsplit : deg C D.lie = ∑ s, subDeg C D.lie
      (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ s a))) :=
    GlobalTheory.T.degree_sum_eigen_sub_degrees K C (Fin d → K) D.lie O k S χ hs hc (endAct D.ρ) D.lie_bun (isHom_lie D)
  have hdual : deg C (dotDual C D.lie) = - deg C D.lie :=
    (GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C (Fin d → K) (Fin d → K) D.lie (dotProductBilin K K)
      D.lie_bun (dot_bijective K d)).2.1
  have hC1 : ∀ τ, subDeg C D.lie (W τ j) = subDeg C D.lie (L τ q) := by
    intro τ
    rw [hWj, hLq]
    exact GlobalTheory.T.conjugate_eigen_sub_degree_eq K C p O k S χ d D hs hc (ι τ) (κ τ) (hconj τ)
  have hsum : deg C D.lie = 2 * ∑ τ, subDeg C D.lie (W τ j) := by
    rw [hsplit, ← (Equiv.ofBijective _ hbij).sum_comp, Fintype.sum_sum_type, two_mul]
    simp only [Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by rw [hWj]
    · exact Finset.sum_congr rfl fun τ _ => by rw [hC1, hLq]
  refine GlobalTheory.CompanionTheory.Ar.Crv.Chain.lmuNum_nonneg T p j q μ _ _ (subDeg C D.lie W₀ : ℝ)
    (deg C (dotDual C D.lie) : ℝ) hp hj hq hgap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro τ; simp [hW0, hbot]
  · intro τ; simp [hL0, hbot]
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ i _; exact_mod_cast hW₀ _
  · intro τ; exact_mod_cast hC1 τ
  · rw [hdual, hsum]; push_cast; ring
  · exact_mod_cast hC2 W₀
  · exact_mod_cast he0

end GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg
