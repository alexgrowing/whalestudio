import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjModelExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLineKFin

private theorem eq_of_inner_eq_on_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {v w : H}
    (h : ∀ y : E, ⟪v, (y : H)⟫_ℂ = ⟪w, (y : H)⟫_ℂ) : v = w := by
  have hclosed : IsClosed {x : H | ⟪v - w, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (E : Set H) ⊆ {x : H | ⟪v - w, x⟫_ℂ = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, inner_sub_left, h ⟨x, hx⟩, sub_self]
  have hall := closure_minimal hsub hclosed
  rw [hE.closure_eq] at hall
  have hz : ⟪v - w, v - w⟫_ℂ = 0 := hall (Set.mem_univ _)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_riesz {H P : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup P] [Module ℂ P] {E : Submodule ℂ H} (hE : Dense (E : Set H)) (F : P →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hF : ∀ φ, ∃ c : ℝ, ∀ y : E, ‖F φ y‖ ≤ c * ‖(y : H)‖) :
    ∃ b : P →ₛₗ[starRingEnd ℂ] H, ∀ φ (y : E), F φ y = ⟪b φ, (y : H)⟫_ℂ := by
  have hrep : ∀ φ, ∃ v : H, ∀ y : E, F φ y = ⟪v, (y : H)⟫_ℂ := by
    intro φ
    obtain ⟨c, hc⟩ := hF φ
    have hden : DenseRange (E.subtype : E →ₗ[ℂ] H) := by
      simpa using hE.denseRange_val
    let g : H →L[ℂ] ℂ := (F φ).extendOfNorm E.subtype
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    have := LinearMap.extendOfNorm_eq (f := F φ) hden ⟨c, fun y => by simpa using hc y⟩ y
    simpa [g] using this.symm
  choose v hv using hrep
  refine ⟨{ toFun := v, map_add' := ?_, map_smul' := ?_ }, hv⟩
  · intro φ ψ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_add_left, ← hv, ← hv, map_add, LinearMap.add_apply]
  · intro c φ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_smul_left, ← hv, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp

theorem finite_map {H P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup P] [Module ℂ P]
    (b : P →ₛₗ[starRingEnd ℂ] H) (T : Submodule ℂ P) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.map b) := by
  have hT : (T : Submodule ℂ P).FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.iff_fg.mpr (hT.map b)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_stable (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset (M.ε τ)) {y : M.H τ} (hy : y ∈ M.sm τ) : M.σ τ g y ∈ M.sm τ := Submodule.subset_span (GlobalTheory.ConjExt.smooth_translate M τ ⟨y, hy⟩ hg)

theorem dense_sm (M : DSModel V S) (τ : D.what₂.Tau) : Dense (M.sm τ : Set (M.H τ)) := GlobalTheory.LowTypeDetermined.dense_of_irred (M.ds τ).2.2.2.1 (fun _ hg _ hy => sm_stable M τ hg hy) (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)

theorem kset_star {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.mp hu), ?_⟩
  have hJ : star (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
    rw [Matrix.star_eq_conjTranspose]; exact Formalism.REAL.Jm_conjTranspose ε
  calc star k * Formalism.REAL.Jm ε = star (Formalism.REAL.Jm ε * k) := by rw [star_mul, hJ]
    _ = star (k * Formalism.REAL.Jm ε) := by rw [hc]
    _ = Formalism.REAL.Jm ε * star k := by rw [star_mul, hJ]

private theorem mem_UJset_of_mem_Kset_twisted_operators {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hkk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  simp only [Formalism.MainNotions.S.UJset, Set.mem_ofPred_eq, Formalism.REAL.inUJ]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hkk, Matrix.one_mul]

private theorem subst_subst_eq_of_subst_eq_X {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (y : H) : σ k (σ (star k) y) = y := by
  have hks1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 k (mem_UJset_of_mem_Kset_twisted_operators hk) (star k) (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)),
    hks1, hσ.1.1]
  rfl

private theorem inner_urep_apply_eq_inner_star_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k (mem_UJset_of_mem_Kset_twisted_operators hk)⟩
  conv_lhs => rw [← subst_subst_eq_of_subst_eq_X hσ hk y]
  exact L.inner_map_map x (σ (star k) y)

theorem kfin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  intro D V W S S' M M' τ aS aT A hA
  have : CompleteSpace (M'.H τ) := (M'.ds τ).1
  refine ⟨fun φ y => ?_, fun φ u => ?_⟩
  · refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (A.flip y), ?_, ⟨φ, ?_, rfl⟩, ?_⟩
    · exact Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map _)
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl
    · intro g hg v hv
      obtain ⟨ψ, hψ, rfl⟩ := hv
      obtain ⟨ψ', hdeg, heq⟩ := hA.eqK g hg ψ
      refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), ?_⟩
      simp only [LinearMap.flip_apply, heq y]
  · let F : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] ℂ := A.compr₂ (innerSL ℂ u).toLinearMap
    have hFapp : ∀ ψ y, F ψ y = ⟪u, A ψ y⟫_ℂ := fun ψ y => by simp [F]
    obtain ⟨b, hb⟩ := exists_riesz (dense_sm M' τ) F fun ψ => by
      obtain ⟨c, hc⟩ := hA.bdd ψ u
      exact ⟨c, fun y => by rw [hFapp]; exact hc y⟩
    have hσ := (M'.ds τ).2.2.1
    let T : Submodule ℂ (PolF D W.rank V.rank) := MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree
    refine ⟨b φ, ⟨T.map b, finite_map b T, ⟨φ, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩, ?_⟩,
      fun y => by rw [← hFapp, hb]⟩
    intro k hk v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    obtain ⟨ψ', hdeg, heq⟩ := hA.invK k hk ψ
    have key : M'.σ τ k (b ψ) = b ψ' := by
      refine eq_of_inner_eq_on_dense (dense_sm M' τ) fun y => ?_
      have hmem : M'.σ τ (star k) y ∈ M'.sm τ := sm_stable M' τ (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)) y.2
      rw [inner_urep_apply_eq_inner_star_of_mem_Kset hσ hk]
      have e1 : F ψ ⟨_, hmem⟩ = ⟪b ψ, M'.σ τ (star k) y⟫_ℂ := hb ψ ⟨_, hmem⟩
      rw [← e1, ← hb ψ' y, hFapp, hFapp, heq ⟨_, hmem⟩ y (subst_subst_eq_of_subst_eq_X hσ hk y).symm]
    rw [key]
    exact ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), rfl⟩

end GlobalTheory.Chain.RealLineKFin

end
