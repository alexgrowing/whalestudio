import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis
  GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasis

theorem exists_eigen_casOp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ →
    (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) →
    (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) →
    ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  intro n ε H _ _ _ σ d e X Y h hX hY hK
  have hσ := h.1
  obtain ⟨v₀, hv₀K, hv₀⟩ := h.2.2.2.2
  let f : KG ε → ℂ := fun k => star ⟪v₀, σ (toMK k) v₀⟫_ℂ
  have hfc : Continuous f := (continuous_const.inner (KCoef.continuous_orbit hσ v₀)).star
  obtain ⟨Q, hQ⟩ := KCoef.exists_clm_kAvg hσ hfc
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h f (KCoef.kFinFun_coef hσ hv₀K)
  let Ss : Submodule ℂ H := smooth (Jm ε) σ
  let V : Submodule ℂ H := Ss.map (Q : H →ₗ[ℂ] H)
  have hVspan : V ≤ Submodule.span ℂ (Set.range a) := by
    rintro _ ⟨w, -, rfl⟩
    change Q w ∈ _
    rw [hQ, hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hVsm : ∀ u ∈ V, Sm ε σ u := by
    intro u hu
    have hspan : Submodule.span ℂ (Set.range a) ≤ Ss :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h.2.2.1 _ (haK j))
    exact hspan (hVspan hu)
  haveI : FiniteDimensional ℂ V :=
    by
      haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
      exact Submodule.finiteDimensional_of_le hVspan

  have hcomm : ∀ v, Sm ε σ v → casOp σ X Y (Q v) = Q (casOp σ X Y v) := by
    intro v hv
    have hQv : Sm ε σ (Q v) := hVsm _ ⟨v, hv, rfl⟩
    refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
    have hy' : Sm ε σ y := hy
    rw [inner_casOp hσ hX hY hy' hQv, hQ, hQ, KCoef.inner_kAvg hσ hfc, KCoef.inner_kAvg hσ hfc]
    congr 1
    funext k
    congr 1
    rw [← inner_casOp hσ hX hY hy' (Sm.translate hσ hv (KCoef.toMK_mem_UJ k)), hK _ (toMK_mem_K k) v hv]
  have hVmap : ∀ u ∈ V, casOp σ X Y u ∈ V := by
    rintro _ ⟨v, hv, rfl⟩
    change casOp σ X Y (Q v) ∈ V
    rw [hcomm v hv]
    exact ⟨_, sm_casOp hσ hX hY hv, rfl⟩
  let F : Module.End ℂ V :=
    { toFun := fun u => ⟨casOp σ X Y u, hVmap u u.2⟩
      map_add' := fun x y => Subtype.ext (casOp_add hσ hX hY (hVsm _ x.2) (hVsm _ y.2))
      map_smul' := fun r x => Subtype.ext (casOp_smul hσ hX hY r (hVsm _ x.2)) }
  have hQv₀ : Q v₀ ≠ 0 := by
    intro h0
    apply KCoef.inner_kAvg_ne_zero hσ hv₀
    rw [← hQ, h0, inner_zero_right]
  haveI : Nontrivial V := ⟨⟨⟨Q v₀, v₀, h.2.2.1 _ hv₀K, rfl⟩, 0, fun h0 => hQv₀ (congrArg Subtype.val h0)⟩⟩
  obtain ⟨χ, hχ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨u, hu⟩ := hχ.exists_hasEigenvector
  refine ⟨u, χ, hVsm _ u.2, fun h0 => hu.2 (Subtype.ext h0), ?_⟩
  exact congrArg Subtype.val (hu.apply_eq_smul)

end GlobalTheory.TypeSum.CasBasis

end
