import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.Pullback

theorem hasFDerivAt_apply_of_vanish {X V F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : X → V → F) (hlin : ∀ x, IsLinearMap ℝ (L x)) (x₀ : X)
    (hL : ∀ v, DifferentiableAt ℝ (fun x => L x v) x₀)
    (u : X → V) (u' : X →L[ℝ] V) (hu : HasFDerivAt u u' x₀) (hu0 : u x₀ = 0) :
    ∃ D : X →L[ℝ] F, HasFDerivAt (fun x => L x (u x)) D x₀ ∧ ∀ w, D w = L x₀ (u' w) := by
  let b := Module.finBasis ℝ V
  have hexp : ∀ x (v : V), L x v = ∑ k, b.repr v k • L x (b k) := by
    intro x v
    let Lx : V →ₗ[ℝ] F := IsLinearMap.mk' (L x) (hlin x)
    calc L x v = Lx (∑ k, b.repr v k • b k) := by rw [b.sum_repr]; rfl
      _ = ∑ k, b.repr v k • Lx (b k) := by rw [map_sum]; simp only [map_smul]
      _ = _ := rfl
  let c : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun k => LinearMap.toContinuousLinearMap (b.coord k)
  have hc : ∀ k (v : V), c k v = b.repr v k := fun k v => by simp [c]
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ V))),
      HasFDerivAt (fun x => c k (u x) • L x (b k))
        (c k (u x₀) • (fderiv ℝ (fun x => L x (b k)) x₀) + ((c k).comp u').smulRight (L x₀ (b k))) x₀ :=
    fun k _ => ((c k).hasFDerivAt.comp x₀ hu).smul (hL (b k)).hasFDerivAt
  refine ⟨_, (HasFDerivAt.sum hterm).congr_of_eventuallyEq ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x => by
      simp only [Finset.sum_apply, hc]; exact hexp x (u x)
  · intro w
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, hu0, map_zero, hc, Finsupp.coe_zero, Pi.zero_apply,
      zero_smul, zero_add]
    exact (hexp x₀ (u' w)).symm

theorem corr_deriv_base_change : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {g m n : ℕ} (N : Fin n → Pt E g → E → Ext m) (φ : E' → E) (β : Fin n → E') (b : E') (z : Fin g → ℂ), (∀ i Q, IsLinearMap ℝ (N i Q)) → (∀ i v, DifferentiableAt ℝ (fun Q => N i Q v) (φ b, z)) → (∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c) → DifferentiableAt ℝ (fun P : Pt E' g => ∑ i, N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))) (b, z) ∧ ∀ w : Pt E' g, fderiv ℝ (fun P : Pt E' g => ∑ i, N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))) (b, z) w = ∑ i, N i (φ b, z) (fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b w.1) := by
  intro E E' _ _ _ _ _ _ g m n N φ β b z h1 h2 h3
  have hφb : DifferentiableAt ℂ φ b := h3.self_of_nhds
  have han : AnalyticAt ℂ φ b := GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.mpr h3
  have hD : DifferentiableAt ℂ (fderiv ℂ φ) b := han.fderiv.differentiableAt
  have hpair : DifferentiableAt ℝ (fun P : Pt E' g => (φ P.1, P.2)) (b, z) :=
    ((hφb.restrictScalars ℝ).comp (b, z) differentiableAt_fst).prodMk differentiableAt_snd
  have key : ∀ i, ∃ D : Pt E' g →L[ℝ] Ext m,
      HasFDerivAt (fun P : Pt E' g => N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))) D (b, z) ∧
      ∀ w : Pt E' g, D w = N i (φ b, z) (fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b w.1) := by
    intro i
    have hψ : DifferentiableAt ℂ (fun c => fderiv ℂ φ c (β i)) b :=
      hD.clm_apply (differentiableAt_const _)
    have hu : HasFDerivAt (fun P : Pt E' g => fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))
        (((fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b).restrictScalars ℝ).comp
          (ContinuousLinearMap.fst ℝ E' (Fin g → ℂ))) (b, z) :=
      by
        have h0 : HasFDerivAt (fun c : E' => fderiv ℂ φ c (β i))
            ((fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b).restrictScalars ℝ) b :=
          hψ.hasFDerivAt.restrictScalars ℝ
        have h00 : HasFDerivAt (fun P : Pt E' g => fderiv ℂ φ P.1 (β i))
            (((fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b).restrictScalars ℝ).comp
              (ContinuousLinearMap.fst ℝ E' (Fin g → ℂ))) (b, z) :=
          by
            have h' := h0.comp (b, z) (hasFDerivAt_fst (𝕜 := ℝ) (p := ((b, z) : E' × (Fin g → ℂ))))
            exact h'
        exact h00.sub_const _
    exact hasFDerivAt_apply_of_vanish (fun P : Pt E' g => N i (φ P.1, P.2)) (fun P => h1 i _) (b, z)
      (fun v => by have h' := (h2 i v).comp (b, z) hpair; exact h') _ _ hu (sub_self _)
  choose D hD1 hD2 using key
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hD1 i)
  have hsum' : HasFDerivAt (fun P : Pt E' g => ∑ i, N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i)))
      (∑ i, D i) (b, z) := by
    rw [Finset.sum_fn] at hsum
    exact hsum
  refine ⟨hsum'.differentiableAt, fun w => ?_⟩
  rw [hsum'.fderiv, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hD2 i w

end GlobalTheory.TorsionForm.Pullback
