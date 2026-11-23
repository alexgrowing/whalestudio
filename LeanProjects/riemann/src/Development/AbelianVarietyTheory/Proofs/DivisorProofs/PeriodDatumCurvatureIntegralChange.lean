import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodVectorMoebiusTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureReframedMetricEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSymplecticPreimageEqStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.TorsionForm.HeatConj

theorem frameMap_comp_inv (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) :
    frameMap n D ∘L frameMapInv n D = ContinuousLinearMap.id ℂ _ := by
  rw [frameMap, frameMapInv, GlobalTheory.T.extMap_comp_extMap, fibMat_mul, ← conjTranspose_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det D).1 hD), conjTranspose_one, fibMat_one,
    GlobalTheory.T.extMap_one']

theorem frameMapInv_comp (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) :
    frameMapInv n D ∘L frameMap n D = ContinuousLinearMap.id ℂ _ := by
  rw [frameMap, frameMapInv, GlobalTheory.T.extMap_comp_extMap, fibMat_mul, ← conjTranspose_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det D).1 hD), conjTranspose_one, fibMat_one,
    GlobalTheory.T.extMap_one']

theorem frameMap_inv_apply (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D)
    (w : Ext (n + n + g)) : frameMap n D (frameMapInv n D w) = w := by
  simpa using congrArg (fun L => L w) (frameMap_comp_inv n D hD)

theorem frameMapInv_apply (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D)
    (w : Ext (n + n + g)) : frameMapInv n D (frameMap n D w) = w := by
  simpa using congrArg (fun L => L w) (frameMapInv_comp n D hD)

def frameEquiv (n : ℕ) {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) :
    Ext (n + n + g) ≃L[ℂ] Ext (n + n + g) :=
  ContinuousLinearEquiv.equivOfInverse (frameMap n D) (frameMapInv n D)
    (frameMapInv_apply n D hD) (frameMap_inv_apply n D hD)

theorem contDiff_vecMul {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    ContDiff ℝ ∞ (fun y : Fin g → ℂ => y ᵥ* A) := by
  unfold Matrix.vecMul dotProduct
  fun_prop

theorem vecMul_inv_vecMul {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) (y : Fin g → ℂ) :
    y ᵥ* D⁻¹ ᵥ* D = y := by
  rw [vecMul_vecMul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det D).1 hD), vecMul_one]

theorem vecMul_vecMul_inv {g : ℕ} (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) (y : Fin g → ℂ) :
    y ᵥ* D ᵥ* D⁻¹ = y := by
  rw [vecMul_vecMul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det D).1 hD), vecMul_one]

end GlobalTheory.TorsionForm.HeatConj

namespace GlobalTheory.TorsionForm.HeatConj

theorem isHeatKernel_kerConj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (γ : Sp g)
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (u : ℝ) (D : Set (Fl g))
    (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (hτ : IsPeriodMap B τ) (hd : IsDatum B (fun b => moeb γ (τ b)) (latAct M γ) j h) (hb : b ∈ B)
    (hK : IsHeatKernel (fun b => moeb γ (τ b)) (latAct M γ) j h β b u D K) :
    IsHeatKernel τ M (fun l P => j (l ᵥ* (γ⁻¹).mat) (reframe τ γ P)) (fun P => h (reframe τ γ P)) β b u
      ((fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D) (kerConj n (den γ (τ b)) K) := by
  have hD : IsUnit (den γ (τ b)) := GlobalTheory.T.period_map_moebius_denom_unit B τ γ hd.1 b hb
  have hper : ∀ x, per (τ b) x ᵥ* (den γ (τ b))⁻¹ = per (moeb γ (τ b)) (x ᵥ* (γ⁻¹).mat) :=
    fun x => GlobalTheory.T.period_vector_moebius_transform γ (τ b) x hD
  have hmem : ∀ l ∈ M, l ᵥ* (γ⁻¹).mat ∈ latAct M γ := fun l hl => Submodule.mem_map.2 ⟨l, hl, rfl⟩
  have hsec : ∀ (t : ℝ), 0 < t → ∀ z' w,
      ContDiff ℝ ∞ (fun y => K t y z' w) := by
    intro t ht z' w
    have h1 : ContDiff ℝ ∞ (fun y : Fin g → ℂ => K t y z') := by
      rw [← contDiffOn_univ]
      refine hK.1.comp (f := fun y : Fin g → ℂ => (t, y, z'))
        (show ContDiff ℝ ∞ (fun y : Fin g → ℂ => (t, y, z')) by fun_prop).contDiffOn ?_
      intro y _
      exact ⟨ht, trivial⟩
    exact ((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) w).restrictScalars ℝ).contDiff.comp h1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    set T : (Ext (n + n + g) →L[ℂ] Ext (n + n + g)) →L[ℝ] (Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :=
      ((ContinuousLinearMap.compL ℂ _ _ _ (frameMap n (den γ (τ b)))).comp
        ((ContinuousLinearMap.compL ℂ _ _ _).flip (frameMapInv n (den γ (τ b))))).restrictScalars ℝ
    have hmap : ContDiff ℝ ∞ (fun a : ℝ × (Fin g → ℂ) × (Fin g → ℂ) =>
        (a.1, a.2.1 ᵥ* (den γ (τ b))⁻¹, a.2.2 ᵥ* (den γ (τ b))⁻¹)) :=
      contDiff_fst.prodMk ((contDiff_vecMul _).comp (contDiff_fst.comp contDiff_snd) |>.prodMk
        ((contDiff_vecMul _).comp (contDiff_snd.comp contDiff_snd)))
    have h2 := hK.1.comp (s := Ioi (0:ℝ) ×ˢ univ) hmap.contDiffOn (fun a ha => ⟨ha.1, trivial⟩)
    exact T.contDiff.comp_contDiffOn h2
  ·
    intro t ht l hl z z'
    obtain ⟨k1, k2⟩ := hK.2.1 t ht _ (hmem l hl) (z ᵥ* (den γ (τ b))⁻¹) (z' ᵥ* (den γ (τ b))⁻¹)
    constructor
    · simp only [kerConj, reframe, add_vecMul, hper]
      rw [k1, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    · simp only [kerConj, reframe, add_vecMul, hper]
      rw [← k2]
      exact ContinuousLinearMap.ext fun w => by simp
  ·
    intro t ht z z' w
    have hdt := hK.2.2.1 t ht (z ᵥ* (den γ (τ b))⁻¹) (z' ᵥ* (den γ (τ b))⁻¹)
      (frameMapInv n (den γ (τ b)) w)
    have hc := GlobalTheory.T.curvature_reframed_metric_eq B τ γ h β b u _ hτ hd.1 hd.2.2.2.1 hd.2.2.2.2.1 hb
      (hsec t ht (z' ᵥ* (den γ (τ b))⁻¹) (frameMapInv n (den γ (τ b)) w)) z
    have e : (fun y => kerConj n (den γ (τ b)) K t y z' w) = fun y =>
        frameMap n (den γ (τ b)) (K t (y ᵥ* (den γ (τ b))⁻¹) (z' ᵥ* (den γ (τ b))⁻¹)
          (frameMapInv n (den γ (τ b)) w)) := rfl
    rw [e, hc]
    have := ((frameMap n (den γ (τ b))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hdt
    have e3 : (fun t' => kerConj n (den γ (τ b)) K t' z z' w) =
        (⇑((frameMap n (den γ (τ b))).restrictScalars ℝ)) ∘ (fun t' => K t' (z ᵥ* (den γ (τ b))⁻¹)
          (z' ᵥ* (den γ (τ b))⁻¹) (frameMapInv n (den γ (τ b)) w)) := rfl
    rw [e3]
    exact this.congr_deriv (map_neg _ _)
  ·
    intro f₂ hf₂
    set Φ := frameMap n (den γ (τ b)) with hΦ
    set Ψ := frameMapInv n (den γ (τ b)) with hΨ
    set f₁ : (Fin g → ℂ) → Ext (n + n + g) := fun y => Ψ (f₂ (y ᵥ* den γ (τ b))) with hf₁def
    have hf₁ : IsSec (fun b => moeb γ (τ b)) (latAct M γ) j b f₁ := by
      refine ⟨(Ψ.restrictScalars ℝ).contDiff.comp (hf₂.1.comp (contDiff_vecMul _)), ?_⟩
      intro l' hl' y
      obtain ⟨l, hl, hll⟩ := Submodule.mem_map.1 hl'
      have hl'' : l' = l ᵥ* (γ⁻¹).mat := hll.symm
      subst hl''
      have e : (y + per (moeb γ (τ b)) (l ᵥ* (γ⁻¹).mat)) ᵥ* den γ (τ b) =
          y ᵥ* den γ (τ b) + per (τ b) l := by
        rw [← hper, add_vecMul, vecMul_inv_vecMul _ hD]
      simp only [hf₁def, e]
      rw [hf₂.2 l hl, map_smul]
      simp [reframe, vecMul_vecMul_inv _ hD]
    have htend := hK.2.2.2 f₁ hf₁
    have hfun : (fun t z => ∫ x in (fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D,
        kerConj n (den γ (τ b)) K t z (per (τ b) x) (f₂ (per (τ b) x))) =
        fun t z => Φ (∫ x in D, K t (z ᵥ* (den γ (τ b))⁻¹) (per (moeb γ (τ b)) x)
          (f₁ (per (moeb γ (τ b)) x))) := by
      funext t z
      have hint : ∀ x, kerConj n (den γ (τ b)) K t z (per (τ b) x) (f₂ (per (τ b) x)) =
          frameEquiv n (den γ (τ b)) hD ((fun y => K t (z ᵥ* (den γ (τ b))⁻¹) (per (moeb γ (τ b)) y)
            (f₁ (per (moeb γ (τ b)) y))) (x ᵥ* (γ⁻¹).mat)) := by
        intro x
        have e2 : f₂ (per (τ b) x) = f₂ (per (moeb γ (τ b)) (x ᵥ* (γ⁻¹).mat) ᵥ* den γ (τ b)) := by
          rw [← hper, vecMul_inv_vecMul _ hD]
        simp only [kerConj, ContinuousLinearMap.comp_apply, hper, e2, hf₁def]
        rfl
      simp only [hint]
      have hch := GlobalTheory.T.integral_symplectic_preimage_eq (F := Ext (n + n + g)) γ D (fun y => K t (z ᵥ* (den γ (τ b))⁻¹)
        (per (moeb γ (τ b)) y) (f₁ (per (moeb γ (τ b)) y)))
      rw [ContinuousLinearEquiv.integral_comp_comm, hch]
      rfl
    rw [hfun]
    have h2 := htend.comp (fun z : Fin g → ℂ => z ᵥ* (den γ (τ b))⁻¹)
      (contDiff_vecMul _).continuous
    have h3 := Φ.uniformContinuous.comp_tendstoLocallyUniformly h2
    have e5 : Φ ∘ (f₁ ∘ fun z : Fin g → ℂ => z ᵥ* (den γ (τ b))⁻¹) = f₂ := by
      funext z
      simp [hf₁def, Function.comp, vecMul_inv_vecMul _ hD, hΦ, hΨ, frameMap_inv_apply n _ hD]
    rw [← e5]
    exact h3

end GlobalTheory.TorsionForm.HeatConj
