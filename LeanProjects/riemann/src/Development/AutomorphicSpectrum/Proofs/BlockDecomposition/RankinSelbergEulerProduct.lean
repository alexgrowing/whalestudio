import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RankinSelberg.Unfolded

open Ad3 Ad3.R

theorem localChar_inv' (c : HeckeCharacter ℚ) (v : Pl) :
    localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rfl

theorem glAt_prodEquiv (v : Pl) (g : G2) :
    glAt v (AdelicGLn.prodEquiv ℚ 2 g).2 = finAt v g := by
  apply Units.ext
  ext i j
  simp [GroundTheory.Automorphic.GodementSection.glAt_apply, AdelicGLn.prodEquiv_apply_snd]

theorem wh_mul_right {φ : G2 → ℂ} {r : G2} {u : ℂ} (h : ∀ g, φ (g * r) = u * φ g) (g : G2) :
    Wh φ (g * r) = u * Wh φ g := by
  unfold Wh
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, h, mul_assoc]

theorem q_torus {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hφ : Lift k N f ω φ) (hW : ∀ t : ℝˣ, Wh φ (realEmb (dg2 t 1)) = WR k t) (t : ℝˣ) (r : GL (Fin 2) ℝ)
    (hr : r.val * r.valᵀ = 1) (hd : r.det.val = 1) :
    (fun y => Wh φ (realEmb y) * conj (Wh φ (realEmb y))) (dg2 t 1 * r) = WR k t * conj (WR k t) := by
  obtain ⟨u, hu, hru⟩ := hφ.rot r hr hd
  have hu1 : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  show Wh φ (realEmb (dg2 t 1 * r)) * conj (Wh φ (realEmb (dg2 t 1 * r))) = _
  rw [map_mul, wh_mul_right hru, hW, map_mul]
  linear_combination (WR k t * conj (WR k t)) * hu1

theorem locConst_section (hL : Loc2) (hA : A10) {ψ : ∀ v : Pl, AddChar (Qv v) Circle} (v : Pl) (hψ : IsStd (ψ v))
    (m : Measure (integralGL (Qv v) 2)) [m.IsHaarMeasure] [IsProbabilityMeasure m]
    {μ₁ μ₂ c : (Qv v)ˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) (hc : IsUnit1 c)
    {φ₀ Ψ : (Fin 2 → Qv v) → ℂ} (hφ₀ : SB φ₀) (hΨ : SB Ψ) (x : Qv v) {s : ℂ} (hs : 0 < s.re) :
    IsLocallyConstant (fun g => GodementSectionLocal.localSection c c⁻¹ s Ψ g *
      Av (W2 (ψ v) μ₁ μ₂ φ₀) (fun g => W2 (ψ v) μ₁ μ₂ φ₀ (g * uni2 x)) c s g) := by
  have hW : W2 (ψ v) μ₁ μ₂ φ₀ ∈ V2 (ψ v) μ₁ μ₂ := Submodule.subset_span ⟨φ₀, hφ₀, rfl⟩
  have hW' := (hL (Qv v) (ψ v) hψ μ₁ μ₂ h₁ h₂).1.stable _ hW (uni2 x)
  have h := hA (Qv v) (ψ v) hψ m μ₁ μ₂ c h₁ h₂ hc _ hW _ hW'
  exact ((h.2 Ψ hΨ).1 s hs).mul ((h.1 s hs).2)

theorem e6 : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6 := by
  intro hL hB hA hE2 hE3 hE5 hE6a hF2 k N _ hk χ hχ f a hf ha ω φ hω hφ μ₁ μ₂ φ₀ hM mK _ _ m hm γ hγ
  obtain ⟨C, hC0, hC⟩ := hE5 k (by omega)
  refine ⟨C, hC0, ?_⟩
  intro S hS c δ hc hδ hun x h hx Ψ hΨ s hs
  have hcu : ∀ v, IsUnit1 (localChar c v) := fun v => (hB.1 v).2.2.2.2.2.2 c
  have hun' : ∀ v ∉ S, IsUnramifiedChar (localChar c⁻¹ v) := fun v hv => by
    rw [localChar_inv']
    exact isUnramifiedChar_inv_iff.2 (hun v hv)
  have hc1 := ((hE2 S s hs).1 c hun).1
  have hc2 := ((hE2 S s hs).1 c⁻¹ hun').1
  have hW := (hF2 k N hk χ hχ f a hf ha ω φ hω hφ).2.2.2
  have hs0 : 0 < s.re := by linarith
  set A : ∀ v : S, GL (Fin 2) (Qv v.1) → ℂ := fun v g =>
    GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) g *
      Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
        (localChar c v.1) s g with hAdef
  have hAlc : ∀ v, IsLocallyConstant (A v) := fun v => by
    have := (hm v.1).1
    have := (hm v.1).2
    exact locConst_section (ψ := fun v => localAdelicChar ℚ v) hL hA v.1 (hB.1 v.1).1 (m v.1)
      (hM.u₁ v.1) (hM.u₂ v.1) (hcu v.1) (hM.sb v.1) (hΨ v) (x v) hs0
  set T : ℂ := (∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s with hT
  have hpt : ∀ κ : KA, godementSection c c⁻¹ s (tst γ S Ψ) κ.1 *
      Ag (fun g => Wh φ g * conj (Wh φ (g * h))) c s κ.1 =
      (C * (if δ then -1 else 1) * GG k s * T) * ∏ v : S, A v (finAt v.1 κ.1) := by
    intro κ
    have e1 := GroundTheory.Automorphic.GodementSection.godementSection_tensor c c⁻¹ s γ (restrictedTensor2 S Ψ) κ.1
    have e2 := GroundTheory.Automorphic.GodementSection.finSection_restrictedTensor2 c c⁻¹ S hΨ hc1 hc2
      (s := s) (by linarith) (g := (AdelicGLn.prodEquiv ℚ 2 κ.1).2)
      (fun v _ => by rw [glAt_prodEquiv]; exact κ.2.2 v)
    have e3 := hE6a k N hk χ hχ f a hf ha ω φ hω hφ μ₁ μ₂ φ₀ hM S hS c hun x h hx s hs κ
    have e4 := hC γ hγ c δ hc hδ s hs κ (fun y => Wh φ (realEmb y) * conj (Wh φ (realEmb y)))
      (fun t r hr hd => q_torus hφ hW t r hr hd)
    simp only [inv_inv, localChar_inv', glAt_prodEquiv] at e2
    have e0 : godementSection c c⁻¹ s (tst γ S Ψ) κ.1 = _ := e1
    rw [e0, e2]
    simp only [hAdef, Finset.prod_mul_distrib]
    linear_combination (archSection c c⁻¹ s γ (AdelicGLn.prodEquiv ℚ 2 κ.1).1 *
      ∏ v : S, GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) (finAt v.1 κ.1)) * e3 +
      ((∏ v : S, GodementSectionLocal.localSection (localChar c v.1) (localChar c v.1)⁻¹ s (Ψ v) (finAt v.1 κ.1)) *
      (∏ v : S, Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v)))
        (localChar c v.1) s (finAt v.1 κ.1)) * T) * e4
  have hJ : Jg mK (fun g => Wh φ g * conj (Wh φ (g * h))) c (tst γ S Ψ) s =
      (C * (if δ then -1 else 1) * GG k s * T) * ∫ κ : KA, ∏ v : S, A v (finAt v.1 κ.1) ∂mK := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hJ, hE3 mK m hm S A hAlc]
  have hZ : ZS m μ₁ μ₂ φ₀ S x Ψ c s = ∏ v : S, ∫ κ, A v κ.1 ∂m v.1 := rfl
  rw [hZ]
  ring

end GlobalTheory.CompanionTheory.RankinSelberg.Unfolded

end
