import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev
variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : Pl D → Prop)
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (↑LS) (↑LT) P ≤ latO S T (↑LS) (↑LT) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, hr⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, hr⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hle hu), fun e he u hu => hf.2.2 e he u (hle hu)⟩

theorem hand_mul_right {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (k : GA D J.W) (a : ℂ) (ha : a ≠ 0)
    (h₁ : s₁.om (1, k) Φ₁ = a⁻¹ • Φ₁) (h₂ : s₂.om (k, 1) Φ₂ = a • Φ₂) (g : GA D B.V) (q₁ : GA D J.W) (q₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (q₁ * k) q₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂ := by
  have e₁ : s₁.om (g, q₁ * k) Φ₁ = a⁻¹ • s₁.om (g, q₁) Φ₁ := by
    rw [show ((g, q₁ * k) : GA D B.V × GA D J.W) = (g, q₁) * (1, k) from by simp, map_mul, Module.End.mul_apply, h₁,
      LinearMap.map_smul]
  have e₂ : s₂.om (q₁ * k, q₂) Φ₂ = a • s₂.om (q₁, q₂) Φ₂ := by
    rw [show ((q₁ * k, q₂) : GA D J.W × GA D B'.V) = (q₁, q₂) * (k, 1) from by simp, map_mul, Module.End.mul_apply, h₂,
      LinearMap.map_smul]
  unfold Chain.hand
  rw [e₁, e₂, (GlobalTheory.HandHom.hand_hom D ψ σ B J B' s₁ s₂ l vL φ).1, inv_mul_cancel₀ ha, one_smul]

theorem integ_lev : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * k) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a _ f _ k hk q₁ q₂
  obtain ⟨b, hb, l₁, l₂, -⟩ := hF.lawG j (by omega) k hk
  have hd : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.1 hF.disjG hp
  have v₁ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ j) (hF.atQ j).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₁)
  have v₂ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ (j + 1)) (hF.atQ (j + 1)).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₂)
  have m₁ := l₁ _ v₁
  have m₂ := l₂ (by omega) _ v₂
  rw [← (ht.sBF j (σ + 1) h).1] at m₁
  rw [← (ht.sFB j σ h).1] at m₂
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun y => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ y (rTrans q₂ f))
    (hand_mul_right (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) k b hb m₁ m₂ g q₁ q₂)

end GlobalTheory.DStepLev
