import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepOffSnd

theorem vac_off {D : D7} {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (hc : c.Is) (hv : v.Is) (hw : VForm v w)
    (i : ℕ) (hi : i + 1 < D.R.m) (Ψ : WO (c.V i) (c.V (i + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) (comb c.ψ _ _ (v.eG i) (comb c.ψ _ _ (w.eQ i) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) Ψ := by
    have key := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N i) (v.N (i + 1)) Ψ (hv.sd i (by omega)) (hv.sd (i + 1) hi)
    have e : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ => True := by
      funext p; exact eq_true (Classical.em _)
    rw [e] at key
    exact (key.1 hΨ).1
  have h1 := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ w.Q) (offP v w)
      (fun p hp hn => hn.2 hp)).2.1 (w.eQ i) (hw.atQ i).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ v.gP) (offP v w)
      (fun p hp hn => hn.1 hp)).2.1 (v.eG i) (hv.atG i).1).2 _ _ _ h1

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * κ) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hw _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a ha f hf κ hκ q₁ q₂
  have hΦ₁ := vac_off v w hc hv hw j (by omega) Ψ₁ hΨ₁
  have hΦ₂ := vac_off v w hc hv hw (j + 1) (by omega) Ψ₂ hΨ₂
  have hfix := (hoff j σ h _ _ hΦ₁ hΦ₂).2.1 κ hκ
  have hom : t.om (j + 1) (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have e : ((q₁, q₂ * κ) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (1, κ) := by simp
    rw [e, map_mul, Module.End.mul_apply, hfix]
  have hrow : rTrans κ f = f := by
    rw [hf]; exact (hw.row (j + 1 + 1) (by omega) G x a ha).2 κ hκ
  have hr : rTrans (q₂ * κ) f = rTrans q₂ f := by
    conv_rhs => rw [← hrow]
    funext g; simp only [rTrans, mul_assoc]
  have hs := (ht.sFB j σ h).1
  have hom' : (t.sFB j σ h).om (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      (t.sFB j σ h).om (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    rw [hs]; exact hom
  unfold integ Chain.hand
  rw [hr]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun Z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h)
      ((t.sBF j (σ + 1) h).om (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))))) (flatFB (t.sFB j σ h) Z))
      (rTrans q₂ f)) hom'

end GlobalTheory.DStepOffSnd

end
