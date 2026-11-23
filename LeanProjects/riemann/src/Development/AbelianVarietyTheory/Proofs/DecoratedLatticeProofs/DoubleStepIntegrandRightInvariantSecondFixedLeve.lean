import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev

theorem comm_inf_fin {D : D7} (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  have ha' : finHom V a = 1 := ha
  have hb' : infHom V b = 1 := hb
  have h := GlobalTheory.LevelCut.eq_one_of_parts V (a * b * (b * a)⁻¹)
    (show infHom V _ = 1 by simp [hb']) (show finHom V _ = 1 by simp [ha'])
  exact mul_inv_eq_one.mp h

theorem per_hand_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (g : GA D B.V) (q₁ : GA D J.W) (q₂ k : GA D B'.V)
    (s : ℂ) (hs : s ≠ 0) (hom : s₂.om (1, k) Φ₂ = s⁻¹ • Φ₂) (f f' : GA D B'.V → ℂ) (hf : f' = s • f) :
    B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ (q₂ * k)) f' = B'.per ψ (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂) f := by
  have e : ((q₁, q₂ * k) : GA D J.W × GA D B'.V) = (q₁, q₂) * (1, k) := by simp
  have hh := GlobalTheory.HandHom.handFB_smul s₂ vL 1 s⁻¹
  simp only [one_smul, star_one, one_mul] at hh
  unfold Chain.hand
  rw [hf, e, map_mul, Module.End.mul_apply, hom, LinearMap.map_smul, GlobalTheory.HandHom.flatFB_smul, hh, GlobalTheory.HandHom.per_smul,
    inv_mul_cancel₀ hs, one_mul]

theorem rTrans_eigen {G : Type} [Group G] (a b k q : G) (F : G → ℂ) (s : ℂ) (hcm : a * k = k * a)
    (h : rTrans k (rTrans b F) = s • rTrans b F) :
    rTrans (q * k) (rTrans (a * b) F) = s • rTrans q (rTrans (a * b) F) := by
  funext g
  have := congrFun h (g * q * a)
  simp only [rTrans, Pi.smul_apply] at this ⊢
  rw [show g * (q * k) * (a * b) = g * q * a * k * b by
    rw [mul_assoc (g * q) a k, hcm]; simp only [mul_assoc], this]
  simp only [mul_assoc]

theorem vac_comb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (LS : Lat S) (LT : Lat T)
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (P Q : Pl D → Prop) (hPQ : ∀ p, Q p → ¬ P p) (e : WO S T →₀ ℂ)
    (he : CombAt Q e) (f : WO S T → ℂ) (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P (comb ψ S T e f) := by
  have h0 : Vac ψ S T LS LT P f := by
    have e : (fun p : Pl D => P p ∨ ¬ P p) = fun _ => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    refine (((GlobalTheory.DisjComb.main D ψ hψ S T P (fun p => ¬ P p) (fun p hp hq => hq hp)).2.2.2.2 LS LT f hS hT).1 ?_).1
    rw [e]; exact hf
  exact ((GlobalTheory.DisjComb.main D ψ hψ S T Q P hPQ).2.1 e he).2 _ _ _ h0

set_option maxHeartbeats 1000000 in

theorem integ_mul_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1 + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * k) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ _ hΨ₂ φ _ G x a ha f hf k hk q₁ q₂
  have hlt : j + 1 + 1 < D.R.m := by omega
  obtain ⟨s, hs, h1, -, h3⟩ := hF.lawG (j + 1) hlt k hk
  have hom := h1 _ (vac_comb c.ψ hc.std _ _ _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) hlt) (· ∈ v.gP) (· ∈ w.Q)
    (fun p hp => Finset.disjoint_left.1 hF.disjG hp) _ (hF.atQ (j + 1)).1 Ψ₂ hΨ₂)
  have hkf : k ∈ GfC _ := GlobalTheory.LevelCut.mem_GfC_of_grpAt _ _ k ((hv.JG _ hlt).1 hk)
  have hr : rTrans (q₂ * k) f = s • rTrans q₂ f := by
    rw [hf]; exact rTrans_eigen a _ k q₂ _ s (comm_inf_fin _ ha hkf) (h3 G x)
  rw [← (ht.sFB j σ h).1] at hom
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (w.ε j α g * ·) (per_hand_mul (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) g q₁ q₂ k
    s hs hom _ _ hr)

end GlobalTheory.DStepLev
