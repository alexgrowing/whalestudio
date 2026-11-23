import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepSuppSecond

variable {D : D7}

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem grpAt_inter {V : HSp D} {P P' R : Pl D → Prop} (h : ∀ p, P p → P' p → R p) {g : GA D V}
    (hg : g ∈ grpAt V P) (hg' : g ∈ grpAt V P') : g ∈ grpAt V R := by
  rw [grpAt, mem_congGrp] at hg hg' ⊢
  intro i j
  have h1 := hg i j
  have h2 := hg' i j
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h1 h2 ⊢
  refine ⟨h1.1, fun u => ?_⟩
  by_cases hp : P u.1
  · exact h2.2 ⟨u.1, fun hp' => u.2 (h _ hp hp')⟩
  · exact h1.2 ⟨u.1, hp⟩

theorem grpAt_mono {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpAt V R := grpAt_inter (fun p hp _ => h p hp) hg hg

theorem grpAt_off {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → ¬ R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpOff V R := by
  rw [grpAt, mem_congGrp] at hg
  rw [grpOff, mem_congGrp]
  intro i j
  have h1 := hg i j
  simp only [idAt, idOff, Submodule.mem_inf, Submodule.mem_iInf] at h1 ⊢
  exact fun u => h1.2 ⟨u.1, fun hp => h _ hp u.2⟩

theorem grpAt_fin {V : HSp D} {P : Pl D → Prop} {g : GA D V} (hg : g ∈ grpAt V P) : g ∈ GfC V :=
  (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V ∅).2.2.2.1 (grpAt_mono (fun p _ => Finset.notMem_empty p) hg)

theorem split_two {V : HSp D} (G Q : Finset (Pl D)) {x : GA D V} (hx : x ∈ GfC V)
    (hx' : x ∈ grpOff V fun p => p ∉ G ∧ p ∉ Q) :
    ∃ y ∈ grpAt V (· ∈ Q), ∃ z ∈ grpAt V (· ∈ G), x = y * z := by
  obtain ⟨-, -, hQ, -, -, ⟨e, he⟩, -, hinf, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q
  obtain ⟨p, hp⟩ := e.surjective ⟨x, hx⟩
  have hxe : x = p.1.1 * p.2.1 := by rw [← he p, hp]
  refine ⟨p.1.1, p.1.2, p.2.1, ?_, hxe⟩
  have h1 : p.2.1 ∈ grpAt V fun q => ¬ (q ∉ G ∧ q ∉ Q) := by
    rw [← hinf]
    have : p.2.1 = p.1.1⁻¹ * x := by rw [hxe]; group
    rw [this]
    exact Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem (hQ p.1.2)) hx, mul_mem (inv_mem (grpAt_off (fun q hq hq' => hq'.2 hq) p.1.2)) hx'⟩
  exact grpAt_inter (fun q h h' => by_contra fun hG => h ⟨hG, h'⟩) h1 p.2.2

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f := by
  have hm : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P' := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hm hu), fun e he u hu hh => hf.2.2 e he u (hm hu) hh⟩

theorem moved_data {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {G Q : Finset (Pl D)} (hd : Disjoint Q G)
    {eG eQ : WO S T →₀ ℂ} (hG : CombAt (· ∈ G) eG) (hQ : CombAt (· ∈ Q) eQ) {Ψ : WO S T → ℂ}
    (hΨ : Vac ψ S T LS LT (fun _ => True) Ψ) {a : GA D S} {b : GA D T} (ha : a ∈ grpAt S (· ∈ Q)) (hb : b ∈ grpAt T (· ∈ Q)) :
    Vac ψ S T LS LT (fun p => p ∉ G ∧ p ∉ Q) (om (a, b) (comb ψ S T eG (comb ψ S T eQ Ψ))) ∧
      ∃ Ψ', Vac ψ S T LS LT (· ∈ G) Ψ' ∧ om (a, b) (comb ψ S T eG (comb ψ S T eQ Ψ)) = comb ψ S T eG Ψ' := by
  have hI := GlobalTheory.DisjComb.main D ψ hW.std S T
  have hQG : ∀ p, p ∈ Q → ¬ p ∈ G := fun p hp => Finset.disjoint_left.mp hd hp
  have hQo : ∀ p, p ∈ Q → ¬ (p ∉ G ∧ p ∉ Q) := fun p hp h => h.2 hp
  have hGo : ∀ p, p ∈ G → ¬ (p ∉ G ∧ p ∉ Q) := fun p hp h => h.1 hp
  have h1 : Vac ψ S T LS LT (· ∈ G) (comb ψ S T eQ Ψ) :=
    ((hI (· ∈ Q) (· ∈ G) hQG).2.1 eQ hQ).2 _ _ _ (vac_mono (fun _ _ => trivial) hΨ)
  refine ⟨GlobalTheory.OffPlaceWeil.vac_off hW ?_ (grpAt_off hQo ha) (grpAt_off hQo hb), om (a, b) (comb ψ S T eQ Ψ),
    GlobalTheory.OffPlaceWeil.vac_off hW h1 (grpAt_off hQG ha) (grpAt_off hQG hb), ?_⟩
  · exact ((hI (· ∈ G) _ hGo).2.1 eG hG).2 _ _ _
      (((hI (· ∈ Q) _ hQo).2.1 eQ hQ).2 _ _ _ (vac_mono (fun _ _ => trivial) hΨ))
  · exact (hI (· ∈ G) _ hGo).2.2.1 χS χT om hW eG hG a (grpAt_off hQG ha) b (grpAt_off hQG hb) _ h1.1

theorem om_mul {S T : HSp D} (om : Om S T) (a a' : GA D S) (b b' : GA D T) (f : WO S T → ℂ) :
    om (a * a', b * b') f = om (a, b) (om (a', b') f) := by
  rw [← Prod.mk_mul_mk, map_mul]
  rfl

theorem integ_support : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∀ q₂ ∈ GfC (c.V (j + 1 + 1)), integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1 + 1), q₂ = r * y * (κ * k) := by
  intro D c v t w hc hv ht hF hW hO hGs _ hC hFl j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ q₁ hq₁ q₂ hq₂ hne
  obtain ⟨α, -, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨g, hg, hαg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have hgQ := (hF.e j α).2 g hg
  have e₁ := (ht.sBF j (σ + 1) h).1
  have e₂ := (ht.sFB j σ h).1
  have W₁ : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) _ _ (t.om j) := e₁ ▸ (t.sBF j (σ + 1) h).weil
  have W₂ : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) _ _ (t.om (j + 1)) := e₂ ▸ (t.sFB j σ h).weil
  set Φ₁ := comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁) with hΦ₁
  set Φ₂ := comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) with hΦ₂
  have hH : handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
      (flatBF (t.sBF j (σ + 1) h) (t.om j (g, q₁) Φ₁))) (flatFB (t.sFB j σ h) (t.om (j + 1) (q₁, q₂) Φ₂)) ≠ 0 := by
    intro h0
    apply hαg
    have hp := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).2.2
      0 1 0 (rTrans q₂ f)
    rw [zero_smul, one_smul, zero_mul, zero_mul] at hp
    rw [Chain.hand, e₁, e₂]
    erw [h0, hp]
    exact mul_zero _
  obtain ⟨V₁, Ψ₁', V₁', E₁⟩ := moved_data W₁ hF.disjG (hv.atG j).1 (hF.atQ j).1 h₁ hgQ hq₁
  obtain ⟨V₂, -⟩ := moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ (one_mem _)
  obtain ⟨-, hfix, -, hbig⟩ := hO j σ h _ _ V₁ V₂
  obtain ⟨r, hr, hrP, y, hy, κ, hκ, hq⟩ := hbig (φ α) (hφ α) q₂ (by
    rw [Chain.hand, e₁, e₂]
    erw [← om_mul, ← om_mul]
    simp only [one_mul, mul_one]
    exact hH)
  have hyf : y ∈ GfC (c.V (j + 1 + 1)) := by
    have : y = r⁻¹ * q₂ * κ⁻¹ := by rw [hq]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (grpAt_fin hrP)) hq₂) (inv_mem (grpAt_fin hκ.1))
  obtain ⟨yQ, hyQ, z, hz, rfl⟩ := split_two v.gP w.Q hyf hy
  have comm := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1 + 1)) v.gP).2.2.2.2.1
  have hQG : ∀ p, p ∈ w.Q → p ∉ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hyQ' := grpAt_mono hQG hyQ
  have hκ' : κ ∈ grpAt _ (· ∉ v.gP) := grpAt_mono (fun p hp => hp.1) hκ.1
  obtain ⟨-, Ψ₂', V₂', E₂⟩ := moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ hyQ
  have hΦ : t.om (j + 1) (q₁, q₂) Φ₂ =
      t.om (j + 1) (1, r) (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) := by
    have s1 : t.om (j + 1) (q₁, q₂) Φ₂ =
        t.om (j + 1) (1, r * (yQ * z)) (t.om (j + 1) (1, κ) (t.om (j + 1) (q₁, 1) Φ₂)) := by
      rw [← om_mul, ← om_mul, hq]
      simp only [one_mul, mul_one]
    rw [s1, hfix κ hκ, ← E₂, ← om_mul, ← om_mul, ← om_mul, ← comm z hz yQ hyQ']
    simp only [one_mul, mul_one, mul_assoc]
  have T₁ : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (v.eG j) Ψ₁') := E₁ ▸ V₁.1
  have T₂ : IsThetaFunO c.ψ _ _ (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) := by
    refine W₂.om_pres _ _ ?_
    rw [← E₂]
    exact (moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ hyQ).1.1
  have hR := (GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant D c.ψ (offP v w)).2 σ _ _ (t.sFB j σ h) (c.vL j σ h)
    (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h) (comb c.ψ _ _ (v.eG j) Ψ₁'))) _ T₂ r hr hrP
  rw [e₂] at hR
  rw [hΦ, E₁] at hH
  have hH' := fun h0 => hH (hR.2 h0)
  have hctr : c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁')
      (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) ≠ 0 := by
    intro h0
    apply hH'
    obtain ⟨χA, χA', χz, omz, omz', a1, a2, a3, a4, a5, a6⟩ := hW.mid j σ h
    have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hFl c.ψ
    have hcl := (hC c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz _ omz _ omz'
      a1 a2 a3 a4 a5 a6 (φ α) _ _ (hv.ram j _ (hφ α)).1 (hth.1 _ _ _ (t.sBF j (σ + 1) h) _ T₁)
      (hth.2 _ _ _ (t.sFB j σ h) _ T₂)).2.2
    funext h₂
    rw [hcl h₂]
    unfold Comm.ctr at h0
    erw [h0]
    have z1 : ∀ p vv, t.kom j p (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0 = 0 :=
      fun p vv => congrFun (map_zero (t.kom j p)) 0
    have z2 : ∀ p p', t.kom (j + 1) p' (fun vv => t.kom j p
        (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0) 0 = 0 := by
      intro p p'
      rw [show (fun vv => t.kom j p
        (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0) = 0 from funext (z1 p)]
      exact congrFun (map_zero (t.kom (j + 1) p')) 0
    refine (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun h₁ => ?_)).trans (integral_zero _ _)
    refine (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun h₀ => ?_)).trans (integral_zero _ _)
    exact mul_eq_zero_of_right _ (z2 _ _)
  obtain ⟨r', hr', hr'G, k, hk, hzk⟩ := (hGs j σ h Ψ₁' Ψ₂' V₁' V₂').2 z hz hctr
  have hkG := (hv.JG (j + 1 + 1) (by omega)).1 hk
  refine ⟨r * r', mul_mem hr hr', mul_mem (grpAt_fin hrP) (grpAt_fin hr'G), yQ, hyQ, κ, hκ, k, hk, ?_⟩
  rw [hq, hzk, ← comm k hkG κ hκ', mul_assoc r r' yQ, comm r' hr'G yQ hyQ']
  simp only [mul_assoc]

end GlobalTheory.DStepSuppSecond

end
