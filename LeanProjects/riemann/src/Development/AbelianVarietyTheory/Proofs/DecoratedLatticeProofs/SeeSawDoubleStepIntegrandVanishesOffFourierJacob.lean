import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepSupp

variable {D : D7}

theorem mem_cong {V : HSp D} {I : Ideal (AE D)} {g : GA D V}
    (h : ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I) : g ∈ congGrp V I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  ext i j
  have := h i j
  rw [← Ideal.Quotient.eq] at this
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem off_union {V : HSp D} {P P' R : Pl D → Prop} (hR : ∀ p, R p → P p ∨ P' p) {g : GA D V} (h : g ∈ grpOff V P)
    (h' : g ∈ grpOff V P') : g ∈ grpOff V R := by
  refine mem_cong fun i j => ?_
  have a := GlobalTheory.DisjComb.mem_congGrp' h i j
  have b := GlobalTheory.DisjComb.mem_congGrp' h' i j
  unfold idOff at a b ⊢
  simp only [Submodule.mem_iInf] at a b ⊢
  intro u
  rcases hR u.1 u.2 with k | k
  · exact a ⟨u.1, k⟩
  · exact b ⟨u.1, k⟩

theorem at_le_off (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V ∅).2.2.2.2.2.2.1 P P' h

theorem at_eq (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V ∅).2.2.2.2.2.2.2.1]
  simp only [not_not]

theorem at_le_fin (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := by
  rw [at_eq]; exact inf_le_left

theorem at_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  rw [at_eq V P']
  exact le_inf (at_le_fin V P) (at_le_off V fun p hp hn => hn (h p hp))

theorem split_two (V : HSp D) (A B : Finset (Pl D)) {x : GA D V} (hx : x ∈ GfC V)
    (ho : x ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B)) :
    ∃ a ∈ grpAt V (· ∈ A), ∃ b ∈ grpAt V (· ∈ B), b ∈ grpAt V (· ∉ A) ∧ x = a * b := by
  obtain ⟨e, he⟩ := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V A).2.2.2.2.2.1
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨x, hx⟩
  have h1 : x = a.1 * b.1 := by
    have := he (a, b)
    rw [hab] at this
    exact this
  refine ⟨a.1, a.2, b.1, ?_, b.2, h1⟩
  rw [at_eq]
  refine ⟨at_le_fin V _ b.2, ?_⟩
  have hb1 : b.1 ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B) := by
    have : b.1 = a.1⁻¹ * x := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem (at_le_off V (fun p hp hn => hn.1 hp) a.2)) ho
  have hb2 : b.1 ∈ grpOff V (· ∈ A) := at_le_off V (fun p hp hn => hp hn) b.2
  refine off_union (fun p hp => ?_) hb1 hb2
  by_cases h : p ∈ A
  · exact Or.inr h
  · exact Or.inl ⟨h, hp⟩

theorem vac_om {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu e
    have := hW.om_heis g h u f hf.1
    rw [GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu), e] at this
    exact this.symm
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (hQ : ∀ p, Q p → P p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hm : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hm hu), fun e he u hu => hf.2.2 e he u (hm hu)⟩

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  intro D c v t w hc hv ht hf _ hoff hG _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ q₁ hq₁ q₂ hne
  have DC := GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hom := (ht.sBF j (σ + 1) h).1
  have hW : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
    rw [← hom]; exact (t.sBF j (σ + 1) h).weil
  have hGQ : ∀ p, p ∈ w.Q → p ∉ v.gP := fun p hp => Finset.disjoint_left.1 hf.disjG hp

  obtain ⟨g, hg, hflat⟩ : ∃ g ∈ grpAt (c.V j) (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h)
      (t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))) ≠ 0 := by
    unfold integ at hne
    obtain ⟨α, -, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨g, hg, hg'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    refine ⟨g, (hf.e j α).2 g hg, fun h0 => hg' ?_⟩
    rw [← hom] at h0
    have H := GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)
    unfold Chain.hand
    erw [h0, H.2.1]
    have := H.2.2 0 1 0 (rTrans q₂ f)
    rw [zero_smul, one_smul, zero_mul, zero_mul] at this
    erw [this, mul_zero]

  have vQ : ∀ P : Pl D → Prop, (∀ p, p ∈ w.Q → ¬ P p) →
      Vac c.ψ _ _ (v.N j) (v.N (j + 1)) P (comb c.ψ _ _ (w.eQ j) Ψ₁) := fun P hP =>
    ((DC (· ∈ w.Q) P hP).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ (vac_mono (fun _ _ => trivial) h₁)
  have k₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) :=
    ((DC (· ∈ v.gP) (offP v w) (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vQ _ fun p hp hn => hn.2 hp)
  have k₂ : ∀ P, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) P Ψ₂ := fun P => vac_mono (fun _ _ => trivial) h₂
  have k₁' := vac_om hW k₁ (at_le_off _ (fun p hp hn => hn.2 hp) hg) (one_mem (grpOff (c.V (j + 1)) (offP v w)))
  have mulom : ∀ (g₁ g₂ : GA D (c.V j)) (y₁ y₂ : GA D (c.V (j + 1))) (Φ : WO (c.V j) (c.V (j + 1)) → ℂ),
      t.om j (g₁ * g₂, y₁ * y₂) Φ = t.om j (g₁, y₁) (t.om j (g₂, y₂) Φ) := by
    intro g₁ g₂ y₁ y₂ Φ
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  obtain ⟨r, hr, hrP, z, hz, κ, hκ, hdec⟩ := (hoff j σ h _ _ k₁' (k₂ _)).2.2.1 q₁ (by
    rw [← mulom, one_mul, mul_one]; exact hflat)
  have hzf : z ∈ GfC (c.V (j + 1)) := by
    have : z = r⁻¹ * q₁ * κ⁻¹ := by rw [hdec]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (at_le_fin _ _ hrP)) hq₁) (inv_mem (at_le_fin _ _ hκ.1))
  obtain ⟨s, hs, y, hy, hy', hzs⟩ := split_two (c.V (j + 1)) v.gP w.Q hzf hz

  have e₁ := ((hoff j σ h _ _ k₁ (k₂ _)).1 κ hκ).1
  have hgo : g ∈ grpOff (c.V j) (· ∈ v.gP) := at_le_off _ hGQ hg
  have hyo : y ∈ grpOff (c.V (j + 1)) (· ∈ v.gP) := at_le_off _ hGQ hy
  have vG := vQ (· ∈ v.gP) hGQ
  have e₂ := (DC (· ∈ v.gP) (fun _ => False) (fun _ _ => id)).2.2.1 _ _ _ hW (v.eG j) (hv.atG j).1 g hgo y hyo _ vG.1
  have e₃ : t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (1, r) (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    conv_rhs => rw [← e₁]
    rw [← mulom, ← mulom, ← mulom, hdec, hzs]
    simp only [one_mul, mul_one, mul_assoc]
  have th : IsThetaFunO c.ψ _ _ (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    exact hW.om_pres _ _ (hW.om_pres _ _ k₁.1)
  have hfl : flatBF (t.sBF j (σ + 1) h)
      (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) ≠ 0 := by
    intro h0
    apply hflat
    have := ((GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant D c.ψ (offP v w)).1 _ _ _ (t.sBF j (σ + 1) h) _ th r hr hrP).2 h0
    rw [hom] at this
    rw [e₃]
    exact this
  obtain ⟨r', hr', hr'P, k, hk, hsk⟩ := (hG j σ h _ _ (vac_om hW vG hgo hyo) (k₂ _)).1 s hs hfl
  refine ⟨r * r', mul_mem hr hr', mul_mem (at_le_fin _ _ hrP) (at_le_fin _ _ hr'P), y, hy, κ, hκ, k, hk, ?_⟩
  have hkP : k ∈ grpAt (c.V (j + 1)) (· ∈ v.gP) := (hv.JG (j + 1) (by omega)).1 hk
  have hcm := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) v.gP).2.2.2.2.1 k hkP (y * κ)
    (mul_mem hy' (at_mono _ (fun p hp => hp.1) hκ.1))
  rw [hdec, hzs, hsk]
  calc r * (r' * k * y) * κ = r * r' * (k * (y * κ)) := by group
    _ = r * r' * y * (κ * k) := by rw [hcm]; group

end GlobalTheory.DStepSupp
