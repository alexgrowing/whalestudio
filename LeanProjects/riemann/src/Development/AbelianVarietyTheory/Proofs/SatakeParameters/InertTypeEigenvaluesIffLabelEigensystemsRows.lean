import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UpwardThetaLiftInjectiveOnCarriedPartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertRowsEig

theorem eig_eq_of_span_maxGen {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (op : Module.End K V) (opC : Module.End ℂ W) (hj : ∀ x, j (op x) = opC (j x))
    (a : K) (S : Submodule K V) (hS : S ≤ op.maxGenEigenspace a) {v : W} (hv : v ∈ Submodule.span ℂ (j '' S))
    {l : ℂ} (hev : opC v = l • v) (hv0 : v ≠ 0) : l = σ a := by
  have hstep : ∀ y, j ((op - a • (1 : Module.End K V)) y) = (opC - σ a • (1 : Module.End ℂ W)) (j y) := by
    intro y
    simp [hj]
  have hpow : ∀ n : ℕ, ∀ y, j (((op - a • (1 : Module.End K V)) ^ n) y) = ((opC - σ a • (1 : Module.End ℂ W)) ^ n) (j y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hstep, ih]
  have h1 : ∀ x ∈ S, j x ∈ opC.maxGenEigenspace (σ a) := by
    intro x hx
    have hx' := hS hx
    rw [Module.End.mem_maxGenEigenspace] at hx' ⊢
    obtain ⟨k, hk⟩ := hx'
    exact ⟨k, by rw [← hpow, hk, map_zero]⟩
  have h2 : v ∈ opC.maxGenEigenspace (σ a) := by
    refine Submodule.span_le.2 ?_ hv
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  rw [Module.End.mem_maxGenEigenspace] at h2
  obtain ⟨k, hk⟩ := h2
  have hpv : ∀ n : ℕ, ((opC - σ a • (1 : Module.End ℂ W)) ^ n) v = (l - σ a) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hev, LinearMap.smul_apply,
        Module.End.one_apply, ← sub_smul, smul_smul, pow_succ', mul_comm (l - σ a)]
  rw [hpv, smul_eq_zero] at hk
  rcases hk with hk | hk
  · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 hk).1
  · exact absurd hk hv0

theorem inertFullEigenspaceSum_le_maxGenEigenspace {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}
    {B : BlockDat K G Pl0} (Dd : InertDat3 B I0 Ty) (p : Typ3 K Pl0 I0 Ty) (k : Dd.PlI × Ty) :
    Dd.inertTypeEigenspaceSum p ≤ (Dd.opI k).maxGenEigenspace (p.2 (Dd.plI k.1, k.2)) := by
  unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
  refine iSup₂_le fun x hx => ?_
  have h := Formalism.L2.Col.eigAt_le Dd.opAll x (Sum.inr k)
  rw [hx.2 k] at h
  exact h

theorem maxGen_zero_top {K V : Type} [Field K] [AddCommGroup V] [Module K V] :
    (0 : Module.End K V).maxGenEigenspace 0 = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp⟩

end GlobalTheory.InertRowsEig

namespace GlobalTheory.InertRowsEig

theorem hkF_single_of_not_lab {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (e : List ℤ)
    (he : ¬ IsLab V P e) (F : Bridge.Gf V → W) : hkF V P (Finsupp.single e 1) F = 0 := by
  funext h
  simp [hkF, GlobalTheory.Hk3.rep, dif_neg he]

theorem hkF_eq_sum {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = c.sum fun e z => z • hkF V P (Finsupp.single e 1) F := by
  funext h
  simp only [hkF, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem ops_decomp {D : D7} (V : HSp D) {W H : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup H] [Module ℂ H]
    (e : H →ₗ[ℂ] (Bridge.Gf V → W)) (he : Function.Injective e) (P : Pl D.host.E) (h : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hh : ∀ c x, e (h c x) = hkF V P c (e x)) (c : List ℤ →₀ ℂ) (x : H) :
    h c x = c.sum fun d z => z • h (Finsupp.single d 1) x := by
  apply he
  rw [hh, hkF_eq_sum]
  simp only [Finsupp.sum, map_sum, map_smul, hh]

theorem ops_zero {D : D7} (V : HSp D) {W H : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup H] [Module ℂ H]
    (e : H →ₗ[ℂ] (Bridge.Gf V → W)) (he : Function.Injective e) (P : Pl D.host.E) (h : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hh : ∀ c x, e (h c x) = hkF V P c (e x)) (d : List ℤ) (hd : ¬ IsLab V P d) (x : H) :
    h (Finsupp.single d 1) x = 0 := by
  apply he
  rw [hh, hkF_single_of_not_lab V P d hd, map_zero]

theorem scalar_of_decomp {H : Type} [AddCommGroup H] [Module ℂ H] (T : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hdec : ∀ c x, T c x = c.sum fun e z => z • T (Finsupp.single e 1) x) (μ : List ℤ → ℂ) {v : H} (hv : v ≠ 0)
    (hμ : ∀ e, T (Finsupp.single e 1) v = μ e • v) (cX : List ℤ →₀ ℂ) {a : ℂ} (ha : T cX v = a • v) :
    a = cX.sum fun e z => z * μ e := by
  rw [hdec] at ha
  simp only [hμ, smul_smul, Finsupp.sum, ← Finset.sum_smul] at ha
  exact (smul_left_injective ℂ hv ha).symm

theorem evC_congr {D : D7} (V : HSp D) (P : Pl D.host.E) (a a' : List ℤ → ℂ) (c0 : List ℤ →₀ ℂ)
    (h : ∀ d, IsLab V P d → a d = a' d) : evC V P a c0 = evC V P a' c0 := by
  unfold evC
  refine Finsupp.sum_congr fun d _ => ?_
  split_ifs with hd
  · rw [h d hd]
  · rfl

theorem evC_single_dual {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d)
    (hs : dualLab d = d) : evC V P (fun d => a (dualLab d)) (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]
  show a (dualLab d) = a d
  rw [hs]

theorem eq_zero_smul {H : Type} [AddCommGroup H] [Module ℂ H] {x : H} (v : H) (hx : x = 0) : x = (0 : ℂ) • v := by
  rw [hx, zero_smul]

open Classical in

noncomputable def muOf {K : Type} (n : ℕ) (σ : K → ℂ) (a : List ℕ → K) (e : List ℤ) : ℂ :=
  if h : ∃ s, Formalism.L2.Col.InertTypeOk n s ∧ e = GlobalTheory.Hk3.labIn n s then σ (a h.choose) else 0

end GlobalTheory.InertRowsEig

namespace GlobalTheory.InertRowsEig

set_option maxHeartbeats 4000000 in

theorem inert_types_iff_labels : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → R.PThmB → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → ∀ (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ), R.Carries p c → R.Carries p' c' → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)) ↔ ∀ d, IsLab (Yc D 0) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hSchur hJ hB hpos p p' c c' hc hc' Q
  obtain ⟨hcore, hSF, hplI, -, hEE, -, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have hCore := hcore hEx
  have hgood : Good R.toRealDat A3.A.μ0 (R.plI Q.1) := (hplI _ Q.1 Q.2).1
  have hconj : conjPl (R.plI Q.1) = R.plI Q.1 := (hplI _ Q.1 Q.2).2
  have hfix := GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC A3.A.μ0 (R.plI Q.1) hgood hconj
  have htwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hHowe R.toRealDat F.lv2 hLI hCore hSchur A3.A.μ0 (R.plI Q.1) hgood hconj hfix
  obtain ⟨hX, hXops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).1 A3.A.μ0
  have hinj : Function.Injective (R.HX A3.A.μ0).e := (hCore.models.HX A3.A.μ0).1

  have hvec : ∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∃ v, v ≠ 0 ∧
      v ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) ∧
      ∀ cX c0, MatchE R.toRealDat A3.A.μ0 (R.plI Q.1) cX c0 →
        hX (R.plI Q.1) cX v = evC (Yc D 0) (R.plI Q.1) (fun d => c (R.plI Q.1) (dualLab d)) c0 • v := by
    intro p c hc
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.1
    refine ⟨LinearMap.adjoint (R.Th A3.A.μ0) w, GlobalTheory.T.upward_theta_lift_injective_on_carried_part R F hB hpos p c hc w hw hw0,
      hc.2 (Submodule.mem_map_of_mem hw), fun cX c0 hm => ?_⟩
    exact (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hCore hSchur R.SF hSF A3.A.μ0 (R.plI Q.1) hgood cX c0 hm hX hXops).2 c w
      (by rw [← hEE c]; exact hw)

  have hne : ∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → (A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 ≠ ⊥ := by
    intro p c hc hbot
    obtain ⟨v, hv0, hvs, -⟩ := hvec p c hc
    rw [hbot] at hvs
    simp at hvs
    exact hv0 hvs

  have hvalid : ∀ i : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2 →
      Good R.toRealDat A3.A.μ0 (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn D.sp.X'.rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    exact ⟨(hplI _ i.1.1 i.1.2).1, (hplI _ i.1.1 i.1.2).2,
      ((GlobalTheory.Hk3.labIn_selfDual_iff D.sp.X'.rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  have hR := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
    (fun i => R.plI i.1) (fun i => GlobalTheory.Hk3.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2) hvalid (hC.inert.hR A3.A.μ0).some

  have E1 : ∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ y,
      Formalism.L2.Col.InertTypeOk D.sp.X'.rank y → ∀ c0,
      MatchE R.toRealDat A3.A.μ0 (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn D.sp.X'.rank y) 1) c0 →
        D.what₂.embLL (p.1.2 (Q.1, y)) = evC (Yc D 0) (R.plI Q.1) (fun d => c (R.plI Q.1) (dualLab d)) c0 := by
    intro p c hc y hy c0 hm
    obtain ⟨v, hv0, hvs, hev⟩ := hvec p c hc
    have hint := (hR (Q, y) hy).2.2.2 hX hXops
    exact (eig_eq_of_span_maxGen (R.jX A3.A.μ0) (A3.heckeRI A3.A.μ0 (Q, y)) _ hint _ _
      (inertFullEigenspaceSum_le_maxGenEigenspace (A3.rowI A3.A.μ0) p.1 (Q, y)) hvs (hev _ c0 hm) hv0).symm

  have hsame : ∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ y y',
      A3.heckeRI A3.A.μ0 (Q, y) = A3.heckeRI A3.A.μ0 (Q, y') → p.1.2 (Q.1, y) = p.1.2 (Q.1, y') := by
    intro p c hc y y' he
    have h1 := inertFullEigenspaceSum_le_maxGenEigenspace (A3.rowI A3.A.μ0) p.1 (Q, y)
    have h2 := inertFullEigenspaceSum_le_maxGenEigenspace (A3.rowI A3.A.μ0) p.1 (Q, y')
    change _ ≤ (A3.heckeRI A3.A.μ0 (Q, y)).maxGenEigenspace (p.1.2 (Q.1, y)) at h1
    change _ ≤ (A3.heckeRI A3.A.μ0 (Q, y')).maxGenEigenspace (p.1.2 (Q.1, y')) at h2
    rw [← he] at h2
    exact Formalism.L2.NCov.eq_of_le_maxGen (hne p c hc) h1 h2
  have hzero : ∀ (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ), R.Carries p c → ∀ y,
      A3.heckeRI A3.A.μ0 (Q, y) = 0 → p.1.2 (Q.1, y) = 0 := by
    intro p c hc y he
    have h1 := inertFullEigenspaceSum_le_maxGenEigenspace (A3.rowI A3.A.μ0) p.1 (Q, y)
    change _ ≤ (A3.heckeRI A3.A.μ0 (Q, y)).maxGenEigenspace (p.1.2 (Q.1, y)) at h1
    rw [he] at h1
    exact Formalism.L2.NCov.eq_of_le_maxGen (hne p c hc) h1 (le_top.trans maxGen_zero_top.ge)

  have hsd : ∀ d, IsLab (Yc D 0) (R.plI Q.1) d → dualLab d = d := fun d hd =>
    ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Yc D 0) (R.plI Q.1) d).1 hd).2.2 hconj
  have hdec := ops_decomp D.sp.X' (R.HX A3.A.μ0).e hinj (R.plI Q.1) (hX (R.plI Q.1)) (hXops _ hgood)
  have hnl := ops_zero D.sp.X' (R.HX A3.A.μ0).e hinj (R.plI Q.1) (hX (R.plI Q.1)) (hXops _ hgood)
  constructor
  · intro hval d hd
    obtain ⟨cX, hm⟩ := htwo.1.2 (Finsupp.single d 1)
    have key : ∀ (q : A3.fam3.base3.Ix) (b : Pl D.host.E → List ℤ → ℂ), R.Carries q b →
        b (R.plI Q.1) d = cX.sum fun e z => z * muOf D.sp.X'.rank (⇑D.what₂.embLL) (fun y => q.1.2 (Q.1, y)) e := by
      intro q b hb
      obtain ⟨v, hv0, -, hev⟩ := hvec q b hb
      have h1 := (hev cX (Finsupp.single d 1) hm).trans
        (congrArg (· • v) (evC_single_dual (Yc D 0) (R.plI Q.1) (b (R.plI Q.1)) d hd (hsd d hd)))
      refine scalar_of_decomp (hX (R.plI Q.1)) hdec _ hv0 (fun e => ?_) cX h1
      unfold muOf
      split_ifs with h
      · obtain ⟨c0, hm0⟩ := htwo.1.1 (Finsupp.single e 1)
        rw [hev _ c0 hm0]
        congr 1
        obtain ⟨hs, hse⟩ := h.choose_spec
        rw [hse] at hm0
        exact (E1 q b hb _ hs c0 hm0).symm
      · refine eq_zero_smul v (hnl e (fun hl => h ?_) v)
        obtain ⟨hlen, hpw, hsd'⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing D.sp.X' (R.plI Q.1) e).1 hl
        obtain ⟨s, h2s, hpws, hposs, hes⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff _ e).1 ⟨hlen, hpw, hsd' hconj⟩
        exact ⟨s, ⟨hpws, hposs, h2s⟩, hes⟩
    rw [key p c hc, key p' c' hc']
    exact congrArg (fun a => cX.sum fun e z => z * muOf D.sp.X'.rank (⇑D.what₂.embLL) a e) (funext hval)
  · intro hlab
    have hval : ∀ y, Formalism.L2.Col.InertTypeOk D.sp.X'.rank y → p.1.2 (Q.1, y) = p'.1.2 (Q.1, y) := by
      intro y hy
      obtain ⟨c0, hm⟩ := htwo.1.1 (Finsupp.single (GlobalTheory.Hk3.labIn D.sp.X'.rank y) 1)
      apply RingHom.injective D.what₂.embLL
      rw [E1 p c hc y hy c0 hm, E1 p' c' hc' y hy c0 hm]
      exact evC_congr _ _ _ _ c0 fun d hd => by simp only [hsd d hd]; exact hlab d hd
    intro y
    rcases hJ.R A3.A.μ0 Q y with h0 | ⟨y', hy', he⟩
    · rw [hzero p c hc y h0, hzero p' c' hc' y h0]
    · rw [hsame p c hc y y' he, hsame p' c' hc' y y' he]
      rw [← R.B.rankR] at hy'
      exact hval y' hy'

end GlobalTheory.InertRowsEig
