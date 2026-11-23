import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.InertLift

variable {D : D7}

theorem hkF_comb (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = ∑ d ∈ c.support, c d • hkF V P (Finsupp.single d 1) F := by
  funext h
  simp only [hkF, Finset.sum_apply, Pi.smul_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem hkF_nonlab (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) {d : List ℤ}
    (hd : ¬ IsLab V P d) (F : Bridge.Gf V → W) : hkF V P (Finsupp.single d 1) F = 0 := by
  funext h
  simp [hkF, rep, hd]

open Classical in

def tyOf (n : ℕ) (e : List ℤ) : List ℕ :=
  if h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y then h.choose else []

theorem labIn_tyOf {n : ℕ} {e : List ℤ} (h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y) :
    Formalism.L2.Col.InertTypeOk n (tyOf n e) ∧ e = GlobalTheory.Hk3.labIn n (tyOf n e) := by
  have hs : tyOf n e = h.choose := by
    simp only [tyOf]
    rw [dif_pos h]
  rw [hs]
  exact h.choose_spec

open Classical in

def valC (Lb : List ℤ → Prop) (n : ℕ) (a : List ℕ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  ∑ e ∈ c.support, c e * (if Lb e then a (tyOf n e) else 0)

open Classical in

theorem comb_apply {M X : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X] (e : M →ₗ[ℂ] X)
    (he : Function.Injective e) (h : (List ℤ →₀ ℂ) → Module.End ℂ M) (Tt : (List ℤ →₀ ℂ) → X → X)
    (hh : ∀ c x, e (h c x) = Tt c (e x))
    (hT : ∀ c F, Tt c F = ∑ d ∈ c.support, c d • Tt (Finsupp.single d 1) F)
    (Lb : List ℤ → Prop) (hT0 : ∀ d, ¬ Lb d → ∀ F, Tt (Finsupp.single d 1) F = 0) (n : ℕ) (a : List ℕ → ℂ) (u : M)
    (hlab : ∀ d, Lb d → ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ d = GlobalTheory.Hk3.labIn n y)
    (heig : ∀ y, Formalism.L2.Col.InertTypeOk n y → h (Finsupp.single (GlobalTheory.Hk3.labIn n y) 1) u = a y • u) (c : List ℤ →₀ ℂ) :
    h c u = valC Lb n a c • u := by
  have hone : ∀ d, h (Finsupp.single d 1) u = (if Lb d then a (tyOf n d) else 0) • u := by
    intro d
    by_cases hd : Lb d
    · obtain ⟨h1, h2⟩ := labIn_tyOf (hlab d hd)
      have := heig _ h1
      rw [← h2] at this
      rw [if_pos hd, this]
    · rw [if_neg hd, zero_smul]
      apply he
      rw [hh, hT0 d hd, map_zero]
  apply he
  rw [hh, hT, valC, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul, ← hone d, map_smul, hh]

theorem evC_congr (V : HSp D) (P : Pl D.host.E) {a b : List ℤ → ℂ} (hab : ∀ d, IsLab V P d → a d = b d) (c : List ℤ →₀ ℂ) :
    evC V P a c = evC V P b c := by
  classical
  simp only [evC, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : IsLab V P d
  · rw [if_pos hd, if_pos hd, hab d hd]
  · rw [if_neg hd, if_neg hd]

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tied_label (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m)
    (Q : A3.okI A3.A.μ0) (y : List ℕ) (hy : Formalism.L2.Col.InertTypeOk (Vc D j).rank y) :
    ∀ h, IsOpsV R.toRealDat j A3.A.μ0 h → ∀ f : (A3.A.fam.L j A3.A.μ0).S.Forms,
      R.jV j A3.A.μ0 ((A3.liftI j A3.A.μ0).opAll (Sum.inr (Q, y)) f) =
      h (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 f) := by
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hOk := h3.2.2.1
  have hin : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 →
      Good R.toRealDat A3.A.μ0 (R.plI k.1.1) ∧ conjPl (R.plI k.1.1) = R.plI k.1.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
    ⟨(hOk A3.A.μ0 k.1.1 k.1.2).1, (hOk A3.A.μ0 k.1.1 k.1.2).2,
      ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
  exact (hC.inert.hL j A3.A.μ0).elim fun Comparison₂ =>
    (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) hin Comparison₂ (Q, y) hy).2.2.2

theorem one_side (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hSch : SchurAll R.toRealDat) (hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) (j : Fin D.R.m)
    (c : Pl D.host.E → List ℤ → ℂ) (s : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms)
    (hx : ∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x)
    (hm : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c) (h0 : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
    (Q : A3.okI A3.A.μ0) :
    (∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → ∀ cW,
      MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) cW →
      D.what₂.embLL (s (Sum.inr (Q, y))) = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW) ∧
    (∀ d, IsLab (Wc D j) (R.plI Q.1) d → ∀ cV, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV (Finsupp.single d 1) →
      c (R.plI Q.1) d =
        valC (IsLab (Vc D j) (R.plI Q.1)) (Vc D j).rank (fun y => D.what₂.embLL (s (Sum.inr (Q, y)))) cV) := by
  classical
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hSF := h3.2.1
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hVall := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models).2 j A3.A.μ0
  have hWall := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 core hSch hIrr R.SF hSF j
  obtain ⟨hV, hVo, -⟩ := hVall
  obtain ⟨hW, hWo, -, -, -, -, hWev, -⟩ := hWall
  have hwW : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ Wcc R.toRealDat R.SF j c := hm
  have heig : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y →
      hV (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (s (Sum.inr (Q, y))) • R.jV j A3.A.μ0 x := fun y hy =>
    (tied_label R F hC hEx j Q y hy hV hVo x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) (hx (Sum.inr (Q, y)))).trans (LinearMap.map_smulₛₗ (R.jV j A3.A.μ0) _ x))
  have hlab : ∀ d, IsLab (Vc D j) (R.plI Q.1) d →
      ∃ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y ∧ d = GlobalTheory.Hk3.labIn (Vc D j).rank y := by
    intro d hd
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) (R.plI Q.1) d).1 hd
    obtain ⟨y, ya, yb, yc, yd⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff _ d).1 ⟨h1, h2, h3 hcj⟩
    exact ⟨y, ⟨yb, yc, ya⟩, yd⟩
  have hthe : ∀ cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      R.thG j A3.A.μ0 (hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x)) =
        hW (R.plI Q.1) cW (R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x)) := fun cV cW hM =>
    (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 core hSch hIrr R.SF hSF j A3.A.μ0 (R.plI Q.1) hg cV cW hM hV hVo).1 hW hWo
      (R.jV j A3.A.μ0 x)
  have hchain : ∀ (v : ℂ) cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x) = v • R.jV j A3.A.μ0 x →
      v = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW := fun v cV cW hM hv =>
    smul_left_injective ℂ h0 (((R.thG j A3.A.μ0).map_smul v _).symm.trans
      ((congrArg (R.thG j A3.A.μ0) hv.symm).trans ((hthe cV cW hM).trans (hWev c _ hg cW _ hwW))))
  refine ⟨fun y hy cW hM => hchain _ _ cW hM (heig y hy), fun d hd cV hM => ?_⟩
  have h2 : evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) (Finsupp.single d 1) = c (R.plI Q.1) d := by
    simp [evC, hd]
  refine h2.symm.trans (hchain _ cV _ hM ?_).symm
  exact comb_apply (R.HV j A3.A.μ0).e (core.models.HV j A3.A.μ0).1 (hV (R.plI Q.1)) (hkF (Vc D j) (R.plI Q.1))
    (fun c y => hVo _ hg c y) (hkF_comb (Vc D j) (R.plI Q.1)) (IsLab (Vc D j) (R.plI Q.1))
    (fun d hd F => hkF_nonlab (Vc D j) (R.plI Q.1) hd F) (Vc D j).rank _ _ hlab heig cV

end Main

end GlobalTheory.Hk3.InertLift

open GlobalTheory.Hk3.InertLift in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.lift_inert_iff : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ (j : Fin D.R.m) (c c' : Pl D.host.E → List ℤ → ℂ) (s s' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = s' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) ↔ ∀ d, IsLab (Wc D j) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ hIrr j c c' s s' x x' hx hm h0 hx' hm' h0' Q
  have h3 := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := h3.1 hEx
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hTwo := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hInt core hSch A3.A.μ0 _ hg hcj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC A3.A.μ0 _ hg hcj)
  obtain ⟨a1, a2⟩ := one_side R F hC hEx hSch hIrr j c s x hx hm h0 Q
  obtain ⟨b1, b2⟩ := one_side R F hC hEx hSch hIrr j c' s' x' hx' hm' h0' Q
  constructor
  · intro hs d hd
    obtain ⟨cV, hM⟩ := (hTwo.2 j).2 (Finsupp.single d 1)
    rw [a2 d hd cV hM, b2 d hd cV hM]
    simp only [hs]
  · intro hcc y
    have hval : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y)) := by
      intro y hy
      obtain ⟨cW, hM⟩ := (hTwo.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1)
      apply D.what₂.embLL.injective
      rw [a1 y hy cW hM, b1 y hy cW hM]
      exact evC_congr _ _ hcc cW
    have hx0 : x ≠ 0 := fun e => h0 ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hx0' : x' ≠ 0 := fun e => h0' ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.B.rankL j
    have e1 : A3.heckeLI j A3.A.μ0 (Q, y) x = s (Sum.inr (Q, y)) • x := hx (Sum.inr (Q, y))
    have e2 : A3.heckeLI j A3.A.μ0 (Q, y) x' = s' (Sum.inr (Q, y)) • x' := hx' (Sum.inr (Q, y))
    rcases hJ.L j A3.A.μ0 Q y with hz | ⟨y', hy', he⟩
    · have z1 : s (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun hz x).trans (zero_smul _ x).symm))
      have z2 : s' (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun hz x').trans (zero_smul _ x').symm))
      rw [z1, z2]
    · have f1 : A3.heckeLI j A3.A.μ0 (Q, y') x = s (Sum.inr (Q, y')) • x := hx (Sum.inr (Q, y'))
      have f2 : A3.heckeLI j A3.A.μ0 (Q, y') x' = s' (Sum.inr (Q, y')) • x' := hx' (Sum.inr (Q, y'))
      have g1 : s (Sum.inr (Q, y)) = s (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun he x).trans f1))
      have g2 : s' (Sum.inr (Q, y)) = s' (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun he x').trans f2))
      rw [g1, g2]
      exact hval y' (hrk ▸ hy')

end
