import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabOfReps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

noncomputable def lift (V : HSp D) (x : Bridge.Gf V) : GA D V := Classical.choose (GlobalTheory.ThetaCommutation.exists_fin_part V x)

theorem lift_mem (V : HSp D) (x : Bridge.Gf V) : lift V x ∈ GfC V :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).1

theorem finPt_lift (V : HSp D) (x : Bridge.Gf V) : finPt V (lift V x) = x :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).2

theorem eq_of_finPt (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : finPt V a = finPt V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := congrArg Subtype.val h
  have h2 : a⁻¹ * b ∈ GinfC V := by
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.1 _ h2 ((GfC V).mul_mem ((GfC V).inv_mem ha) hb)
  rw [inv_mul_eq_one] at h3
  exact h3

theorem lift_finPt (V : HSp D) {a : GA D V} (ha : a ∈ GfC V) : lift V (finPt V a) = a :=
  eq_of_finPt V (lift_mem V _) ha (finPt_lift V _)

theorem mem_GfC_of_suppAt {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {V : HSp D} {g : GA D V}
    (hg : SuppAt (idem Q) V g) : g ∈ GfC V := by
  refine GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hg
  rw [RingHom.map_add, idem, map_sum (cA D), map_sum (infPart D), map_sum (infPart D), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun PP hPP => ?_
  have h1 := (hQ.isIdemAt hPP).1
  rw [GlobalTheory.SplitScalar.infPart_splitIdem h1, GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj h1), add_zero]

theorem act_of_mem_GfC {S T : HSp D} (B : Base S T) {g : GA D S} (hg : g ∈ GfC S) : B.act g = 1 := by
  have h1 : infHom S g = 1 := hg
  have h2 : realGL B.F.θ S g = 1 := by
    funext τ
    show Formalism.UG.bc (B.F.θ τ) (infHom S g) = 1
    rw [h1, map_one]
  rw [Base.act, MonoidHom.comp_apply, h2, map_one]

noncomputable def kern {S T : HSp D} (B : Base S T) (ω : PairRep S T) (t : Twist D Circle) (x : Bridge.Gf S) :
    PolF D T.rank S.rank →ₗ[ℂ] (GA D T → ℂ) :=
  series B.F ω (B.vecFlat t) (lift S x)

noncomputable abbrev ratAct {S T : HSp D} (B : Base S T) : Representation ℂ (GQ S) (PolF D T.rank S.rank) :=
  B.act.comp (GQ S).subtype

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

variable {D : D7}

theorem gen_eq_smul {S T : HSp D} {B : Base S T} (hB : B.Good) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω₁ ωt : PairRep S T} (h1 : B.IsWeil 1 ω₁) (h2 : B.IsWeil t.chi ωt) (h : GA D S) (P : PolF D T.rank S.rank) :
    B.gen ω₁ t h P = ((detChar S t.chi h : Circle) : ℂ) • series B.F ωt (B.vecFlat t) h P := by
  have hν := ht.isHeckeChar
  have hF := ht.real
  have hω1 : IsWeilDatumO B.F.ψ S T B.mu (B.mu * B.eta⁻¹) ω₁ := by
    have := h1
    unfold Base.IsWeil at this
    simpa only [mul_one] using this
  have hωt : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * B.eta⁻¹ * t.chi) ωt := by
    have := h2
    unfold Base.IsWeil at this
    rwa [mul_right_comm B.mu t.chi] at this
  have key := ((GlobalTheory.SplitChange.change_of_splitting_pair D B.F.ψ S T B.mu (B.mu * B.eta⁻¹) t.chi ω₁ hω1 hν hF).2.1
    _ _ (muVal_detChar S hF) (muVal_detChar T hF)).2 ωt hωt
  have hth := Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) P
  funext g
  have e := key h g _ hth
  have hc : ((detChar S t.chi h : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  change ((detChar T t.chi g : Circle) : ℂ) * (ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0) =
    ((detChar S t.chi h : Circle) : ℂ) * (ωt (h, g) (B.F.fock (B.vecFlat t) P) 0)
  have e' : ωt (h, g) (B.F.fock (B.vecFlat t) P) 0 = (((detChar T t.chi g : Circle) : ℂ) *
      (((detChar S t.chi h : Circle) : ℂ))⁻¹) * ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0 := by
    have := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  rw [e']
  field_simp

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

theorem traceForm_mem_mtLat {S T : HSp D} {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K]
    {σ : K →+* ℂ} {emb : D.what₂.Tau → D.host.E →+* K} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {t : Twist D Circle}
    (hfin : ∀ x, Finite (Bridge.stab (Bridge.ratF S) (B.levJ t) x))
    (hlam : ∀ x : B.levJ t, ((B.levLam t x : ℂˣ) : ℂ) ∈ O) (h : Bridge.Gf S) {P : PolF D T.rank S.rank}
    (hP : P ∈ B.coefLat σ emb O h) :
    traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) h P ∈ B.mtLat σ emb O t := by
  have hV : P ∈ B.valSpace := (Submodule.mem_inf.1 hP).1
  rw [Base.mem_mtLat, Base.mem_formsC]
  refine ⟨⟨fun x => ?_, fun γ x k => ?_⟩, fun x => ?_⟩
  · refine finsum_induction (· ∈ B.valSpace) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ hV)
  · exact traceForm_law _ _ _ _ hfin h P γ x k
  · refine finsum_induction (· ∈ B.coefLat σ emb O x) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    by_cases hγ : γ ∈ link (Bridge.ratF S) (B.levJ t) h x
    · obtain ⟨k, rfl⟩ := (mem_link_iff _ _).1 hγ
      have e : h⁻¹ * (Bridge.ratF S γ)⁻¹ * (Bridge.ratF S γ * h * k) = k := by group
      rw [e, lamExt_coe]
      exact (B.coefLat σ emb O _).smul_mem (⟨_, hlam k⟩ : O)
        (Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hP)
    · rw [lamExt_of_not_mem _ _ hγ, zero_smul]
      exact zero_mem _

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

set_option maxHeartbeats 3000000 in

theorem dualLaw_kern {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle} (ht : t.Good)
    (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) :
    DualLaw (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (kern B ωt t) := by
  intro γ x k p
  have hW : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * t.chi * B.eta⁻¹) ωt := h2
  obtain ⟨a, ha, γf, hγf, hγ⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 (γ : GA D S)
  have hxl := lift_mem S x
  have hkl := lift_mem S (k : Bridge.Gf S)
  have hfa : finHom S a = 1 := ha
  have e1 : lift S (Bridge.ratF S γ * x * k) = γf * lift S x * lift S (k : Bridge.Gf S) := by
    refine eq_of_finPt S (lift_mem S _) ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl) ?_
    rw [finPt_lift]
    apply Subtype.ext
    have hx1 : finHom S (lift S x) = x.1 := congrArg Subtype.val (finPt_lift S x)
    have hk1 : finHom S (lift S (k : Bridge.Gf S)) = (k : Bridge.Gf S).1 := congrArg Subtype.val (finPt_lift S _)
    show finHom S (γ : GA D S) * x.1 * (k : Bridge.Gf S).1 = finHom S (γf * lift S x * lift S (k : Bridge.Gf S))
    rw [map_mul, map_mul, hx1, hk1, hγ, map_mul, hfa, one_mul]
  have e2 : ratAct B γ p = B.act a p := by
    show B.act (γ : GA D S) p = _
    rw [hγ, map_mul, act_of_mem_GfC B hγf, mul_one]
  have hcomm : γf * lift S x * lift S (k : Bridge.Gf S) * a = (γ : GA D S) * (lift S x * lift S (k : Bridge.Gf S)) := by
    rw [← (GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha _ ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl), hγ]
    group
  have hJ : finPt S (lift S (k : Bridge.Gf S)) ∈ B.levJ t := by rw [finPt_lift]; exact k.2
  have hT0 : ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p) =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) p := by
    have := ((GlobalTheory.ExportSeries.DualType.thetaSeriesData_have_dualType hB hS ht hQ).1 ωt h2 _ hkl hJ).2 p
    rwa [show (⟨finPt S (lift S (k : Bridge.Gf S)), hJ⟩ : B.levJ t) = k from Subtype.ext (finPt_lift S _)] at this
  have hK2 : ωt (a, 1) (B.F.fock (B.vecFlat t) p) = B.F.fock (B.vecFlat t) (B.act a p) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ωt t.Q (fun PP => flat (t.resC PP.1)) hB ht hQ h2 a ha p
  have hth : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) p) :=
    Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) p
  funext g
  rw [Pi.smul_apply, RingHom.id_apply, kern, kern, series_apply, series_apply, smul_eq_mul]
  rw [e1, e2, ← hK2]
  have q1 : ((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1) =
      (((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hcomm, mul_assoc]
  have e5 : ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p)) =
      ωt ((γ : GA D S), 1) (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) := by
    calc ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p))
        = ωt (((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1)) (B.F.fock (B.vecFlat t) p) := by
          rw [map_mul ωt, Module.End.mul_apply]
      _ = ωt ((((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1)) (B.F.fock (B.vecFlat t) p) := by rw [q1]
      _ = _ := by rw [map_mul ωt, map_mul ωt, Module.End.mul_apply, Module.End.mul_apply]
  have hA := hW.om_aut (γ : GA D S) γ.2 1 (one_mem _)
    (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) (hW.om_pres _ _ (hW.om_pres _ _ hth))
  simp only [e5, hA]
  simp only [hT0, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ((B.levLam t) k)), one_mul]

theorem classSum_traceForm_eq {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle}
    (ht : t.Good) (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) {I : Type} [Fintype I] {rep : I → GA D S}
    (hcl : IsClassSystem S (B.levJ t) rep) {h : GA D S} (hh : h ∈ GfC S) (P : PolF D T.rank S.rank) :
    B.classSum ωt t rep (traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (finPt S h) P) =
      series B.F ωt (B.vecFlat t) h P := by
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have key := classSum_traceForm (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) hfin
    (dualLaw_kern hB hS ht hQ h2) hcl.reps (finPt S h) P
  have e : kern B ωt t (finPt S h) P = series B.F ωt (B.vecFlat t) h P := by rw [kern, lift_finPt S hh]
  rw [← e, ← key, Base.classSum_apply, GlobalTheory.ClassTrace.classSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kern, lift_finPt S (hcl.fin i)]

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

theorem trace_cx : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k Q ψ,
    TwOK i k Q ψ →
    (∀ x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ), (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range) →
    ∀ s h P, ρ.IsDatum i j b s h P → ∀ f ∈ ρ.gens i j b k Q ψ h P, ∃ F ∈ ρ.mt i j b k Q ψ, f = ρ.sum i j b k Q ψ F := by
  intro D ρ hρ i j b k Q ψ hok hlam s h P hd f hf
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hok
  obtain ⟨hQ, hsupp, rfl⟩ := hf
  have hB := hρ.base i j b
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  have hcl := hρ.classes i j b _ ht hadm
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have hh : h * hQ ∈ GfC (Vc D j) := (GfC _).mul_mem hd.fin (mem_GfC_of_suppAt ht.split hsupp)
  have hdisj : Disjoint (ρ.tw i b k Q ψ).Q (D.ntw.S0 i) := hok.2.1.mono_left fun x hx =>
    (mem_half.1 (show x ∈ half (ρ.ch i) Q from hx)).1
  have hP : P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) :=
    GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l D ρ hρ i j b k _ h hQ P ht.split hdisj hd.fin hsupp hd.mem
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) ∈ (ρ.eOk i b k).range := ⟨u, hu.symm⟩
  refine ⟨(⟨_, hc⟩ : (ρ.eOk i b k).range) • traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P,
    Submodule.smul_mem _ _ (traceForm_mem_mtLat hB (hρ.isCoefRing_k i b k) hfin hlam _ hP), ?_⟩
  rw [gen_eq_smul hB ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)]
  change _ = (ρ.B i j b).classSum _ _ _
    (((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) •
      traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P)
  rw [map_smul, classSum_traceForm_eq hB hS ht hadm (hρ.weil i j b _ ht) hcl hh]

end GlobalTheory.TwTraceCx

end
