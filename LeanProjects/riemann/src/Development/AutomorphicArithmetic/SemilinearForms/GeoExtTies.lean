import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivAllEnl
import Development.AutomorphicArithmetic.UnitTensorPairings.GeometricActionOverCoefficientExtension
import Development.AutomorphicArithmetic.UnitTensorPairings.ThetaLiftDataOverCoefficientExtension
import Development.AutomorphicArithmetic.UnitTensorPairings.CuspSectionsOverCoefficientExtension

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

namespace UpperTheory.Mem.GeoExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

section Two

variable {D' : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0' T0' : Type} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}
  {T' : CoreJ D'} [Algebra T'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' T'.Q.c.F} {κ' : ∀ i : Fin D'.R.m, WeightFamilies.Wt D' ((i : ℕ) + 1)}
  {v₀' : ∀ (i : Fin D'.R.m) (σ : D'.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {i' : Fin D'.R.m}

theorem center_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {z : G} (hz : z ∈ Subgroup.center G) :
    φ z ∈ Subgroup.center G' := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g]

set_option maxHeartbeats 2000000 in

theorem oneMapOf_two (hR : PreChar R') (hchi : R'.grp_chiW) (hT : TieIn T' R' κ' v₀')
    (O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0)) (hF : O'.c'.F = D'.what₂.embLL.toRatAlgHom.fieldRange)
    (hP' : O'.Pins (κ' i') (v₀' i' (sg0 D' A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0))
    {cE' : (T'.U ((i' : ℕ) + 1) O'.s0).Comp → ℂ} (hU : ∀ k, ‖cE' k‖ = 1) (hE : O'.EquivAt (κ' i') cE')
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec} {ι x₀}
    (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1)
    (hV : R.models_HV) (hj : R.models_jV) (hL : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (hO : OmOver O O')
    (φ : G ≃* G') (pt : AutQ (Wc D' i') → AutQ (Wc D i)) (e : (R.HV i A.μ0).H ≃ₗ[ℂ] (R'.HV i' A'.μ0).H)
    (he : ∀ y, HEq (e y) y ∧ ∀ q, R'.thF i' A'.μ0 (e y) (v₀' i' (sg0 D' A')) q.out = R.thF i A.μ0 y v₀ (pt q).out)
    (hf : ∀ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (hle : O.c'.F ≤ c.F), HEq O'.c' c →
      ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        ∃ f' ∈ sec (T'.Q.Xo ((i' : ℕ) + 1)) O'.c' (wtA (κ' i')) (Vc D' i').rank, HEq f' (GlobalTheory.FieldBC.rulBC hle f) ∧ ∀ z q,
          (lieFac (T'.Q.Dw ((i' : ℕ) + 1)) (xiR D') (wtA (κ' i')) : ℂ) * adOver O' cE' (actLev O'.c' O'.lev2 (φ z) f') q.out =
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) (pt q).out) :
    O'.OneMapOf (κ' i') (v₀' i' (sg0 D' A')) cE' 1 := by
  refine (lift_of_oneMapOf O hP h).elim fun z h0 => h0.2.elim fun ζ h0' => h0'.2.2.elim fun r h0'' => h0''.elim fun J h1 => ?_
  refine hO.2.elim fun c hO => hO.elim fun hle hO => (hO.2 r J h1.1).elim fun r' h2 => h2.elim fun J' h2 => ?_
  refine oneMapOf_of_span hR hchi hT O' hF hP' hU hE (center_map φ h0.1) (hL h0'.1) h0'.2.1 ?_
  have h3 := span_image e (GlobalTheory.LiftScalarCompare.span_jVx hV hj)
  refine top_le_iff.1 (h3.ge.trans (Submodule.span_mono fun y hy => ?_))
  refine hy.elim fun y₁ hy => hy.1.elim fun y₀ hy₀ => ?_
  have hy' : e (jVx R i A.μ0 y₀) = y := (congrArg e hy₀).trans hy.2
  refine hy' ▸ ?_
  refine (h1.2 y₀).elim fun x h4 => h4.elim fun f h4 => ?_
  refine (h2.2 y₀ x h4.1 _ (he _).1).elim fun x' h8 => ?_
  refine (hf c hle hO.1 f h4.2.1).elim fun f' h10 => ?_
  refine ⟨r', J', x', f', h2.1, h8.1, h10.1, h8.2 _ _ f h4.2.1 h4.2.2.1 f' h10.2.1, fun q => ?_⟩
  exact ((he _).2 q).trans ((h4.2.2.2 _).trans ((mul_assoc _ _ _).trans ((congrArg (ζ * ·) (h10.2.2 z q).symm).trans
    (mul_assoc _ _ _).symm)))

end Two

theorem preChar_of {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) : PreChar R.toRealDat :=
  ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
    RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩

set_option maxHeartbeats 4000000 in

theorem cpt : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          (∃ φ : Gc B w.px ≃* Gc B' w'.px, ∀ g, HEq (φ g) g) ∧ ∃ pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i), ∀ q, HEq (pt q) q := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ i i' hi
  obtain ⟨h1, -, -, -⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  rcases w' with ⟨px'⟩
  obtain rfl : px' = w.px := eq_of_heq hpx
  obtain rfl : i' = Fin.cast rfl i := Fin.ext hi.symm
  exact ⟨⟨(by with_unfolding_all exact ((MulEquiv.refl (Gc B w.px)) :)), fun g => HEq.rfl⟩, (by with_unfolding_all exact ((id : AutQ (Wc (w.st Z).toD7 i) → AutQ (Wc (w.st Z).toD7 i)) :)), fun q => HEq.rfl⟩

theorem ties_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL)) →
        ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
        (∀ i, OMPins core' R'.toRealDat κ' v₀' O' i) →
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → OmOver (z.geo.O i) (O' i')) →
        z.R.toRealDat.ExAt → z.R.toRealDat.LUnif → R'.toRealDat.ExAt → MWOver z.R.toRealDat R'.toRealDat →
        BarTie fw' ∧ RhoGeo fw' O' ∧ EquivAll core' R'.toRealDat κ' O' ∧ (∀ i, CTie core' R'.toRealDat κ' v₀' O' i) ∧
          ∀ i, R'.toRealDat.LUnif → PhaseTie core' R'.toRealDat κ' v₀' O' (fun _ => 1) i := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hv0 O'
    hOP hOm hEx hLU hEx' hMW
  letI := alg'
  have hz := z.pins.char
  have hpz := preChar_of z.R z.F hz hEx
  have hp' := preChar_of R' _ hPins.char hEx'
  have hio := GlobalTheory.IoExtremal.ioExt _ _ _ _ _ _ z.R.toRealDat hpz.lev hpz.fam hpz.models hpz.thP
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  have key : ∀ i', (O' i').OneMapOf (κ' i') (v₀' i' (sg0 _ _)) (core'.cE ((i' : ℕ) + 1) (O' i').s0) 1 := by
    intro i'
    let i : Fin (w.st Z).toD7.R.m := Fin.cast hm.symm i'
    have hi : (i : ℕ) = i' := rfl
    have h0 := GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.ChartFree.chartIndep _ _ _ _ _ z.core z.R.toRealDat _
      z.geo.κ z.geo.v₀ hpz.lev hz.base.grp hpz.fam hpz.models hpz.thP (GlobalTheory.OneMapRefObj.tieIn_of_fwTie z.geo.fw) hio z.geo.O i
      (z.geo.pins i)
    have h1 := z.geo.phase i hLU h0
    have hc0 := cpt w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ i i' hi
    refine hc0.1.elim fun φ hφ => hc0.2.elim fun pt hpt => ?_
    have hl := UpperTheory.theta_lift_data_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hv0
      i i' hi hMW pt hpt
    have hf := UpperTheory.cusp_sections_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O' i i' hi
      (hOm i i' hi).1 φ hφ pt hpt
    refine hl.elim fun e he => ?_
    have hE' := (EqvMove.equivAll_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O'
      (fun i i' h => (hOm i i' h).1)).2 i i' hi h1.1
    refine oneMapOf_two hp' hPins.char.base.grp.chiW (GlobalTheory.OneMapRefObj.tieIn_of_fwTie fw') (O' i') (hOP i').1 (hOP i').2
      (fun k => fw'.laws.cUnit _ (inR i') _ ((by with_unfolding_all exact (core'.toCore.good_σ₀ :))) k) hE'
      (z.geo.O i) (z.geo.pins i).2 h1 hpz.models.HV hpz.models.jV ((by with_unfolding_all exact (hE.2.2.2 :))) (hOm i i' hi) φ pt e he hf
  exact ⟨barTie_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hMW,
    UpperTheory.geometric_action_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd O'
      (fun i i' h => (hOm i i' h).1),
    (EqvMove.equivAll_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O'
      (fun i i' h => (hOm i i' h).1)).1,
    fun i' _ => ⟨1, key i'⟩, fun i' _ _ => key i'⟩

end UpperTheory.Mem.GeoExt

end
