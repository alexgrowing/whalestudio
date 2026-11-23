import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

private theorem UpperTheory.omega_lowering_action {D : D7} {G : Type} [iG : Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F)
    {G' : Type} [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G' → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La} (hlev : HEq lev O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (z' : G') (hz : HEq z' z) {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (q q' : AutQ (Wc D i)) (hq : HEq q q') :
    (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) a' : ℂ) * (cc (O.dict q'.out).1 * (O.mu q'.out * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z' (GlobalTheory.FieldBC.rulBC hle f)) (O.dict q'.out).1 (O.dict q'.out).2)) =
      (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out := by
  subst hG ha
  cases hi; cases hz; cases hq
  exact congrArg _ (adOver_rulBC O hact c hle h₃ (eq_of_heq hlev) cc _ hf _)

open Classical in
private theorem UpperTheory.weight_function_eq {D : D7} {j : ℕ} (b : WeightFamilies.Wt D j) (aP : type_of% b.aP) (aM : type_of% b.aM) (hP : HEq aP b.aP)
    (hM : HEq aM b.aM) :
    (fun x : (D.host.E →+* ℂ) × ℕ => ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t then ext0 (aP t) x.2 else 0) +
      if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) then ext0 (aM t) x.2 else 0)) = wtA b := by
  cases hP; cases hM; rfl

private theorem UpperTheory.base_change_mem_section {D : D7} {C : Formalism.L2.Pj.Core D} {j : ℕ} {c c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l} (hle : c.F ≤ c'.F)
    {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n : ℕ} {f : Rul (C.Q.Xo j) c} (hf : f ∈ sec (C.Q.Xo j) c a n) :
    GlobalTheory.FieldBC.rulBC hle f ∈ sec (C.Q.Xo j) c' a' n := ha ▸ GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf

theorem UpperTheory.cusp_sections_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
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
            ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
            ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev →
              ∀ (φ : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (φ g) g) →
            ∀ (pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i)), (∀ q, HEq (pt q) q) →
                ∀ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff z.core.Q.l) (hle : (z.geo.O i).c'.F ≤ c.F), HEq (O' i').c' c →
                  ∀ f ∈ sec (z.core.Q.Xo ((i : ℕ) + 1)) (z.geo.O i).c' (wtA (z.geo.κ i)) (Vc (w.st Z).toD7 i).rank,
                    ∃ f' ∈ sec (core'.Q.Xo ((i' : ℕ) + 1)) (O' i').c' (wtA (κ' i')) (Vc (w'.st Z').toD7 i').rank,
                      HEq f' (GlobalTheory.FieldBC.rulBC hle f) ∧ ∀ g q,
                      (lieFac (core'.Q.Dw ((i' : ℕ) + 1)) (xiR (w'.st Z').toD7) (wtA (κ' i')) : ℂ) *
                        adOver (O' i') (core'.cE ((i' : ℕ) + 1) (O' i').s0) (actLev (O' i').c' (O' i').lev2 (φ g) f') q.out =
                      (lieFac (z.core.Q.Dw ((i : ℕ) + 1)) (xiR (w.st Z).toD7) (wtA (z.geo.κ i)) : ℂ) *
                        adOver (z.geo.O i) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) (actLev (z.geo.O i).c' (z.geo.O i).lev2 g f)
                          (pt q).out := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ O' i i' hii hlev φ hφ pt hpt c hle hcc f₀ hf₀
  have hk := hκ i i' hii
  have a1 := hk.1
  have a2 := hk.2.1
  have a3 := hk.2.2
  clear hk hκ
  obtain ⟨h1, -, -, -⟩ := hE
  clear hP hRS halg'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, hV, hdict, hmu, -, hcE, -, -, -⟩ := hcore
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((z.core.Q.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((z.core.Q.H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((z.core.Q.l) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((z.core.Q.l))) (((hl)))).symm : _))
  clear (hl)
  subst e))
  ( (
  have e : @Eq (type_of% (c')) ((by with_unfolding_all exact ((z.core.Q.c) :))) (c') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (c')) (c') (((z.core.Q.c))) (((hc)))).symm : _))
  clear (hc)
  subst e))
  ( (
  have e : @Eq (type_of% (Dw')) ((by with_unfolding_all exact ((z.core.Q.Dw) :))) (Dw') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Dw')) (Dw') (((z.core.Q.Dw))) (((hDw)))).symm : _))
  clear (hDw)
  subst e))
  ( (
  have e : @Eq (type_of% (Xo')) ((by with_unfolding_all exact ((z.core.Q.Xo) :))) (Xo') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Xo')) (Xo') (((z.core.Q.Xo))) (((hXo)))).symm : _))
  clear (hXo)
  subst e))
  ( (
  have e : @Eq (type_of% (U')) ((by with_unfolding_all exact ((z.core.U) :))) (U') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (U')) (U') (((z.core.U))) (((hU)))).symm : _))
  clear (hU)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((z.core.V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((z.core.V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  ( (
  have e : @Eq (type_of% (dict')) ((by with_unfolding_all exact ((z.core.dict) :))) (dict') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (dict')) (dict') (((z.core.dict))) (((hdict)))).symm : _))
  clear (hdict)
  subst e))
  ( (
  have e : @Eq (type_of% (mu')) ((by with_unfolding_all exact ((z.core.mu) :))) (mu') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (mu')) (mu') (((z.core.mu))) (((hmu)))).symm : _))
  clear (hmu)
  subst e))
  ( (
  have e : @Eq (type_of% (cE')) ((by with_unfolding_all exact ((z.core.cE) :))) (cE') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (cE')) (cE') (((z.core.cE))) (((hcE)))).symm : _))
  clear (hcE)
  subst e))
  have ei : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((@Fin.ext (w'.st Z').toD7.R.m ((i)) i' ((hii))) : _))
  subst ei
  have ha : @Eq (type_of% (wtA (z.geo.κ i))) ((by with_unfolding_all exact ((wtA (κ' ((i)))) : _))) (wtA (z.geo.κ i)) := (by with_unfolding_all exact ((UpperTheory.weight_function_eq (z.geo.κ i) ((by with_unfolding_all exact ((κ' ((i))).aP : _))) ((by with_unfolding_all exact ((κ' ((i))).aM : _))) ((by with_unfolding_all exact (a1 :))) ((by with_unfolding_all exact (a2 :)))) :))
  letI := z.alg
  have hm := UpperTheory.base_change_mem_section (C := z.core.toCore) hle ha hf₀
  have key := fun (g : Gc B w.px) (q : AutQ (Wc (w'.st Z').toD7 ((by with_unfolding_all exact (i :))))) =>
    UpperTheory.omega_lowering_action (z.geo.O i) (z.geo.pins i).2.act.1 c hle (le_trans (z.geo.O i).hle hle) hG hi (lev := (by with_unfolding_all exact ((O' ((i))).lev : _)))
      ((by with_unfolding_all exact (hlev :))) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) g ((by with_unfolding_all exact ((φ g) :))) ((by with_unfolding_all exact ((hφ g) :))) ha hf₀ ((by with_unfolding_all exact ((pt ((q))) : _))) ((by with_unfolding_all exact (q :))) ((by with_unfolding_all exact ((hpt ((q))) : _)))
  have hr : HEq (GlobalTheory.FieldBC.rulBC hle f₀) (GlobalTheory.FieldBC.rulBC hle f₀) := HEq.rfl
  let F1 := GlobalTheory.FieldBC.rulBC hle f₀
  ( (
  have e : @Eq (type_of% (c)) ((by with_unfolding_all exact (((O' ((by with_unfolding_all exact (i :)))).c') :))) (c) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (c)) ((((O' ((by with_unfolding_all exact (i :)))).c'))) (c) (((hcc)))) : _))
  clear (hcc)
  subst e))
  exact ⟨(by with_unfolding_all exact (F1 :)), (by with_unfolding_all exact (hm :)), (by with_unfolding_all exact (hr :)), (by with_unfolding_all exact (key :))⟩
