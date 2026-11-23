import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

private theorem exEquiv (LL LL' Ks C : Type) [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] (alg' : Algebra Ks LL')
    [AddCommGroup C] [Module Ks C]
    (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) (n n' : ℕ)
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK))
    (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x')
    (e : C ≃ₗ[Ks] WK) :
    ∃ e' : C ≃ₗ[Ks] WK', ∀ (φ : C) (φ' : C), HEq φ' φ → CrdOver ι (e φ).1 (e' φ').1 := by
  have hn : n = n' := (honto 0 WK'.zero_mem).choose_spec.1
  refine ⟨e.trans (GeoFW.baseChangeEquiv ι hι hn WK WK' hmem honto), fun φ φ' h => ?_⟩
  cases h
  exact GeoFW.baseChangeEquiv_crdOver ι hι hn WK WK' hmem honto (e φ)

private theorem moved (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T')
    (hPre : B'.toPre = B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt)
    (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL)
    (halg : ∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ))
    (hH : HEq core'.Q.H z.core.Q.H) (hl : HEq core'.Q.l z.core.Q.l) (hc : HEq core'.Q.c z.core.Q.c)
    (hDw : HEq core'.Q.Dw z.core.Q.Dw) (hXo : HEq core'.Q.Xo z.core.Q.Xo) (hU : HEq core'.U z.core.U)
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y)
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (k' : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1))
    (a1 : HEq k'.aP (z.geo.κ i).aP) (a2 : HEq k'.aM (z.geo.κ i).aM) (a3 : k'.n = (z.geo.κ i).n) (n' : ℕ) :
    letI := alg'; ∀ (WK' : Submodule core'.Q.c.F (Fin n' → (w'.st Z').toD7.what₂.LL)),
      (∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ (z.R.FW i).WK)) →
      (∀ x' ∈ WK', ∃ x : Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL, CrdOver ι x x') →
      ∃ e' : core'.cuspA ((i' : ℕ) + 1) (wtA k') k'.n ≃ₗ[core'.Q.c.F] WK',
        ∀ φ φ', HEq φ' φ → CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' φ' : WK').1 := by
  intro WK' hmem honto
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((@Fin.ext _ i ((i')) ((hii))) : _))
  clear hii
  subst e
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  dsimp only at hH hl hc hDw hXo hU
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
  obtain ⟨aP, aM, hP, hM, nn, hnn⟩ := k'
  dsimp only at a1 a2 a3
  ( (
  have e : @Eq (type_of% (aP)) ((by with_unfolding_all exact (((z.geo.κ i).aP) :))) (aP) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (aP)) (aP) ((((z.geo.κ i).aP))) (((a1)))).symm : _))
  clear (a1)
  subst e))
  ( (
  have e : @Eq (type_of% (aM)) ((by with_unfolding_all exact (((z.geo.κ i).aM) :))) (aM) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (aM)) (aM) ((((z.geo.κ i).aM))) (((a2)))).symm : _))
  clear (a2)
  subst e))
  subst a3
  letI := z.alg
  have halg2 : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) =
      @algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ ((by with_unfolding_all exact (alg' :))) y := fun y =>
    (w'.st Z').toD7.what₂.embLL.injective ((hι _).trans ((by with_unfolding_all exact (((z.alg_eq y).trans ((by with_unfolding_all exact ((halg ((y))).symm : _))) : _ = (w'.st Z').toD7.what₂.embLL (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ ((by with_unfolding_all exact (alg' :))) y)) :))))
  exact (by with_unfolding_all exact ((exEquiv (w.st Z).toD7.what₂.LL (w'.st Z').toD7.what₂.LL z.core.Q.c.F
    (z.core.cuspA ((i : ℕ) + 1) (wtA (z.geo.κ i)) (z.geo.κ i).n) ((by with_unfolding_all exact (alg' :))) ι ((by with_unfolding_all exact (halg2 :))) (z.R.nW i) n'
    (z.R.FW i).WK ((by with_unfolding_all exact (WK' :))) ((by with_unfolding_all exact (hmem :))) ((by with_unfolding_all exact (honto :))) (z.geo.fw.e i)) :))

private theorem exIdx (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T')
    (hPre : B'.toPre = B.toPre) (Z : w.Lt) (Z' : w'.Lt) (i' : Fin (w'.st Z').toD7.R.m) :
    ∃ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i' := by
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  exact (by with_unfolding_all exact ((⟨i', rfl⟩ : ∃ i : Fin (w'.st Z').toD7.R.m, (i : ℕ) = i') :))

theorem UpperTheory.cuspFormCoords_identification_of_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
        B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
        (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
        (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
        (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
        Formalism.L2.Pj.LawsCore core'.toCore →
        letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
          (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
          RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
          ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
          ∃ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι κ' hκ
  have h0 := fun i i' hii => ((hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.1
  have key := fun i i' hii => moved B B' f f' T T' w w' hPre Z hX Wt z Z' core' alg' halg hcore.1 hcore.2.1 hcore.2.2.1
    hcore.2.2.2.1 hcore.2.2.2.2.1 hcore.2.2.2.2.2.1 ι hι i i' hii (κ' i') (hκ i i' hii).1 (hκ i i' hii).2.1 (hκ i i' hii).2.2
    (R'.nW i') (R'.FW i').WK (h0 i i' hii).1 (h0 i i' hii).2
  have hex := exIdx B B' f f' T T' w w' hPre Z Z'
  refine ⟨fun i' => (key _ i' (hex i').choose_spec).choose, fun i i' hii => ?_⟩
  have hi : (hex i').choose = i := Fin.ext ((hex i').choose_spec.trans hii.symm)
  subst hi
  exact (key _ i' (hex i').choose_spec).choose_spec
