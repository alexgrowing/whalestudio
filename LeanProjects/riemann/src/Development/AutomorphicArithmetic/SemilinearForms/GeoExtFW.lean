import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsJEnl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiROfEnlarged
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreBaseFramesEqModelFramesEnlargedCoefficientBa
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseReadingZeroWithoutEvaluationProperty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KapMoved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsFormBaseChangeCrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapEqOtoLLEOOfPin
import Development.AutomorphicArithmetic.UnitTensorPairings.ExtVecPairingIndepOfBaseSamePre
import Development.AutomorphicArithmetic.UnitTensorPairings.CuspEvalPropertyIndepOfBaseSamePre
import Development.AutomorphicArithmetic.UnitTensorPairings.LocalCuspNormsIndepOfBaseSamePre
import Development.AutomorphicArithmetic.UnitTensorPairings.CuspCoreDatumTransportOfSamePre
import Development.AutomorphicArithmetic.UnitTensorPairings.CuspFormCoordsIdentificationOfSamePre
import Development.AutomorphicArithmetic.UnitTensorPairings.PointEquivFamilyTransportOfSamePre

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

namespace UpperTheory.Mem.GeoExt

section Set

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}

def setMu0 {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (m : ℕ → ((AE D)ˣ →* Circle)) :
    RealDat3 D A3 Ks :=
  { R with mu0 := m }

def fwBack {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (m : ℕ → ((AE D)ˣ →* Circle))
    (h : ∀ i : Fin D.R.m, m ((i : ℕ) + 1) = R.mu0 ((i : ℕ) + 1)) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T (setMu0 R m).toRealDat κ v₀) :
    FWTie T R.toRealDat κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := fun i σ hg => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := t.chiR i σ hg
    refine ⟨a1, a2, a3, fun x hx => ?_, fun hσ => (a5 hσ).trans (h i)⟩
    obtain ⟨y, hy1, hy2⟩ := a4 x hx
    exact ⟨y, by rw [← h i]; exact hy1, hy2⟩
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev

end Set

theorem exists_kap : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
      ∃ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  refine ⟨fun i =>
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :))
      aM := (by with_unfolding_all exact ((z.geo.κ i).aM :))
      aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :))
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :))
      n := (z.geo.κ i).n
      n_even := (z.geo.κ i).n_even }, fun i i' hi => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  exact ⟨(by with_unfolding_all exact ((HEq.refl (z.geo.κ i).aP) :)), (by with_unfolding_all exact ((HEq.refl (z.geo.κ i).aM) :)), rfl⟩

theorem exists_fw_mu : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
      ∃ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
        (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
          HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (fw'.e i' φ' : (R'.FW i').WK).1) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
  letI := alg'
  obtain ⟨κ', hκ⟩ := exists_kap B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
  obtain ⟨v₀', hv⟩ := UpperTheory.cuspCoreDatum_transport_of_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
  obtain ⟨e', he⟩ := UpperTheory.cuspFormCoords_identification_of_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ
  obtain ⟨pt', hpt⟩ := UpperTheory.pointEquiv_family_transport_of_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
  exact ⟨κ', v₀',
    { alg_eq := GlobalTheory.Mem.R3.Rw.algebraMap_eq_OtoLL_eO_of_pin B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
      e := e'
      ks := GlobalTheory.ksForm_moved B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
      kap := GlobalTheory.FWKapMove.kap_moved B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ
      pt := pt'
      nrm_eq := UpperTheory.localCuspNorms_indep_of_base_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ e' he pt' hpt
      laws := GlobalTheory.Mem.R3.Ext.lawsJ_enl B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
      chiR := GlobalTheory.Mem.R3.Rw.chiR_of_enlarged B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
      hv₀ := UpperTheory.extVecPairing_indep_of_base_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι v₀' hv
      x0 := GlobalTheory.Mem.R3.Rw.FwBase.coreBaseFrames_eq_modelFrames_enlargedCoefficientBase B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι
      ev0 := GlobalTheory.Mem.R3.Rw.EvZero.enlargedBase_reading_zero_without_evaluationProperty B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ v₀' hv e' he
      ev := UpperTheory.cuspEvalProperty_indep_of_base_same_pre B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hmu ι hι κ' hκ v₀' hv e' he }, hκ, hv, he⟩

theorem exists_reference_characters_over_extension {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    (m : ℕ → ((AE a.D)ˣ →* Circle)) : ∃ m' : ℕ → ((AE a'.D)ˣ →* Circle), HEq m' m ∧ ∀ j, HEq (m' j) (m j) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact ⟨(by with_unfolding_all exact (m :)), (by with_unfolding_all exact ((HEq.refl m) :)), fun j => (by with_unfolding_all exact ((HEq.refl (m j)) :))⟩

theorem exists_fw : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
      RSideW z Wt' R' → HEq f' f → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∃ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
        (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
          HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (fw'.e i' φ' : (R'.FW i').WK).1) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hRS hf hL' ι hι
  letI := alg'
  obtain ⟨m, hm, hm'⟩ := exists_reference_characters_over_extension (a := Z) (a' := Z') hPre z.R.toLevCh.mu0
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact LevExt.hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hPre hf h
  have hm0 : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  have h : ∀ i' : Fin (w'.st Z').toD7.R.m, m ((i' : ℕ) + 1) = R'.mu0 ((i' : ℕ) + 1) := fun i' =>
    eq_of_heq ((hm' _).trans (LevExt.idc_heq (a := Z) (a' := Z') hPre (hmu0 ⟨i'.1, hm0 ▸ i'.2⟩ i' rfl)
      (z.lev.is.mu0 ⟨i'.1, hm0 ▸ i'.2⟩) (hL'.is.mu0 i')).symm)
  obtain ⟨κ', v₀', fw', h1, h2, h3⟩ := exists_fw_mu B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr
    (setMu0 R' m) ((by with_unfolding_all exact (hRS :))) hm ι hι
  exact ⟨κ', v₀', fwBack R' m h fw', h1, h2, (by with_unfolding_all exact (h3 :))⟩

end UpperTheory.Mem.GeoExt

end
