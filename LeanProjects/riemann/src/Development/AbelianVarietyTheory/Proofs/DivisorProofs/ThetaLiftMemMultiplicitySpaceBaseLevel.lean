import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfMemLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectorsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLevelP

set_option maxHeartbeats 1000000 in

theorem thF_mem_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hIs : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hTh : R.IsThP) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (y : (R.HV i t).H)
    (hy : R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P))) :
    R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj)) := by
  have hW := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hTh.thF_mem i t y)
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2 ⟨hW.aut, hW.cusp, fun v k' hk' g => ?_, hW.equiv, hW.cont⟩
  obtain ⟨g0, hl', hc'⟩ := GlobalTheory.LevelRankR.exists_lift_of_mem_level R i P.conj k' hk'
  have hL := (GlobalTheory.StepLifts.lifts_exist R hIs i).1 t
  have hx := hL g0
  clear hL
  rcases hx with ⟨κ, hl⟩
  have h1 := GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter R i t P
  let g1 : P.H := ⟨g0.1, g0.2⟩
  have h3 := h1 g1 κ hl
  clear h1
  have hf0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := Units.ne_zero _
  have hy' : ∀ k ∈ levS (Vc D i) (R.βV i) (RecTie.datVP R i t P), ∀ h,
      R.extV i t y (h * k) = levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) k • R.extV i t y h := hy
  have e1 := hy' κ h3.1
  have e2 := h3.2
  clear hy' hy h3
  have hnum : (((P.chi g1 : ℂˣ) : ℂ))⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
      levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ := by
    rw [e2]
    field_simp
  have hsh : ∀ h, R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
    intro h
    have e3 : R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ • R.extV i t y h :=
      congrFun ((R.extV i t).map_smul _ y) h
    refine e3.trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) (e1 h).symm)
    refine (congrArg (fun a : ℂ => a • R.extV i t y h) hnum).trans ?_
    exact mul_smul _ _ _
  have key := GlobalTheory.T.thetaLift_intertwines_lifts_smoothVectors R hIs hMod hTh i t g0.1 κ k' hl hl' y _ hsh v g
  have hcc : levChi (Wc D i) (R.βW i) (R.datWp i P.conj) k' = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ := by
    rw [hc']
    change (((P.chi⁻¹) g1 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e4 : R.thF i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) v g = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ * R.thF i t y v g := by
    have e5 := congrFun (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) ((R.thF i t).map_smul (((P.chi g1 : ℂˣ) : ℂ))⁻¹ y)) g
    exact e5
  exact key.symm.trans (e4.trans (congrArg (· * R.thF i t y v g) hcc.symm))

set_option maxHeartbeats 1000000 in

theorem thF_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs hMod hTh hv b i t y hy
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R F b hv]
  exact thF_mem_conj R hIs hMod hTh i t (R.levR F b) y hy

end GlobalTheory.ThetaLevelP
