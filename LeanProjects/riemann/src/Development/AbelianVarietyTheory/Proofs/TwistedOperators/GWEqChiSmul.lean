import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormEigenW

theorem gW_eq_chi_smul : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (w : (R.HW i σ).H), (R.HW i σ).e w ∈ Mult R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) → ∀ g0 : P.H, R.gW i σ (R.eG.symm g0.1) w = ((P.chi g0 : ℂˣ) : ℂ) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hLev hMod i σ P w hX g0
  apply (hMod.HW i σ).1
  have hg : (R.HW i σ).e (R.gW i σ (R.eG.symm g0.1) w) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0.1))) ((R.HW i σ).e w) :=
    hMod.gW i σ (R.eG.symm g0.1) w
  rw [hg, R.eG.apply_symm_apply, LinearMap.map_smul]
  have hM : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      ((R.HW i σ).e w) := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hX
  obtain ⟨κ', hκ'⟩ := (GlobalTheory.StepLifts.lifts_exist R hLev i).2 g0.1

  have hmem : κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) := ⟨hκ'.1, hκ'.2.1, by
    show rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) κ') ∈ P.H
    rw [hκ'.2.2]; exact g0.2⟩
  have hchi : levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
    have hr : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') = g0.1 := hκ'.2.2
    have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
        (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi g0 := by
      have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := by rw [hr]; exact g0.2
      have h3 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
          (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
      rw [h3]
      exact congrArg _ (Subtype.ext hr)
    unfold levChi levFn
    rw [h2]
    have hs : (R.datWp i P).s = 0 := rfl
    have hQ : (R.datWp i P).Q = ∅ := rfl
    rw [hs, hQ]
    simp
  ext v h
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 ((R.HW i σ).e w v) h =
    ((P.chi g0 : ℂˣ) : ℂ) * (R.HW i σ).e w v h
  have hT : HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e w v) := by
    intro κ hκ h'
    have hle := GlobalTheory.GoodProjLevel.mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) P hκ
    have h1 : (R.HW i σ).e w v (h' * κ) = levChi (Wc D i) (R.βW i) (R.datWp i P) κ * (R.HW i σ).e w v h' :=
      hM.lev v κ hle.1 h'
    rw [h1]
    exact congrArg (· * (R.HW i σ).e w v h') hle.2
  have hA := level_action_spec hT ⟨κ', hκ'⟩ κ' hκ' h
  rw [hA, GlobalTheory.ThetaShiftSmooth.levChi_flag_eq_one R i κ', inv_one, one_mul,
    hM.lev v κ' hmem h, hchi]

end GlobalTheory.FormEigenW
