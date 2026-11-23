import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.Transl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem lifts (hL : R.toLevCh.Is A.μ0) : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  have h := hL.βW i
  obtain ⟨c, hc⟩ := h
  exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ _ _ _ hc rfl
    (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)

theorem levChi_flag (k : GA D (Wc D i)) : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := Lev.subgroupCharExtension_one_apply _ _
  unfold Lev.levChi levFn
  rw [h2, show (Lev.flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (Lev.flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem hasType (hW : R.models_HW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    Lev.HasType (Wc D i) (R.βW i) (Lev.flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := (hW i σ).2.1.le (LinearMap.mem_range_self _ y)
  exact fun κ hκ h => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hm).lev v κ hκ h

theorem transl (hW : R.models_HW) (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (g : G) (k : GA D (Wc D i))
    (hk : IsLiftW R i g k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) (h : GA D (Wc D i)) :
    (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k) := by
  have h1 := Lev.level_action_spec (hasType R i hW σ y v) ⟨k, hk⟩ k hk h
  have h2 : (R.HW i σ).e (R.gW i σ g y) v h =
      Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e y v) h :=
    congrArg (fun U : MMap (R.MW i σ) => U v h) (hg i σ g y)
  refine h2.trans (h1.trans ?_)
  rw [levChi_flag, inv_one, one_mul]

theorem sum_apply_eq {G X Y : Type} [Fintype G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ev : X →ₗ[ℂ] Y) (c : G → ℂ) (a : G → Y →ₗ[ℂ] Y) (b : G → X) (y : Y) (h : ∀ g, ev (b g) = a g y) :
    (∑ g, c g • a g) y = ev (∑ g, c g • b g) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]

theorem proj (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v :=
  sum_apply_eq
    (({ toFun := fun U => U v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      MMap (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)) ∘ₗ (R.HW i σ).e)
    (RealDat.eC (A := A) σ) (fun g => actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (fun g => R.gW i σ g y)
    ((R.HW i σ).e y v) fun g => congrArg (fun U : MMap (R.MW i σ) => U v) (hg i σ g y)

end GlobalTheory.GalLift.Transl

namespace GlobalTheory.GalLift

theorem act_eq_translation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i
  exact ⟨fun g => Transl.lifts R i hC.lev (R.eG g), fun σ =>
    ⟨Transl.transl R i hC.models.HW hC.models.gW σ, Transl.proj R i hC.models.gW σ⟩⟩

end GlobalTheory.GalLift

end
