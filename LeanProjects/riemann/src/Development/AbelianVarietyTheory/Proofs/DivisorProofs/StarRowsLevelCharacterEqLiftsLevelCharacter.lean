import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ChiStarLev

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag' (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP' (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag' (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

end Level

theorem ext_by_one_apply_of_not_mem_subgroup {G N : Type} [Group G] [One N] [Mul N] {P : Subgroup G} (f : P → N) {x : G} (h : x ∉ P) :
    ext1 P f x = 1 := by
  unfold ext1; rw [dif_neg h]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem star_levChi_levR (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)) :
    star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  have hsg : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  rw [hsg]
  have h1 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) g
  have h2 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) g
  have hH : (R.levL F b D.what₂.embLL).H = (R.levR F b).H := rfl
  by_cases hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∈ (R.levR F b).H
  · replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
      exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
    have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
      have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
      exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
    rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
    rfl
  · have hm' : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∉ (R.levL F b D.what₂.embLL).H := hm
    replace h2 := h2.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm'))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    simp

end GlobalTheory.ChiStarLev
