import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lift_mem_levVP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P g0 κ hκ
  obtain ⟨hG, hpar, hr⟩ := hκ
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) = g0.1 := hr
  have hmem : finE (Vc D i) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (RecTie.datVP R i t P) := by
    refine ⟨hpar, ?_⟩
    rw [hrt]; exact g0.2
  refine ⟨⟨hG, hmem⟩, ?_⟩
  have e1 : Formalism.L2.DIV.ext1 (RecTie.datVP R i t P).P.H (RecTie.datVP R i t P).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ)) = (P.chi g0)⁻¹ := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ hmem.2]
    simp only [hrt]
    rfl
  have e2 : Formalism.L2.DIV.ext1 (flagL (R.datVt i t)).P.H (flagL (R.datVt i t)).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ)) = 1 := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ (show Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) ∈ (flagL (R.datVt i t)).P.H from Subgroup.mem_top _)]
    rfl
  have key : Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) =
      (P.chi g0)⁻¹ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) := by
    unfold Formalism.L2.DIV.levFn
    rw [e1, e2, one_mul, mul_assoc]
    rfl
  show ((Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) : ℂˣ) : ℂ) = _
  rw [key, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory
