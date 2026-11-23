import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MemBlockTriangularTwoBlockSizesOfLe

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem flag_character_eq_principal (t : T) (k : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) k := by
  unfold levChi
  congr 1
  have e1 : levFn (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k) =
      levFn (R.βY 0) (withP (R.datYt t 0 R.triv) (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ))
        (finE (Yc D 0) k) := rfl
  rw [e1, levFn_withP]
  rw [show ext1 (LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).H
      (⇑(LevelP.triv (R.datYt t 0 R.triv).Pg (R.datYt t 0 R.triv).r ℂ).chi)
      (rTup (R.βY 0) (R.datYt t 0 R.triv) (finE (Yc D 0) k)) = 1 from subgroupCharExtension_one_apply _ _, one_mul, levFn_flag1]
  unfold LevCh.datYt LevCh.dat0
  exact levFn_datY_noQ rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Frm.B _

end Formalism.IndefR.Eqv.Act

end
