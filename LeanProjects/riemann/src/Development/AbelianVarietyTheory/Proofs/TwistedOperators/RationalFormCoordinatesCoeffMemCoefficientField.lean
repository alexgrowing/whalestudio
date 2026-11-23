import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem typeX_mem (R : RealDat D A Ks) (t : T) (M : Subfield ℂ)
    (hχ : ∀ i : Fin D.R.m, ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ M)
    (hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ M) (k) :
    (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) ∈ M := by
  show levFn R.βX (Lev.flag1L (R.datXt t)) _ ∈ GlobalTheory.RationalValues.unitsIn M
  unfold levFn
  refine mul_mem (mul_mem ?_ (prod_mem fun PP hPP => prod_mem fun c hc => ?_)) (prod_mem fun PP hPP => ?_)
  · have h1 : ∀ x, ext1 (Lev.flag1L (R.datXt t)).P.H (Lev.flag1L (R.datXt t)).P.chi x = 1 := fun x => Lev.subgroupCharExtension_one_apply _ x
    rw [h1]
    exact one_mem _
  · have hc' : c < D.R.m := Finset.mem_range.1 hc
    exact show R.chi ((⟨c, hc'⟩ : Fin D.R.m) + 1 : ℕ) PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hχ ⟨c, hc'⟩ PP hPP _
  · exact inv_mem (show R.xiR t PP _ ∈ GlobalTheory.RationalValues.unitsIn M from hξ PP hPP _)

end GlobalTheory.FormCoef

namespace GlobalTheory.FormCoef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000 in

theorem coeff_formC_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A),
    HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m,
      MvPolynomial.coeff m (ch.S.formC t (R.jX t x) y).1 ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F hS _ _ t x y m
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  obtain ⟨k, v, hv⟩ := GlobalTheory.RationalValues.exists_ext_eq (R.B.R t).pres c₀ (GlobalTheory.RationalValues.coef_mem (hT.coefR t))
    (GlobalTheory.RationalValues.rho_mem hT.mapR) x (toXf y)
  have h0 : (R.HX t).e (R.jX t x) (toXf y) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ k : ℂˣ) : ℂ) • c₀ v :=
    (congrFun (hc.models.jX t x) (toXf y)).trans hv
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) k
  have h1 : ch.S.formC t (R.jX t x) y = ch.S.co (c₀ (a • v)) := by
    rw [SumChoice.formC, h0, map_smulₛₗ, ha]
  rw [h1, hco, ← MvPolynomial.map_rename, MvPolynomial.coeff_map]
  exact ⟨_, rfl⟩

end GlobalTheory.FormCoef
