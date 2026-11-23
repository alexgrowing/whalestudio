import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasPolChartOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalPolChartsKS
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRescale

open GlobalTheory.PsiWZeroPull (prod_four)

section Geometry

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

abbrev FourGen (L : LB A.left) (f : A ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 4) ![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2])

theorem exists_normalised {L : LB A.left} (hL : L.IsLB) (f : A ⟶ A) [IsMonHom f] (u : FourGen L f) (hu : u.IsGen) :
    ∃ u' : FourGen L f, u'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (eSec A)) (LB.oneGen L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL
    (φ' := (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (prod_four f (1 : A ⟶ A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : A ⟶ A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ (LB.pullGen L _ _ u (1 : A ⟶ A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val hL fun y J hJ => ?_⟩
  have e : eSec A ≫ (1 : A ⟶ A).left = eSec A :=
    congrArg (fun q : 𝟙_ (Over S) ⟶ A => q.left) ((MonObj.comp_one (M := A) η[A]).trans (by simp [Hom.one_def]))
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

end Geometry

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

open DVR (cP cPoint_add)

theorem cPoint_smul (oa : D.OAct O) (w : O) (a : D.X) : cP D (TK R) (w • a) = cP D (TK R) a ≫ oa.onB.act w := by
  rw [cP, cP, oa.c_lin, Category.assoc]

end GlobalTheory.PsiRescale
