import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

attribute [local instance] cotOp cotCentral cotTower

theorem cotSnd_cotPt_eq_dUnit (R : Type) [CommRing R] (D : Type) [CommRing D] [Bialgebra R D] (z : D) :
    cotSnd R D (cotPt R D z) = dUnit R z := by
  change TrivSqZeroExt.snd (algebraMap R (TrivSqZeroExt R (Cot R D)) (Coalgebra.counit z) +
    TrivSqZeroExt.inr (AugCot.d (Bialgebra.counitAlgHom R D) z)) = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

theorem crystallineCocycleCotangentValue_sub_of_coboundary : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D) (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _))), d0 _ k = f.1 - f'.1 → cotVal f y - cotVal f' y = dUnit R (show D from k (trivAt y)) := by
  intro R _ X D _ _ y f f' k h
  have hf : f - f' = ⟨d0 _ k, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ k⟩ := Subtype.ext h.symm
  let y' : Pt X (cotExt R D).C := spOver (cotPt R D) ≫ y
  have h1 : (cotExt R D).val y'.left y'.w f - (cotExt R D).val y'.left y'.w f' =
      (k (trivAt y') : (cotExt R D).C) -
        (cotExt R D).i (k (Thick.triv (cotExt R D).B _ ((cotExt R D).red_w y'.w))) := by
    rw [← map_sub, hf]
    exact SqExt.tangentValue_coboundary _ _ _ k
  have h2 : fv f D (cotExt R D).C (cotPt R D) y - fv f' D (cotExt R D).C (cotPt R D) y =
      (show (cotExt R D).C from k (trivAt y')) - cotPt R D (show D from k (trivAt y)) :=
    (congrFun (congrFun (congrFun h _) _) (trivMap (cotPt R D) y)).symm
  have key : ∀ a a' b b' c i p : (cotExt R D).C, a - a' = c - i → b - b' = c - p →
      (a - b) - (a' - b') = p - i := fun a a' b b' c i p e1 e2 ↦ by linear_combination e1 - e2
  have h3 := congrArg (cotSnd R D) (key _ _ _ _ _ _ _ h1 h2)
  rw [map_sub, map_sub (cotSnd R D) (cotPt R D _), cotSnd_cotPt_eq_dUnit] at h3
  exact h3.trans (sub_zero _)

end GlobalTheory.PtExt
