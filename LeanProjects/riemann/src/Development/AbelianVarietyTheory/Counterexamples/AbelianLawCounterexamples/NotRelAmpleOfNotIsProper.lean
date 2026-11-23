import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTest

theorem linComb_g_eq_one {X Y : Scheme.{0}} {K : Type} [Fintype K] (L : LB X)
    (h : ∀ i j, L.g i j = 1) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j j' : (LB.LinComb L φ ε).ι) : (LB.LinComb L φ ε).g j j' = 1 :=
  Finset.prod_eq_one fun _ _ => by rw [h]; erw [map_one, map_one]; exact one_zpow _

theorem exists_gen_of_g_eq_one {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) :
    ∃ t : LB.Gen L, t.IsGen :=
  ⟨⟨fun _ => 1⟩, fun i j => by rw [h, _root_.one_mul]; dsimp only; rw [map_one, map_one]⟩

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem rigidified_sym_triv : Rigidified A (trivLB A.left) ∧ Out.Sym A (trivLB A.left) :=
  ⟨exists_gen_of_g_eq_one _ (linComb_g_eq_one _ (fun _ _ => rfl) _ _),
    fun _ => ⟨⊤, trivial, exists_gen_of_g_eq_one _ (linComb_g_eq_one _ (fun _ _ => rfl) _ _)⟩⟩

theorem rigidified_sym_noChart :
    Rigidified A ⟨PEmpty, PEmpty.elim, fun i => i.elim⟩ ∧
      Out.Sym A ⟨PEmpty, PEmpty.elim, fun i => i.elim⟩ :=
  ⟨exists_gen_of_g_eq_one _ (linComb_g_eq_one _ (fun i => PEmpty.elim i) _ _),
    fun _ => ⟨⊤, trivial, exists_gen_of_g_eq_one _ (linComb_g_eq_one _ (fun i => PEmpty.elim i) _ _)⟩⟩

theorem exists_polAV_dim_of_isEmpty (S : Scheme.{0}) [IsEmpty S] (n : ℕ) :
    ∃ P : PolAV S, P.g = n := by
  let P := zeroPolAV S
  refine ⟨@PolAV.mk S P.A P.grp P.isAb n ?_ P.L P.isLB P.rigid P.sym P.ample P.ktriv, rfl⟩
  have : IsEmpty P.A.left := ‹IsEmpty S›
  exact ⟨fun x => isEmptyElim x⟩

theorem dim_eq_of_nonempty {S : Scheme.{0}} (s : S) (P : PolAV S) {n : ℕ}
    (h : SmoothOfRelativeDimension n P.A.hom) : P.g = n :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h (eSec P.A s)

end GlobalTheory.PolTest
