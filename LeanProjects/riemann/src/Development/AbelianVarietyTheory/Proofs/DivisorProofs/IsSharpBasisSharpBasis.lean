import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
  (sharpReindex h).trans
    { twistSnd (e8 W).adjugate with
      invFun := twistSnd (e8 W)
      left_inv := twistSnd_twistSnd _ _ (by rw [Matrix.mul_adjugate, hW, one_smul])
      right_inv := twistSnd_twistSnd _ _ (by rw [Matrix.adjugate_mul, hW, one_smul]) }

theorem isSharpBasis_sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    IsSharpBasis W (sharpBasis W hW h) := by
  intro i j
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd (e8 W) _ (by simp [e8, Matrix.transpose_add, add_comm])
    (by rw [Matrix.mul_adjugate, hW, one_smul]) _ _

def labMat (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2) :
    Matrix (Fin (2 * (8 * h))) (Fin (2 * (8 * h))) ℤ :=
  fun i' i => (sharpBasis W hW h).symm
    (fun u c => ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c) i'

variable {S : Scheme.{0}}

def ptOf {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) : T ⟶ A :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose

theorem ptOf_pr {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) (u : Fin 8) :
    ptOf hP b x ≫ pr u = ∏ c, b c ^ x u c :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose_spec u

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
