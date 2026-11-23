import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMapStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem pt_zero {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_nsmul {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ∀ N : ℕ, M.pt (N • e) = M.pt e ^ N
  | 0 => by rw [zero_smul, pt_zero, pow_zero]
  | N + 1 => by rw [succ_nsmul, M.add, pt_nsmul M e N, pow_succ]

theorem comp_pow' {X A : Over S} [GrpObj A] (x : X ⟶ A) (g : A ⟶ A) : ∀ N : ℕ, x ≫ g ^ N = (x ≫ g) ^ N
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | N + 1 => by rw [pow_succ, pow_succ, comp_mul, comp_pow' x g N]

def castM {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : LieModel G x' E := h ▸ M

theorem castM_left {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S} (h : x = x') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (e : E) : ((castM h M).pt e).left = (M.pt e).left := by
  subst h; rfl

def toAt {A : Over (Sp R)} (v : epsR R ⟶ A) : epsAt (𝟙 (Sp R)) ⟶ A :=
  Over.homMk v.left (by simp [Over.w v])

theorem toAt_left {A : Over (Sp R)} (v : epsR R ⟶ A) : (toAt v).left = v.left := rfl

theorem toAt_tan {A : Over (Sp R)} [GrpObj A] (v : epsR R ⟶ A) (hv : IsTangent v) : IsTanAt A (𝟙 (Sp R)) (toAt v) := by
  unfold IsTanAt
  rw [toAt_left]
  unfold IsTangent at hv
  rw [hv]
  first
  | (rw [Hom.one_def]; simp)
  | simp [Hom.one_def]
  | (rw [Hom.one_def, Over.comp_left]; congr 1; simp)
  | rfl

end PositivityTheory.Xgf.isogeny_decomposition_product

end
