import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocIsoConj

open Formalism.UG

theorem conj_unitary {R : Type} [CommRing R] (σ : R →+* R) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) (g : Matrix n n R)
    (hg : cT σ g * J * g = J) : cT σ (a * g * b) * J' * (a * g * b) = J' := by
  calc cT σ (a * g * b) * J' * (a * g * b) = cT σ b * (cT σ g * (cT σ a * J' * a) * g) * b := by
        rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ b * (cT σ a * J' * a) * b := by rw [hJ, hg]
    _ = cT σ (a * b) * J' * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

def conjHom {R : Type} [CommRing R] {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1) :
    Matrix n n R →* Matrix m m R where
  toFun g := a * g * b
  map_one' := by rw [Matrix.mul_one, hab]
  map_mul' g h := by
    calc a * (g * h) * b = a * g * (b * a) * h * b := by rw [hba, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_equiv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) :
    ∃ φ : UJ σ J ≃ₜ* UJ σ J', ∀ g, ((φ g).1 : Matrix m m R) = a * (g.1 : Matrix n n R) * b := by
  have hJ' : cT σ b * J * b = J' := by
    rw [← hJ]
    calc cT σ b * (cT σ a * J' * a) * b = cT σ (a * b) * J' * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hc : ∀ {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] (x : Matrix l k R)
      (y : Matrix k l R), Continuous fun g : Matrix k k R => x * g * y := by
    intro k l _ _ _ _ x y
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let φ₀ : UJ σ J →* GL m R := (Units.map (conjHom a b hab hba)).comp (UJ σ J).subtype
  let ψ₀ : UJ σ J' →* GL n R := (Units.map (conjHom b a hba hab)).comp (UJ σ J').subtype
  have hφU : ∀ g, φ₀ g ∈ UJ σ J' := fun g => conj_unitary σ a b hab J J' hJ _ g.2
  have hψU : ∀ g, ψ₀ g ∈ UJ σ J := fun g => conj_unitary σ b a hba J' J hJ' _ g.2
  let φ : UJ σ J →* UJ σ J' := φ₀.codRestrict _ hφU
  let ψ : UJ σ J' →* UJ σ J := ψ₀.codRestrict _ hψU
  have hφc : Continuous φ :=
    ((Continuous.units_map _ (hc a b)).comp continuous_subtype_val).subtype_mk _
  have hψc : Continuous ψ :=
    ((Continuous.units_map _ (hc b a)).comp continuous_subtype_val).subtype_mk _
  have l : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show b * (a * (g.1 : Matrix n n R) * b) * a = g.1
    calc b * (a * (g.1 : Matrix n n R) * b) * a = (b * a) * (g.1 : Matrix n n R) * (b * a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hba, Matrix.one_mul, Matrix.mul_one]
  have r : ∀ g, φ (ψ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show a * (b * (g.1 : Matrix m m R) * a) * b = g.1
    calc a * (b * (g.1 : Matrix m m R) * a) * b = (a * b) * (g.1 : Matrix m m R) * (a * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Matrix.one_mul, Matrix.mul_one]
  exact ⟨{ toFun := φ, invFun := ψ, left_inv := l, right_inv := r, map_mul' := map_mul φ,
            continuous_toFun := hφc, continuous_invFun := hψc }, fun g => rfl⟩

theorem exists_locIso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  intro F E _ _ _ _ _ σ r r' J J' v a b hab hba hJ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨φ, hφ⟩ := exists_equiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a b hab hba _ _ hJ
  exact ⟨φ, hφ⟩

end GlobalTheory.LocIsoConj
