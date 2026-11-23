import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

section Fields

variable {T : Type} {n : ℕ}

open Classical in

def matDer (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (MvPolynomial (T × Fin n × Fin n) ℂ) (MvPolynomial (T × Fin n × Fin n) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun p =>
    if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0

open Classical in
theorem matDer_X (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) (p : T × Fin n × Fin n) :
    matDer τ X (MvPolynomial.X p) =
      if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem matDer_add (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) : matDer τ (X + Y) = matDer τ X + matDer τ Y := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.add_apply, matDer_X, matDer_X, matDer_X]
  split_ifs
  · simp [mul_add, Finset.sum_add_distrib]
  · simp

theorem matDer_smul (τ : T) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : matDer τ (c • X) = c • matDer τ X := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.smul_apply, matDer_X, matDer_X]
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.C_mul, MvPolynomial.smul_eq_C_mul]; ring
  · simp

theorem matDer_bracket (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ Y⁆ = matDer τ (X * Y - Y * X) := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, matDer_X]
  split_ifs with h
  · simp only [map_sum, Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, zero_add, matDer_X, if_true,
      smul_eq_mul, Finset.sum_mul, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, MvPolynomial.C_mul,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_zero, zero_add]
    refine congrArg₂ (· - ·) ?_ ?_ <;> rw [Finset.sum_comm] <;>
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp

theorem matDer_comm {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ' Y⁆ = 0 := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, Derivation.zero_apply]
  by_cases h1 : p.1 = τ <;> by_cases h2 : p.1 = τ' <;>
    simp [h1, h2, h, Ne.symm h, map_sum, Derivation.leibniz, MvPolynomial.derivation_C, matDer_X]

theorem matDer_commute {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Commute (matDer τ X : Module.End ℂ (MvPolynomial (T × Fin n × Fin n) ℂ)) (matDer τ' Y) := by
  refine LinearMap.ext fun a => ?_
  have := congrArg (fun D : Derivation ℂ _ _ => D a) (matDer_comm h X Y)
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
  exact this

end Fields

section Reps

variable {D : D7}

abbrev PolyE (V : HSp D) : Type := MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ

def realEntries (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
  fun p => infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 p.2.2

def polyFun (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (P : PolyE V) : GA D V → ℂ :=
  fun g => MvPolynomial.eval (realEntries θ V g) P

theorem exists_placeRep (V : HSp D) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V),
    ∀ X : LieAt V τ, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  refine GlobalTheory.EnvelopingExtension.exists_algHom_unitary _ _ _ (fun X : LieAt V τ => (matDer τ X.1 : Module.End ℂ (PolyE V)))
    (fun X Y => LinearMap.ext fun a => ?_) (fun c X => LinearMap.ext fun a => ?_) (fun X Y Z h => LinearMap.ext fun a => ?_)
  · change matDer τ (X.1 + Y.1) a = matDer τ X.1 a + matDer τ Y.1 a
    rw [matDer_add]; rfl
  · have e : ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (c : ℂ) • X.1 := by
      ext i j; simp [Complex.real_smul]
    change matDer τ ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) a = (c : ℂ) • matDer τ X.1 a
    rw [e, matDer_smul]; rfl
  · change matDer τ Z.1 a = matDer τ X.1 (matDer τ Y.1 a) - matDer τ Y.1 (matDer τ X.1 a)
    rw [h, ← matDer_bracket, Derivation.commutator_apply]

def placeRep (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V) := (exists_placeRep V τ).choose

theorem placeRep_ι (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) :=
  (exists_placeRep V τ).choose_spec X

theorem placeRep_tmul (V : HSp D) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) = c • (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul,
    placeRep_ι]

theorem placeRep_comm (V : HSp D) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (x : ℂ ⊗[ℝ] LieAt V τ) (y : ℂ ⊗[ℝ] LieAt V τ') :
    Commute (placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x)) (placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add]; exact hx.add_left hx'
  | tmul c X =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add]; exact hy.add_right hy'
    | tmul c' Y =>
      rw [placeRep_tmul, placeRep_tmul]
      exact ((matDer_commute h X.1 Y.1).smul_left c).smul_right c'

open Classical in

def polyLie (V : HSp D) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (PolyE V) :=
  DirectSum.toLieAlgebra _ (fun τ => (placeRep V τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) * placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) * placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(placeRep_comm V h x y).eq, sub_self]

def polyRep (V : HSp D) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (PolyE V) :=
  UniversalEnvelopingAlgebra.lift ℂ (polyLie V)

open Classical in
theorem polyRep_ι_of (V : HSp D) (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    polyRep V (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x)) =
      placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) := by
  rw [polyRep, UniversalEnvelopingAlgebra.lift_ι_apply, polyLie]
  exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x

end Reps

end GlobalTheory.CentralOps
