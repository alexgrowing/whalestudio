import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

abbrev SymUnit (r : ℕ) : Type :=
  {b : (Matrix (Fin r) (Fin r) ℤ)ˣ // (b : Matrix (Fin r) (Fin r) ℤ).transpose = b}

def TensO {r : ℕ} (_ : SymUnit r) : Type := Matrix (Fin r) (Fin r) ℤ

namespace TensO

variable {r : ℕ} (s : SymUnit r)

instance : Ring (TensO s) := inferInstanceAs (Ring (Matrix (Fin r) (Fin r) ℤ))

def mat (a : TensO s) : Matrix (Fin r) (Fin r) ℤ := a

def ofMat (a : Matrix (Fin r) (Fin r) ℤ) : TensO s := a

theorem inv_transpose : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose =
    ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) := by
  have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.inv_mul s.1
  have h2 : (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = 1 :=
    Units.mul_inv s.1
  have h3 := congrArg Matrix.transpose h1
  rw [Matrix.transpose_mul, s.2, Matrix.transpose_one] at h3
  calc _ = (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
        ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

instance : StarRing (TensO s) where
  star a := ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
    (s.1 : Matrix (Fin r) (Fin r) ℤ)
  star_involutive a := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) = a
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, s.2, inv_transpose]
    have h1 : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (s.1 : Matrix (Fin r) (Fin r) ℤ) = 1 :=
      Units.inv_mul s.1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rfl
  star_mul a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a * mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) =
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ)) *
      (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ))
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.one_mul]
  star_add a b := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (mat s a + mat s b).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
    rfl

theorem star_def (a : TensO s) : star a = ofMat s (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (mat s a).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ)) := rfl

@[simp] theorem mat_mul (a b : TensO s) : mat s (a * b) = mat s a * mat s b := rfl
@[simp] theorem mat_add (a b : TensO s) : mat s (a + b) = mat s a + mat s b := rfl
@[simp] theorem mat_one : mat s (1 : TensO s) = 1 := rfl

end TensO

def symUnitOf {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det) : SymUnit r :=
  ⟨((Matrix.isUnit_iff_isUnit_det _).2 h).unit, by
    show (W + W.transpose).transpose = W + W.transpose
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]⟩

end GlobalTheory.Mum

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def Tens.smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) : D'.X :=
  T.xe.symm (fun i => ∑ j, TensO.mat s a i j • T.xe z j)

theorem Tens.xe_smulF (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    T.xe (T.smulF s a z) i = ∑ j, TensO.mat s a i j • T.xe z j := by
  simp [Tens.smulF]

def Tens.mod (T : Tens D D' W) (s : SymUnit r) : Module (TensO s) D'.X where
  smul := T.smulF s
  one_smul z := by
    show T.smulF s 1 z = z
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF]
    simp [TensO.mat_one, Matrix.one_apply, ite_smul]
  mul_smul a b z := by
    show T.smulF s (a * b) z = T.smulF s a (T.smulF s b z)
    apply T.xe.injective
    funext i
    simp only [Tens.xe_smulF, TensO.mat_mul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  smul_zero a := by
    show T.smulF s a 0 = 0
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF]
  smul_add a z z' := by
    show T.smulF s a (z + z') = T.smulF s a z + T.smulF s a z'
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF, smul_add, Finset.sum_add_distrib]
  add_smul a b z := by
    show T.smulF s (a + b) z = T.smulF s a z + T.smulF s b z
    apply T.xe.injective
    funext i
    simp [Tens.xe_smulF, add_smul, Finset.sum_add_distrib]
  zero_smul z := by
    show T.smulF s 0 z = 0
    apply T.xe.injective
    funext i
    rw [Tens.xe_smulF, map_zero]
    exact Finset.sum_eq_zero fun j _ => by
      show (0 : Matrix (Fin r) (Fin r) ℤ) i j • T.xe z j = 0
      simp

theorem Tens.xe_smul (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (z : D'.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • z) i = ∑ j, TensO.mat s a i j • T.xe z j :=
  T.xe_smulF s a z i

def Tens.act (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : D'.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D'.P.A fun i => ∏ j, T.pr j ^ a i j)

theorem Tens.act_pr (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    T.act a ≫ T.pr i = ∏ j, T.pr j ^ a i j :=
  T.lim.fac _ ⟨i⟩

def Tens.inc (T : Tens D D' W) (i₀ : Fin r) : D.P.A ⟶ D'.P.A :=
  T.lim.lift (Fan.mk D.P.A fun i => if i = i₀ then 𝟙 _ else 1)

theorem Tens.inc_pr' (T : Tens D D' W) (i₀ i : Fin r) :
    T.inc i₀ ≫ T.pr i = if i = i₀ then 𝟙 _ else 1 :=
  T.lim.fac _ ⟨i⟩

def Tens.xi (T : Tens D D' W) (i₀ : Fin r) : D.X →+ D'.X :=
  T.xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => D.X) i₀)

def Tens.xp (T : Tens D D' W) (i₀ : Fin r) : D'.X →+ D.X :=
  (Pi.evalAddMonoidHom (fun _ => D.X) i₀).comp T.xe.toAddMonoidHom

end

def TensO.idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO s := TensO.ofMat s (Matrix.single i₀ i₀ 1)

theorem TensO.idem_mul_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) : TensO.idem s i₀ * TensO.idem s i₀ = TensO.idem s i₀ := by
  have h : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    simp
  exact h

def TensO.binv {r : ℕ} (s : SymUnit r) : TensO s := TensO.ofMat s ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)

end GlobalTheory.Mum
