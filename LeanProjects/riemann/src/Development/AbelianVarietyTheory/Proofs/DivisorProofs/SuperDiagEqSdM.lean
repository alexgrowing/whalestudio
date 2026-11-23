import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.TateThesis.AdelicChar

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory

namespace GlobalTheory.WhitBump

abbrev Idx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Vp (E : Type) [Field E] (n : ℕ) : Type := Idx n → Cinf E

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def nu (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdM {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, x i j

theorem superDiag_eq_sdM {R : Type} [CommRing R] (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag g = sdM (g : Matrix (Fin n) (Fin n) R) := rfl

theorem nu_lower (t : Vp E n) {i j : Fin n} (h : j < i) : nu t i j = 0 := by
  simp [nu, not_lt_of_gt h, ne_of_gt h]

theorem nu_diag (t : Vp E n) (i : Fin n) : nu t i i = 1 := by
  simp [nu]

theorem det_nu (t : Vp E n) : (nu t).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [nu_diag]
  · intro i j h; exact nu_lower t h

def nuGL (t : Vp E n) : GL (Fin n) (Cinf E) :=
  Matrix.nonsingInvUnit (nu t) (by rw [det_nu]; exact isUnit_one)

@[simp] theorem nuGL_val (t : Vp E n) : (nuGL t : Matrix (Fin n) (Fin n) (Cinf E)) = nu t := rfl

theorem nuGL_mem (t : Vp E n) : nuGL t ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun _ _ h => nu_lower t h, nu_diag t⟩

variable [IsTotallyComplex E]

def psiInf (z : Cinf E) : ℂ := (GroundTheory.Global.adelicChar E (sInf E z) : ℂ)

def psiFin (a : Af E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E a) : ℂ)

def bumpInf (f : Lie E n → ℝ) (x : Lie E n) : ℂ :=
  ∫ t : Vp E n, (f (toL (nu t * Matrix.of x)) : ℂ) * psiInf (-sdM (nu t))

open Classical in

def bumpFin (g : GL (Fin n) (Af E)) : ℂ :=
  if h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n then
    psiFin (GlobalTheory.Whittaker.superDiag h.choose) else 0

end GlobalTheory.WhitBump
