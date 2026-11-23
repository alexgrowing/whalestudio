import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

abbrev MP (R : Type) [CommRing R] (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) R

def genM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) := Matrix.of fun a s => X (a, s)

def cofAct (R : Type) [CommRing R] (n : ℕ) : MP R n →ₐ[R] MP R n :=
  aeval fun v => (genM R n).adjugate v.2.rev v.1

def nuDual {m : ℕ} (ν : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := fun i => ν 0 - ν i.rev

def CofRel (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (f g : MP R (m + 1)) : Prop :=
  (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * g = cofAct R (m + 1) f

def stdN (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (dualWeyl O n n ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def stdD (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (weyl O n n le_rfl ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def rnd (Kf : Type) [Field Kf] {n : ℕ} (e : ℤ) (g : Matrix (Fin n) (Fin n) Kf) : MP Kf n →ₗ[Kf] MP Kf n :=
  g.det ^ (-e) • (rowAct Kf g⁻¹).toLinearMap

def twLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n : ℕ} (e : ℤ) (S : Submodule O (MP Kf n))
    (g : Matrix (Fin n) (Fin n) Kf) : Submodule O (MP Kf n) :=
  S.map ((rnd Kf e g).restrictScalars O)

def twOf {Kf : Type} [Field Kf] {n : ℕ} (s : ℕ) (h : Matrix (Fin n) (Fin n) Kf) : Matrix (Fin n) (Fin n) Kf :=
  if Even s then h else (h⁻¹).transpose

def PosOk (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν ν' : Fin n → ℕ) (e e' c : ℤ)
    (tw : Matrix (Fin n) (Fin n) Kf → Matrix (Fin n) (Fin n) Kf) (Ψ : MP Kf n →ₗ[Kf] MP Kf n) : Prop :=
  (∀ f ∈ dualWeyl Kf n n ν, Ψ f = 0 → f = 0) ∧
  (dualWeyl Kf n n ν).map Ψ = dualWeyl Kf n n ν' ∧
  (∀ h : Matrix (Fin n) (Fin n) Kf, IsUnit h.det → ∀ f ∈ dualWeyl Kf n n ν,
    Ψ (rnd Kf e h f) = h.det ^ c • rnd Kf e' (tw h) (Ψ f)) ∧
  (stdN O Kf n ν).map (Ψ.restrictScalars O) = stdN O Kf n ν' ∧
  (stdD O Kf n ν).map (Ψ.restrictScalars O) = stdD O Kf n ν'

def renP {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {ι : Type} (e : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ ι) :
    Formalism.L2.DIV.Pol Kf ι (P.m + 1) →ₐ[Kf] P.Xsp :=
  rename fun y => ⟨(e.symm y.1).1, ((e.symm y.1).2, y.2)⟩

end GlobalTheory.ValCmp
