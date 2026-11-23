import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

variable (D : D7)

def rho {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (z : Bool × HH D) : D.host.E →+* ℂ_[p] :=
  (ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D (tauPl D z))

abbrev JJ (n : Bool × HH D → ℕ) (N N' : ℕ) : Type :=
  (Σ z : Bool × HH D, Fin (n z)) × ((Bool × HH D) × Fin N) × ((Bool × HH D) × Fin N')

def rowL {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E)
    (l : (Bool × HH D) × Fin N) : Fin N → D.host.E :=
  fun j => (σ l.1 : D.host.E) * (P (tauPl D l.1))⁻¹ l.2 j

def colR {N' : ℕ} (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ' : Bool × HH D → 𝓞 D.host.E)
    (r : (Bool × HH D) × Fin N') : Fin N' → D.host.E :=
  fun i => (σ' r.1 : D.host.E) * P' (tauPl D r.1) i r.2

def mat {n : Bool × HH D → ℕ} {N N' : ℕ} (a : ∀ z, Fin (n z) → D.host.E)
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N') : Matrix (Fin N') (Fin N) D.host.E :=
  Matrix.of fun i k => a j.1.1 j.1.2 * colR D P' σ' j.2.2 i * rowL D P σ j.2.1 k

def vecF {X : Fields} (s : Seam D X) {N N' : ℕ} (M : Matrix (Fin N') (Fin N) D.host.E) : DVar X.Tau N N' → ℂ :=
  fun k => TaylorLogMetric.embT D (s.iT k.1) (M k.2.1 k.2.2)

def act {X : Fields} (s : Seam D X) (N N' : ℕ) (e : 𝓞 D.host.E) : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ) where
  toFun x := fun k => TaylorLogMetric.embT D (s.iT k.1) (e : D.host.E) * x k
  map_add' x y := by funext k; simp [mul_add]
  map_smul' c x := by funext k; simp; ring

def gc {p : ℕ} [Fact p.Prime] {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p])
    (z : Bool × HH D) (α : Σ z : Bool × HH D, Fin (n z)) : ℂ_[p] :=
  if α.1 = z then cκ z * r α.1 α.2 else 0

def pc {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ} (σ : Bool × HH D → 𝓞 D.host.E) (z : Bool × HH D)
    (l : (Bool × HH D) × Fin N) (a : Fin N) : ℂ_[p] :=
  if l = (z, a) then (rho D ι z (σ z : D.host.E))⁻¹ else 0

def coef {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} {N N' : ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (σ σ' : Bool × HH D → 𝓞 D.host.E) (j : JJ D n N N')
    (x : (Bool × HH D) × Fin N × Fin N') : ℂ_[p] :=
  gc D cκ r x.1 j.1 * pc D ι σ x.1 j.2.1 x.2.1 * pc D ι σ' x.1 j.2.2 x.2.2

def uu {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n : Bool × HH D → ℕ} (cκ : Bool × HH D → ℂ_[p])
    (r : ∀ z, Fin (n z) → ℂ_[p]) (a : ∀ z, Fin (n z) → D.host.E) (t : HH D) : ℂ_[p] :=
  ∑ α, ∑ α', gc D cκ r (false, t) α * rho D ι (false, t) (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) *
    gc D cκ r (true, t) α'

end GlobalTheory.DFrame
