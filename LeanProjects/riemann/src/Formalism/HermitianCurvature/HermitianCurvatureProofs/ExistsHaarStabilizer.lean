import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

def lowP {m : ℕ} (w : Equiv.Perm (Fin m)) (y : C2.LPidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.LPidx w => q.1) y

def lowS {m : ℕ} (w : Equiv.Perm (Fin m)) (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  C2.lowOf (fun q : C2.Lstidx w => q.1) x

def utc {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) : G.UT m → ℂ := fun q => u q.1.1 q.1.2

def lsc {m : ℕ} (w : Equiv.Perm (Fin m)) (l : Matrix (Fin m) (Fin m) ℂ) : C2.Lstidx w → ℂ := fun q => l q.1.1 q.1.2

def SplitUT : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)), ∃ e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT m → ℂ),
    MeasurePreserving e volume volume ∧ ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ

def UTLeft : Prop :=
  ∀ (m : ℕ) (a : Matrix (Fin m) (Fin m) ℂ), a ∈ C2.UTset m →
    MeasurePreserving (fun u : G.UT m → ℂ => utc (a * G.upper u)) volume volume

def LstLeft : Prop :=
  ∀ (m : ℕ) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ), (∀ a, d a ≠ 0) → ∀ x0 : C2.Lstidx w → ℂ,
    MeasurePreserving (fun x : C2.Lstidx w → ℂ => lsc w (lowS w x0 * lowS w x)) volume volume ∧
    ∀ x, lowS w x0 * lowS w x = lowS w (lsc w (lowS w x0 * lowS w x))

def MinorsLU : Prop :=
  ∀ (r : ℕ) (L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), L ∈ C2.LTset (r + 1) → U ∈ C2.UTset (r + 1) →
    (L * M * U).det = M.det ∧
      ((L * M * U).submatrix Fin.castSucc Fin.castSucc).det = (M.submatrix Fin.castSucc Fin.castSucc).det

def PhiTopCoords : Prop :=
  ∀ (m : ℕ) (σ w : Equiv.Perm (Fin m)) (d d' : Fin m → ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat m → V), (∀ a, d' a ≠ 0) → U.hMat σ d = C2.monoP w d' →
    U.PhiTop (p := m) (s := 0) U.betaU σ d Φ (fun x => x.elim0) =
      ∫ q : (C2.LPidx w → ℂ) × (G.UT m → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w q.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper q.2)))) •
          Φ (Matrix.of.symm (lowP w q.1 * C2.monoP w d' * G.upper q.2))

def ExistsHaarStabilizer : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ0 : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ0

def DisintN : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∀ μ0 μN : Measure (Mt k r),
    B.IsHaarOn (C2.N0set k r z) μ0 → B.IsHaarOn (Nset k r) μN →
    ∃ c : NNReal, 0 < c ∧ μN = c • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r z (G.upper p.1) * Matrix.of p.2))

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration
