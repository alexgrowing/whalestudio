import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Calc2

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Cf (n : ℕ) := EuclideanSpace ℝ (Bool × Fin n × Fin n)

def crd (v : Cf n) : Mat n := ∑ p, v p • bs p

def ex (v : Cf n) : Mat n := NormedSpace.exp (crd v)

def s2 (n : ℕ) : ℝ := ⨍ v in Metric.ball (0 : Cf n) 1, ‖v‖ ^ 2

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ld (Y : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (Y * g)

def Lw : List (Bool × Fin n × Fin n) → (Mat n → V) → (Mat n → V)
  | [] => id
  | p :: w => fun f => Ld (bs p) (Lw w f)

def lap (f : Mat n → V) : Mat n → V := ∑ p, Rd (bs p) (Rd (bs p) f)

def kp (X : Mat n) : Mat n := (1 / 2 : ℂ) • (X - Xᴴ)

def ksq (f : Mat n → V) : Mat n → V := ∑ p, Rd (kp (bs p)) (Rd (kp (bs p)) f)

def dlap (ε : ℝ) (f : Mat n → V) : Mat n → V := fun x =>
  ((2 * (Fintype.card (Bool × Fin n × Fin n) : ℝ)) / (ε ^ 2 * s2 n)) •
    ⨍ v in Metric.ball (0 : Cf n) 1, (f (x * ex (ε • v)) - f x)

def OmE (C : V →L[ℂ] V) (ε : ℝ) (f : Mat n → V) : Mat n → V := fun x => dlap ε f x + C (f x)

def chs (C : V →L[ℂ] V) (ε t : ℝ) (f : Mat n → V) : Mat n → V := fun x =>
  ∑' j : ℕ, ((t ^ (2 * j) / ((2 * j).factorial : ℝ) : ℝ) : ℂ) • (OmE C ε)^[j] f x

def shs (C : V →L[ℂ] V) (ε t : ℝ) (f : Mat n → V) : Mat n → V := fun x =>
  ∑' j : ℕ, ((t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) : ℝ) : ℂ) • (OmE C ε)^[j + 1] f x

end Ops

def wds (n m : ℕ) : Finset (List (Bool × Fin n × Fin n)) :=
  (Finset.range (m + 1)).biUnion fun l => (Finset.univ : Finset (Fin l → Bool × Fin n × Fin n)).image List.ofFn

def stp (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

def Equi (E : KMod n) (f : Mat n → E.V) : Prop :=
  ∀ g ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, f (g * k.1) = E.ρ k⁻¹ (f g)

def cop {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' j : ℕ, ((t ^ (2 * j) / ((2 * j).factorial : ℝ) : ℝ) : ℂ) • A ^ j

def sop {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  ∑' j : ℕ, ((t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) : ℝ) : ℂ) • A ^ (j + 1)

end PositivityTheory.RgBcC.Calc2
