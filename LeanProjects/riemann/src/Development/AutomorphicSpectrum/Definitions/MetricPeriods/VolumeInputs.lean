import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top Filter Topology

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

structure GenModel (R : RootModel Ψ N) (Λ : ℝ) where

  F : Type
  [fieldF : Field F]
  [nfF : NumberField F]
  [algF : Algebra F R.Ω]

  I : Type
  [finI : Fintype I]

  w : I → R.Ω

  L : HermLine (fun _ : Unit => I)
  L_deg : L.a = fun _ => 1
  arith : IsArithVar (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) (dimFl Ψ N + 1)
  gen : IsGenH (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) L Λ
  deg_pos : 0 < geomDeg (mCoordIdeal (ι := fun _ : Unit => I) fun x => w x.2) L (dimFl Ψ N)

attribute [instance] GenModel.fieldF GenModel.nfF GenModel.algF GenModel.finI

namespace GenModel

variable {R : RootModel Ψ N} {Λ : ℝ} (G : GenModel R Λ)

def ht (II : IntersectionSystem) : ℝ :=
  normHt II (mCoordIdeal (ι := fun _ : Unit => G.I) fun x => G.w x.2) G.L (dimFl Ψ N)

include G in

theorem charZero : CharZero R.Ω := charZero_of_injective_algebraMap (algebraMap G.F R.Ω).injective

def del : ℝ :=
  haveI := G.charZero
  (IntermediateField.relfinrank (blockFnField (ι := fun _ : Unit => G.I) fun x => G.w x.2) ⊤ : ℝ) *
    geomDeg (mCoordIdeal (ι := fun _ : Unit => G.I) fun x => G.w x.2) G.L (dimFl Ψ N) / R.δ

def HasInputs (lam : ℝ → Wt Ψ N) (cc : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
    ∀ n, ∃ (q : ℕ) (m : Option (Ψ × Fin N) → ℤ), 0 < q ∧ (∀ j, (m j : ℝ) = q * R.coef (lam (s n)) (s n) j) ∧
      Nonempty (SectionInputs R.y G.F G.w G.L (combLine (R.line (scale (s n))) m) q cc C (s n))

end GenModel

def VolumeInputs : Prop :=
  BirationalPullbackPushforwardFormula ∧ ArithmeticHilbertSamuelUpperBoundNumberField ∧ GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement ∧
    ∀ (p : ℕ) [Fact p.Prime] (K K' : Type) [Fintype K] [Fintype K'] (ι : K → Type) [∀ k, Fintype (ι k)]
      (ι' : K' → Type) [∀ k, Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement (ZMod p) ι ι'

end GlobalTheory.CompanionTheory.Ar.Small
