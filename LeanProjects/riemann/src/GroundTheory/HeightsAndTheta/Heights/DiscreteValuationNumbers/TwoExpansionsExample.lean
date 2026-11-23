import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisRest
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinDivDiffExpansion
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

namespace TwoExpansionsAgree

def divExp {N : ℕ} (G : MvPolynomial (Fin N) ℤ) (i : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℤ :=
  rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff i G)

def Common.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (ϖ : O),
    Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum (pointIdeal O y) x x' f g (divExp G) Q =
        pairNum (pointIdeal O y) u u' f₂ g₂ (divExp G) Q

theorem isMultiHomog_one {R : Type*} [CommRing R] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (fun _ => 0) := by
  classical
  intro μ hμ k
  have h0 : μ = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hμ
    exact hμ rfl
  subst h0
  simp

theorem isVertDiv_one {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P (b - b) 1 1 := by
  have h1 : ∀ W : Ideal (MRing ι O), W.IsPrime → (1 : MRing ι O) ∉ W :=
    fun W hW h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  refine ⟨⟨fun _ => 0, fun _ => 0, isMultiHomog_one, isMultiHomog_one, fun k => by simp⟩,
    h1 P hP, h1 P hP, fun W hW _ _ => ⟨1, 1, ⟨_, isMultiHomog_one⟩, ⟨_, isMultiHomog_one⟩,
      h1 W hW.1, h1 W hW.1, by simp⟩⟩

end TwoExpansionsAgree

end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
