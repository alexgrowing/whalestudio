import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquarePolCover.exists_cover : AmpleSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 2 ≤ n → ∃ (κ : Type)
    (s : κ → H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n),
    (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
  intro hA R _ _ P n hn
  obtain ⟨κ, t, ht, hta⟩ := GlobalTheory.Algebraise.exists_cover hA P (2 * n) (by omega)
  have hm : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  choose s hs using fun i => GlobalTheory.T.linComb_pow_section_unflatten P.L 2 n ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) (t i)
  have key : ∀ i, nonzeroLocus (s i) = nonzeroLocus (t i) := by
    intro i
    ext x
    obtain ⟨j, hj⟩ := exists_chart P.isLB x
    have h₁ := GlobalTheory.SectionRingIso.mem_iff_isUnit (t i) (𝟙 _) x (j := fun _ => j) hj
    have h₂ := GlobalTheory.SectionRingIso.mem_iff_isUnit (s i) (𝟙 _) x (j := fun _ => fun _ => j)
      (GlobalTheory.SectionRingIso.mem_ch.2 hj)
    have h₃ := hs i P.A.left (𝟙 _) x j hj
    exact h₂.trans ((congrArg IsUnit h₃).to_iff.symm.trans h₁.symm)
  refine ⟨κ, s, ?_, fun i => ?_⟩
  · simp_rw [key]; exact ht
  · rw [key]; exact hta i
