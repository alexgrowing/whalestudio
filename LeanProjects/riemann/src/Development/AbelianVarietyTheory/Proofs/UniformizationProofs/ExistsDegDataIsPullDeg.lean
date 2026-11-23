import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.exists_degData_isPullDeg : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' → ∀ (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R I) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Out.PsiOn D.toPre W) → (_root_.ReciprocityTheory.ChartRestriction.G.Out.specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W → ∃ (D' : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegData R' I') (hD : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPullDeg φ D.toPre D'.toPre), hD.W = W ∧ D'.toPre.P.g = D.toPre.P.g := by
  intro hP hG R R' _ _ _ _ I I' φ hle D W hψ hgen
  obtain ⟨D₀, hE, hT, hI, hF⟩ := D
  obtain ⟨D', hD, hW, hg⟩ :=
    _root_.GlobalTheory.DegPull.exists_isPullDeg hP R R' φ D₀ W hψ hgen
  refine ⟨⟨D', _root_.GlobalTheory.PsiEvenPull.psiEven_pull hG R R' φ D₀ D' hD hE,
    _root_.GlobalTheory.tauBimult_of_isPullDeg hG R R' φ D₀ D' hD hT, ?_, ?_⟩, hD, hW, hg⟩
  · intro χ hχ
    exact _root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ I I' hle
      (hI _ fun h => hχ (hD.xe.map_eq_zero_iff.mp h))
  · intro n
    refine ((hF n).preimage hD.xe.injective.injOn).subset ?_
    intro χ hχ h
    exact hχ (_root_.GlobalTheory.psiIn_of_isPullDeg R R' φ D₀ D' hD χ (I ^ n) (I' ^ n)
      (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hle n) h)

end GlobalTheory
