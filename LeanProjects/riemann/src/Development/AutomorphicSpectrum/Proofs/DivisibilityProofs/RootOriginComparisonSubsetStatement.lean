import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_comparison_subset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx), S₀ ⊆ S → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S₀) → o₀.𝔐.OmVB → o₁.𝔐.OmVB → (∀ p ∈ S₀, o₀.𝔐.R p = o₁.𝔐.R p) → oR.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (κR : Rf.K → K) (vR : (Σ k, Rf.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (iR : Rf.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), IsBlockMap κ₀ v₀ ∧ IsBlockMap κ₁ v₁ ∧ IsBlockMap κR vR ∧ (∀ p, y (v₀ p) = i₀ (M₀.y p)) ∧ (∀ p, y (v₁ p) = i₁ (M₁.y p)) ∧ (∀ p, y (vR p) = iR (Rf.y p)) ∧ i₀.comp o₀.g = iR.comp oR.g ∧ i₁.comp o₁.g = iR.comp oR.g ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) * M₀.δ = IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) * M₁.δ ∧ (∃ (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)), (Fl.shrink S₀ h hvb hsub).RootLines (fun r => pullDeg κ₀ (M₀.xdeg r)) (fun r => i₀ (o₀.e r))) ∧ Fl.RootLines (fun r => pullDeg κ₁ (M₁.xdeg r)) (fun r => i₁ (o₁.e r)) ∧ ∀ p ∈ S, HT.HTFree 𝔐 p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrLinked.common | exact GlobalTheory.CompanionTheory.Ar.OrLinked.common | (intros; apply GlobalTheory.CompanionTheory.Ar.OrLinked.common <;> assumption)
