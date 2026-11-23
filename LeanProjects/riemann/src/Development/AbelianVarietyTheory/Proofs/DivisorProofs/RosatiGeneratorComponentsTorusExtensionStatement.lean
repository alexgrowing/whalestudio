import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtRelVIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_components_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ'' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Mum.TensRos.RosVT T ν ν' (o.onB.act (star x)) (o.onB.act x) ρ'') → ∀ (χ : N'.X) (b : N'.A) (gs : Fin r → N.Gt), (∀ j, GlobalTheory.Mum.TensTor.cmp T ν ν' b j = (gs j).b) → (letI := H.starRing; ρ'' (N'.c χ) b * GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') (ν'.eX.symm (star x • ν'.eX χ)) gs = GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') χ (fun i => ∏ j, gs j ^ ρ x i j)) := by
  first | exact @GlobalTheory.Mum.TensRos.rosVT_components | exact GlobalTheory.Mum.TensRos.rosVT_components | (intros; apply GlobalTheory.Mum.TensRos.rosVT_components <;> assumption)
