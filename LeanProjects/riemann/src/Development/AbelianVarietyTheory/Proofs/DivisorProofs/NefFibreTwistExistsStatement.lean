import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_fibre_twist_exists : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)), IsProjOver p → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ H : HermLB p, ∀ (X' : Scheme.{0}) (q : X' ⟶ Sp (𝓞 F)), IsProjOver q → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q), NefFib (H.pull π hπ) ∧ ∀ i, NefFib ((H.pull π hπ).tens ((L i).pull π hπ)) ∧ NefFib ((H.pull π hπ).tens ((L i).pull π hπ).dual) := by
  first | exact @GlobalTheory.AmpleTwistNef.exists_nefFib_twists | exact GlobalTheory.AmpleTwistNef.exists_nefFib_twists | (intros; apply GlobalTheory.AmpleTwistNef.exists_nefFib_twists <;> assumption)
