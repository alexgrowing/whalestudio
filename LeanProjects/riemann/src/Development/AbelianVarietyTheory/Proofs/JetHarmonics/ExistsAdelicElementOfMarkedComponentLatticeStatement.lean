import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_element_of_marked_component_lattice : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  first | exact @GlobalTheory.ShortMove.exists_marked_of_component | exact GlobalTheory.ShortMove.exists_marked_of_component | (intros; apply GlobalTheory.ShortMove.exists_marked_of_component <;> assumption)
