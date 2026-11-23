import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData),
    IsProjOver s → ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ GlobalTheory.ProjBlowup.Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates_isLB | exact GlobalTheory.ProjBlowup.exists_generates_isLB | (intros; apply GlobalTheory.ProjBlowup.exists_generates_isLB <;> assumption)
