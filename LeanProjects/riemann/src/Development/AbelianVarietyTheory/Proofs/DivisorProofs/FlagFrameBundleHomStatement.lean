import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameBundleHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_bundle_hom : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) → ∀ (E' : GlobalTheory.FlagBundle.Fr (GlobalTheory.FlagBundle.ratOf Y) (fun _ : ι => N) (fun _ => N)), (∀ y A', A' ∈ E'.S y ↔ GlobalTheory.FlagQ.IsFrame j y A') → ∀ (φ : (GlobalTheory.ProjVar.proj ℚ 0).Fn →ₐ[ℚ] Y.Fn), (GlobalTheory.FlagBundle.ratOf (GlobalTheory.ProjVar.proj ℚ 0)).IsHom (GlobalTheory.FlagBundle.ratOf Y) φ (GlobalTheory.FlagQ.toPt Y) → ∀ (K : Type) [Field K] (x : Sp K ⟶ (GlobalTheory.ProjVar.proj ℚ 0).X), ∀ A ∈ (GlobalTheory.FlagQ.triv ι N).S (x (IsLocalRing.closedPoint K)), ∀ h : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) K, GlobalTheory.FlagBundle.Par 0 ⊤ h → ∃! p : Sp K ⟶ Y.X, p ≫ GlobalTheory.FlagQ.toPt Y = x ∧ GlobalTheory.FlagBundle.Bears E' φ A h p := by
  first | exact @GlobalTheory.FlagQ.Lifts.existsUnique_bears | exact GlobalTheory.FlagQ.Lifts.existsUnique_bears | (intros; apply GlobalTheory.FlagQ.Lifts.existsUnique_bears <;> assumption)
