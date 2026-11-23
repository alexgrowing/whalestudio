import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionLogNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_section_log_norm : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ), (∀ i, IsDivNorm (Y.an σ) (C i) (n i)) → (∀ i, genericPoint Y.X ∉ C i) → ∃ (L : LocPot (Pts Y σ)) (t : Pts Y σ → Pts Y σ → ℂ), IsBdSec (atlasOf Y σ) {z | ∃ i, under z ∈ C i} (fun z => Real.exp 1 - Real.log ((∏ i, n i z) ^ 2)) L t := by
  first | exact @GlobalTheory.DivSecAtlas.isBdSec_atlasOf | exact GlobalTheory.DivSecAtlas.isBdSec_atlasOf | (intros; apply GlobalTheory.DivSecAtlas.isBdSec_atlasOf <;> assumption)
