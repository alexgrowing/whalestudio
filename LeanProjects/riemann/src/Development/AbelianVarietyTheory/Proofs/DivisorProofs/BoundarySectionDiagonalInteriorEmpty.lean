import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.SncZero

theorem interior_zero_eq_empty_of_isSNC {e : ℕ} {X : Type} [TopologicalSpace X]
    (At : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (mu : Fin r → ℕ)
    (D : Fin r → Set X) (hs : IsSection At L s)
    (hn : ReciprocityTheory.AnForm.M.IsSNC At L s mu D) : interior {y | s y y = 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ψ, -, hxs, hsub, σ, -, -, u, -, hu, hform⟩ := hn x
  have hopen : IsOpen (ψ '' (interior {y | s y y = 0} ∩ ψ.source)) :=
    ψ.isOpen_image_of_subset_source (isOpen_interior.inter ψ.open_source) Set.inter_subset_right
  have hdense : Dense (Set.pi Set.univ (fun _ : Fin e => ({0}ᶜ : Set ℂ))) :=
    dense_pi Set.univ (fun _ _ => dense_compl_singleton (0 : ℂ))
  obtain ⟨z, ⟨y, ⟨hyi, hys⟩, rfl⟩, hz⟩ :=
    hdense.inter_open_nonempty _ hopen ⟨ψ x, x, ⟨hx, hxs⟩, rfl⟩
  have hy0 : s y y = 0 := interior_subset (s := {y | s y y = 0}) hyi
  have hnorm := hs.2 x y y ⟨hsub hys, L.mem_U y⟩
  rw [hy0, norm_zero, zero_mul] at hnorm
  have hxy : s x y = 0 := by
    rcases mul_eq_zero.1 hnorm with h | h
    · exact norm_eq_zero.1 h
    · exact absurd h (Real.exp_pos _).ne'
  rw [hform y hys] at hxy
  rcases mul_eq_zero.1 hxy with h | h
  · exact hu y hys h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    rcases hσ : σ k with _ | j
    · rw [hσ] at hk
      exact one_ne_zero hk
    · rw [hσ] at hk
      exact hz j (Set.mem_univ j) (eq_zero_of_pow_eq_zero (n := mu k) hk)

theorem interior_zero_boundary : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (At : FinHolAtlas e X) (m : ℕ) (L : Fin m → LocPot X) (sg : Fin m → X → X → ℂ) (Dd : Fin m → Set X), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary At L sg Dd → ∀ i, interior {y | sg i y y = 0} = ∅ := by
  intro e X _ At m L sg Dd h i
  exact interior_zero_eq_empty_of_isSNC At (L i) (sg i) _ Dd (h i).2.1 (h i).2.2.1

end GlobalTheory.SncZero
