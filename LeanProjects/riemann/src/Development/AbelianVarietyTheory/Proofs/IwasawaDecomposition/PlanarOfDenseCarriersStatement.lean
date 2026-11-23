import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlanarOfDenseCarriers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.planar_of_dense_carriers : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (Ω : Set Z'), IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ ξ, Car Em f q w α h ξ) → Planar Em f q := by
  first | exact @GlobalTheory.GrCl.PlanarMap.planar_of_generic | exact GlobalTheory.GrCl.PlanarMap.planar_of_generic | (intros; apply GlobalTheory.GrCl.PlanarMap.planar_of_generic <;> assumption)
