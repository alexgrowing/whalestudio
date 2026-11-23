import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_independent_span_iff : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (K : Type) [Field K] (w : Sp K ⟶ Z') (β : C.A) (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) (ξ : Fin k → Fin (C.n β) → K), Car Em f q w β hβ ξ → LinearIndependent K ξ ∧ (∀ ξ' : Fin k → Fin (C.n β) → K, Car Em f q w β hβ ξ' ↔ LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ)) ∧ ∀ (α : C.A) (hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), Car Em f q w α hα fun l => (C.tr α β (w ≫ f) hα hβ).mulVec (ξ l) := by
  first | exact @GlobalTheory.GrCl.car_span | exact GlobalTheory.GrCl.car_span | (intros; apply GlobalTheory.GrCl.car_span <;> assumption)
