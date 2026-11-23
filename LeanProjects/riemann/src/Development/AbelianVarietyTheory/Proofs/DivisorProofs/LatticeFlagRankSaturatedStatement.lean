import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFlagRankSaturated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_flag_rank_saturated : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V) (k : ℕ) (hk : k ≤ r), E.FG → LinearIndependent K v → Submodule.span K (Set.range v) ≤ Submodule.span K (E : Set V) → latRank K (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)) = k ∧ (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)).FG ∧ Submodule.span K ((E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = Submodule.span K (Set.range (v ∘ Fin.castLE hk)) ∧ ∀ i, lineHt h (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)) (v ∘ Fin.castLE hk) i = lineHt h E v (Fin.castLE hk i) := by
  first | exact @GlobalTheory.LieSmooth.inf_span_castLE_lineHt | exact GlobalTheory.LieSmooth.inf_span_castLE_lineHt | (intros; apply GlobalTheory.LieSmooth.inf_span_castLE_lineHt <;> assumption)
