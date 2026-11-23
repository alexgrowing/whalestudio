import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  first | exact @GlobalTheory.SphAvg.exists_sum_fixed | exact GlobalTheory.SphAvg.exists_sum_fixed | (intros; apply GlobalTheory.SphAvg.exists_sum_fixed <;> assumption)
