import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_eigen_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  intro E _ _ _ H l c S _ _ N _ _ ρ m
  classical
  have hσ₀ : Function.Injective (fun τ : E →+* ℂ => embK c τ) := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => by
        have h1 := embK_coe c τ a
        have h2 := embK_coe c τ' a
        have h3 : embK c τ a = embK c τ' a := RingHom.congr_fun h a
        exact h1.symm.trans ((congrArg _ h3).trans h2))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => (algebraMap c.F S).comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) (algebraMap c.F S) (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map (algebraMap c.F S))
  have hI := EigenSplit.isInternal_eigenSub hσ ρ
  let A := fun τ : E →+* ℂ => EigenSplit.eigenSub ρ ((algebraMap c.F S).comp (embK c τ))
  have hsum : ∀ x : DirectSum _ (fun τ => A τ), DirectSum.coeAddMonoidHom A x = ∑ τ, (x τ : N) :=
    fun x => by
      conv_lhs => rw [← DirectSum.sum_univ_of x]
      simp [map_sum, DirectSum.coeAddMonoidHom_of]
  obtain ⟨x, hx⟩ := hI.2 m
  refine ⟨fun τ => x τ, ⟨fun τ a => EigenSplit.mem_eigenSub.1 (x τ).2 a, (hsum x).symm.trans hx⟩, ?_⟩
  rintro f ⟨hf, hm⟩
  let y : DirectSum _ (fun τ => A τ) :=
    DFinsupp.equivFunOnFintype.symm fun τ => ⟨f τ, EigenSplit.mem_eigenSub.2 (hf τ)⟩
  have hy : y = x := hI.1 (((hsum y).trans hm).trans hx.symm)
  funext τ
  rw [← hy]
  rfl

end GlobalTheory.Frames
