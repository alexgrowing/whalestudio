import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.Branching

theorem equivariant_map_eq_smul : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam sg → ∀ (φ φ' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), (∀ ψ, ψ = φ ∨ ψ = φ' → (∀ f ∈ nablaSq ℂ N lam, ψ f ∈ nablaSq ℂ n sg) ∧ ∀ (g : GL (Fin n) ℂ), ∀ f ∈ nablaSq ℂ N lam, ψ (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g) f) = sqAct ℂ n sg g (ψ f)) → (∃ f ∈ nablaSq ℂ N lam, φ' f ≠ 0) → ∃ c : ℂ, ∀ f ∈ nablaSq ℂ N lam, φ f = c • φ' f := by
  intro n N h lam sg hI φ φ' H hne
  let mk : ∀ ψ, (ψ = φ ∨ ψ = φ') → (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
      (smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) := fun ψ hψ =>
    ⟨ψ.restrict (H ψ hψ).1, fun g => LinearMap.ext fun f => Subtype.ext ((H ψ hψ).2 g f.1 f.2)⟩
  have h1 := (comult_id n N h lam sg).1 hI
  have hz : mk φ' (Or.inr rfl) ≠ 0 := by
    obtain ⟨f, hf, hf0⟩ := hne
    intro e
    apply hf0
    have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) e
    exact this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 (mk φ (Or.inl rfl))
  refine ⟨c, fun f hf => ?_⟩
  have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) hc
  exact this.symm

end GlobalTheory.Branching
