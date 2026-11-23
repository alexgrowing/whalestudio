import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramMatrixExistence

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem exists_perp_hermitian_reduction (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f) :
    ∃ (β : Fin (r - 2) → Fin r → E) (S : ReciprocityTheory.MultiplicativeHeights.HermForm E (r - 2))
      (LB : Submodule (𝓞 E) (Fin (r - 2) → E)) (Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ),
      (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 → ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) ∧
      (∀ c c' : Fin (r - 2) → E, S.h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k)) ∧
      (∀ c : Fin (r - 2) → E, c ∈ LB ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L') ∧
      ReciprocityTheory.MultiplicativeHeights.IsLattice LB ∧ ReciprocityTheory.MultiplicativeHeights.IsSelfDual S LB ∧
      (∀ τ, (Q τ).det ≠ 0) ∧
      (∀ τ (c c' : Fin (r - 2) → E), τ.1 (S.h c c') =
        ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c')) ∧
      (∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
        ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k) := by
  obtain ⟨β, hβξ, hli, hspan⟩ := PerpBasisExistence.exists_beta X.toData hξ.2.1 hξ.2.2
  obtain ⟨Q, hQ, hSQ, hQf⟩ := GramMatrixExistence.Q_exists X ξ z0 f hξ hz hf β hβξ hli hspan
  exact ⟨β, PerpLatticeTransfer.Sform X β, PerpBasisExistence.LBsub X β ξ, Q, hβξ, hli, hspan,
    fun c c' => PerpLatticeTransfer.Sform_h X β c c', fun c => Iff.rfl,
    PerpLatticeTransfer.LB_lattice X β ξ hli, PerpLatticeTransfer.LB_selfDual X β ξ hξ hβξ hspan, hQ, hSQ, hQf⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
