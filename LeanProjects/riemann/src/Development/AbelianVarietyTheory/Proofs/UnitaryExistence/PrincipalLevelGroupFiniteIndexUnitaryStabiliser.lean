import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceFiniteIndex

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem princ_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab Gm (LinearMap.range φ0) γ → ∃ s ∈ S, s⁻¹ * γ ∈ princ l Gm Di φ0 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ _
  haveI := Di.fin
  have hΛ : (LinearMap.range φ0).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map φ0 Module.Finite.fg_top
  have hM : 0 < l.M * l.A := Nat.mul_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨S, hS⟩ := GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM
  refine ⟨S, fun γ hγ => ?_⟩
  obtain ⟨s, hs, hst, hc⟩ := hS γ hγ
  refine ⟨s, hs, hst, fun a _ => ?_, fun a => ?_⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.A • b, by rw [e, map_nsmul, mul_smul]⟩
  · obtain ⟨w, ⟨b, rfl⟩, e⟩ := hc _ (LinearMap.mem_range_self φ0 a)
    exact ⟨l.M • b, by rw [e, map_nsmul, mul_comm, mul_smul]⟩

end GlobalTheory.FrameUnif
