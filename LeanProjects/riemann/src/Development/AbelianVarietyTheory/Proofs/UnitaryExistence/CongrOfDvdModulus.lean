import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelMStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnifStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLatticeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompatStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.FrameNorm
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem congr_of_dvd_modulus {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    (Λ : Submodule (𝓞 E) (Fin r → E)) (φ : L ≃ₗ[𝓞 E] Λ) (γ : Matrix (Fin r) (Fin r) E) {m N : ℕ} (hd : m ∣ N)
    (h : ∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec γ x - x = (N : E) • y) (a : L) :
    ∃ b : L, γ.mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + m • (φ b : Fin r → E) := by
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨y, hy, e⟩ := h _ (φ a).2
  refine ⟨φ.symm (d • ⟨y, hy⟩), ?_⟩
  rw [LinearEquiv.apply_symm_apply, ← sub_eq_iff_eq_add', e, Nat.cast_smul_eq_nsmul, mul_smul]
  rfl

theorem exists_unf_hasPrinc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ HasPrinc U l.M' ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  intro E _ _ _ H Dw l Xo c σ r ξ₀ Gm φ hpq hσ hξ hneg hφ
  have hN : N1c := GlobalTheory.T.cmModuli_consequence_of_abelianSchemeLaws
  have hH := GlobalTheory.T.hasse_norm_theorem_quadratic_extension
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  classical
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := hN E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation hH E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, fun k γ hγ h => ?_,
    ⟨⟨0, F.n_pos⟩⟩, hM.chi, hG,
    fun k x => GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c (CAt σ) _, fun ρ => ⟨GlobalTheory.T.arithmeticGroup_cuspCentre_lattice E r ρ _ _, fun hA => ?_⟩⟩
  · exact (hM.gam k γ).2 ⟨hγ, fun a _ => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_left _ _) h a,
      fun a => congr_of_dvd_modulus _ (M.φ k) _ (Nat.dvd_lcm_right _ _) h a⟩
  · exact GlobalTheory.T.flagDomainModels_exponents_levelM E H Dw l Xo _ _ _ F r M ρ hM hA

end GlobalTheory.FrameUnif
