import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLinesSmoothFunctionSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureBasisMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLineEigenvectorAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactIsometryLieAlgebraBoundStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.GrowthDec

open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open GlobalTheory.Orb (archMat)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isLineOf_conj (h : IsCMExt F E σ) {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ}
    {γ : ℝ → GAd σ J} (hγ : IsLineOf σ J τ Z γ) (a : GAd σ J) :
    IsLineOf σ J τ ((archMat σ J τ (projArch σ J w a))⁻¹ * Z * archMat σ J τ (projArch σ J w a))
      fun t => a⁻¹ * γ t * a := by
  intro t
  have h1 : archMat σ J τ (projArch σ J w a)⁻¹ * archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : archMat σ J τ (projArch σ J w a) * archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨y, e1, e2⟩ := hγ t
  refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
  · show a⁻¹ * γ t * a = _
    rw [e1]
    refine GAd_ext σ J (fun u => ?_) fun v => by simp
    by_cases e : u = w
    · subst e; simp
    · simp [projArch_embArch_ne σ J e]
  · rw [map_mul, map_mul, e2]
    generalize archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize archMat σ J τ (projArch σ J w a) = M at *
    have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
    rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

theorem dec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ x : Fin n → E, hE σ J x x = 0 → ∀ K : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K → ∀ S : Set (GAd σ J), IsCompact S →
    ∀ γ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J γ →
      ∃ (e e' : ℕ) (β : Fin e → ℝ → GAd σ J) (ζ : Fin e' → ℝ → GAd σ J) (C : ℝ),
        (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (β j) ∧ ∀ s, ∃ t : AF F ⊗[F] E,
          (matHom _ σ J (β j s)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = t • fun i => inclR (F := F) (AF F) (x i)) ∧
        (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (ζ j) ∧ ∀ s, ζ j s ∈ K) ∧
        ∀ k ∈ S, ∃ (c : Fin e → ℂ) (c' : Fin e' → ℂ), (∀ j, ‖c j‖ ≤ C) ∧ (∀ j, ‖c' j‖ ≤ C) ∧
          ∀ f, GlobalTheory.UAut.IsSm σ J f → GlobalTheory.SiegelSet.lineDer γ f =
            ∑ j, c j • GlobalTheory.SiegelSet.lineDer (fun s => k⁻¹ * β j s * k) f + ∑ j, c' j • GlobalTheory.SiegelSet.lineDer (ζ j) f := by
  intro F E _ _ _ _ _ σ h n J hJ x hx K hK S hS γ hγ
  obtain ⟨w, τ, X, hX, hγ⟩ := hγ
  have hγ' : IsLineOf σ J τ X γ := hγ
  obtain ⟨R, ε, hR, hRK⟩ := GlobalTheory.T.exists_signature_basis_max_compact F E σ h n J hJ K hK w τ
  have hA : (J.map τ.1)ᴴ = J.map τ.1 := conjTranspose_map h hJ τ.1
  have hv : star (fun i => τ.1 (x i)) ⬝ᵥ J.map τ.1 *ᵥ (fun i => τ.1 (x i)) = 0 := by
    have e := congrArg τ.1 hx
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, map_zero] at e
    rw [← e]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show τ.1 ((σ : E →+* E) (x i)) = star (τ.1 (x i)) from h.2.2.2 τ.1 (x i)]
    ring
  have hm : Continuous fun k : GAd σ J => archMat σ J τ (projArch σ J w k) :=
    (GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)
  have hu : ∀ y : GArch σ J w, (archMat σ J τ y)ᴴ * J.map τ.1 * archMat σ J τ y = J.map τ.1 :=
    fun y => (archEquiv J h τ y).2
  have hmu : ∀ k : GAd σ J, (archMat σ J τ (projArch σ J w k))ᴴ * J.map τ.1 * archMat σ J τ (projArch σ J w k) =
      J.map τ.1 := fun k => hu _
  obtain ⟨e, e', Yb, l, Zb, C, hY, hZ, hc⟩ := GlobalTheory.T.compact_isometry_lie_algebra_bound n (J.map τ.1) R ε hA hR _ hv (GAd σ J) S hS _ hm.continuousOn
    (fun k _ => hmu k) X hX
  choose β hβ using fun j => exists_isLineOf h hJ (hY j).1
  choose ζ hζ using fun j => exists_isLineOf h hJ (hZ j).1
  refine ⟨e, e', β, ζ, C, fun j => ⟨(hβ j).isRealLine h, GlobalTheory.T.levi_line_eigenvector_adelic_point F E σ h n J x w τ (Yb j) (l j) (hY j).2 (β j) (hβ j)⟩,
    fun j => ⟨(hζ j).isRealLine h, hRK (Zb j) (ζ j) (hζ j) (hZ j).2⟩, fun k hk => ?_⟩
  obtain ⟨c, c', hc1, hc2, hX'⟩ := hc k hk
  refine ⟨fun j => (c j : ℂ), fun j => (c' j : ℂ), fun j => by simpa using hc1 j, fun j => by simpa using hc2 j,
    fun f hf => ?_⟩
  have key := GlobalTheory.T.levi_lines_smooth_function_span F E σ h n J hJ w τ f hf (Fin e ⊕ Fin e')
    (Sum.elim (fun j => (archMat σ J τ (projArch σ J w k))⁻¹ * Yb j * archMat σ J τ (projArch σ J w k)) Zb)
    (Sum.elim (fun j s => k⁻¹ * β j s * k) ζ) (Sum.elim c c') γ
    (by rintro (j | j); exacts [isLineOf_conj h (hβ j) k, hζ j])
    (by rw [Fintype.sum_sum_type]; simpa only [Sum.elim_inl, Sum.elim_inr, ← hX'] using hγ')
  rw [key, Fintype.sum_sum_type]
  rfl

end GlobalTheory.GrowthDec
