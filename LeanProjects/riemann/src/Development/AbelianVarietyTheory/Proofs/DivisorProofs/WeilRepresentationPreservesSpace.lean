import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProductStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SoStable

theorem so_stable : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT γ Φ' hΦ
  unfold Model.So at hΦ ⊢
  induction hΦ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, hloc, rfl⟩ := hx
    obtain ⟨g₁, g₂, hg, hg₁, hg₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ a' G.V'.J B.v₁ γ.1
    obtain ⟨h₁, h₂, hh, hh₁, hh₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ (a + a') G.W.J B.v₁ γ.2
    have hγ : γ = (g₁, h₁) * (g₂, h₂) := Prod.ext hg hh
    obtain ⟨f₂, φ₂, hSB₂, hcof₂, hv₂, he₂⟩ :=
      GlobalTheory.T.theta_trivial_at_place_product hP F E σ B a a' G X om om' hT B.v₁ g₂ h₂ hg₂ hh₂ f φ hSB hcof
    obtain ⟨φ', hSB', hne', hacts, he'⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT B.v₁ g₁ hg₁ h₁ hh₁ f₂ φ₂ hSB₂ hcof₂
    rw [hγ, map_mul, Module.End.mul_apply, he₂, he']
    refine Submodule.subset_span ⟨f₂, φ', hSB', ?_, ?_, rfl⟩
    · filter_upwards [hcof₂, (Set.finite_singleton B.v₁).compl_mem_cofinite] with w hw hw'
      rw [hne' w hw', hw]
    · obtain ⟨hφSB, ι, hι, hsupp⟩ := hloc
      refine ⟨hSB' _, ι, hι, fun Y hY => ?_⟩
      obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι g₁ hg₁ h₁ hh₁
        (φ₂ B.v₁) (hSB₂ _) (φ' B.v₁) (hSB' _) hacts
      rw [hPQ, hv₂, hsupp, mul_zero]
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit

end GlobalTheory.SoStable
