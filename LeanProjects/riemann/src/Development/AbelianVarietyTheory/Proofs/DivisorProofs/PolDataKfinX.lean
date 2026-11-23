import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnlyTrivialPartner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFixedAtOfSummands
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplAtBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairPolynomialCompactStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftInv GlobalTheory.ThK.LiftSemis

noncomputable section

namespace GlobalTheory.FockKFinX

theorem polData_kfinX : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M,
    ∃ S : Submodule ℂ (Fn F n d), FiniteDimensional ℂ S ∧ ∀ k ∈ KInf σ X B.emb, om (k, 1) Φ ∈ S := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hx
    obtain ⟨S₀, hS₀, hS₀k⟩ := GlobalTheory.T.theta_pair_polynomial_compact hKP.base F E σ B n d X W M χX χW om r s r' s' hP f hf
    refine ⟨S₀.map (GlobalTheory.FockKFin.pureL φ), inferInstance, fun k hk => ?_⟩
    have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
      intro u _
      simp [mat]
    obtain ⟨A, hA⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hP.base.std hP.weil (k, 1) hk.1 h1
    rw [GlobalTheory.T.weil_rep_intertwines_action F E σ B.ψ n d X W M om hP.good (k, 1) A hA f φ hφ hvac]
    exact Submodule.mem_map_of_mem (hS₀k k hk (A f) (hA f))
  | zero =>
    exact ⟨⊥, inferInstance, fun k _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁, k₁⟩ := hx
    obtain ⟨S₂, h₂, k₂⟩ := hy
    exact ⟨S₁ ⊔ S₂, inferInstance, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (k₁ k hk) (k₂ k hk)⟩
  | smul c x _ hx =>
    obtain ⟨S, h, k₁⟩ := hx
    exact ⟨S, h, fun k hk => by rw [map_smul]; exact Submodule.smul_mem _ c (k₁ k hk)⟩

end GlobalTheory.FockKFinX

end
