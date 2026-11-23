import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationSeesawIdentityStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem twPart_map_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ → IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ' →
        (∃ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ x ≠ 0) → (∃ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), φ' x ≠ 0) → (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map φ = (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map φ' := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ φ' hφ hφ' hx hx'
  have hirr := GlobalTheory.T.config_a_theta_local_factor hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hland := GlobalTheory.T.configuration_seesaw_identity hK F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hirr₁ := GlobalTheory.T.lowPart_invariant_submodule_equiv hK F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁
  have key : ∀ ψ : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) ψ →
      (∃ x ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ψ x ≠ 0) → (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map ψ = lowPartInf B G₁.M R₁.p := by
    intro ψ hψ ⟨x, hx, hψx⟩
    have hle : (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map ψ ≤ lowPartInf B G₁.M R₁.p := by
      rintro _ ⟨y, hy, rfl⟩
      exact hland ψ hψ y hy
    have hstab : ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin b × Fin (b + a')),
        Acts (evI F) (om₁ (1, k₁)) g g₁ → R₁.p g ∈ (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map ψ → R₁.p g₁ ∈ (twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p)).map ψ := by
      rintro k₁ hk₁ g hg g₁ hg₁ ⟨y, hy, hyg⟩
      obtain ⟨k, hk, hL⟩ := GlobalTheory.T.levi_lift_maximal_compact F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ hM.triple.base.cm hM.triple.geo.hW hC.hH' k₁ hk₁
      have hy0 : y ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; exact Submodule.mem_top
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy0
      obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om X.β (X.β / X.α) hM.triple.base hM.triple.geo.hM
        hM.triple.weil k hk
      have h2 := hψ.cpt k hk 1 k₁ hL hk₁ f hf (A f) (hA f) g hg g₁ hg₁ hyg
      have hin : R.p (A f) ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) := hirr.2.1 k hk k₁ hk₁ hL f hf (A f) (hA f) hy
      refine ⟨R.p (A f), hin, ?_⟩
      rw [h2]
      simp
    rcases hirr₁ _ hle hstab with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩) hψx
    · exact h
  rw [key φ hφ hx, key φ' hφ' hx']

end GlobalTheory.IndLine
