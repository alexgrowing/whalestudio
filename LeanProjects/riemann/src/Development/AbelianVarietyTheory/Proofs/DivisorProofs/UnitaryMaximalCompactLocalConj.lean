import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWittBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockCentreMemStandardParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusCharacterAtSlotElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LanglandsLemmaUnitaryLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormConstantTermVanishesStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

theorem GlobalTheory.LeviBlockRealization.exists_norm_eq_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v), ∃ B : GL (Fin n) (Fv F v),
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
      φ = ∑ j, T j (x j) → ∀ S s, GlobalTheory.StdPar.IsCuspExp σ J Xf Yf S K φ s → (∀ k ∈ S, ∀ i ≤ k, i ∈ S) →
      ∀ i ∈ S, i.val + 1 ≤ n ∧ ∀ (hi : i.val + 1 ≤ n) (ϖ : (Fv F v)ˣ) (L : List ℂ),
        (∀ w, polyAt (jac (blockIndex hi) π (blockScalar₂ (Fv F v) n i ϖ)) L w = 0) →
        ∃ c ∈ L, ‖c‖ = nabs (Fv F v) ϖ ^ (s i).re := by
  intro F E _ _ _ _ _ σ hcm n J hJ r Xf Yf hW hLL v t
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.T.exists_local_witt_basis F E σ hcm n J hJ r Xf Yf hW v t
  refine ⟨B, fun K hK φ hφ V _ _ π hπ m T x hT hφx S s hs hS i hiS => ⟨?_, fun hi ϖ L hL => ?_⟩⟩
  · have h1 : (1 : Matrix (Fin r) (Fin r) E).rank ≤ n := by
      rw [← hW.xy]
      exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_height _)
    rw [Matrix.rank_one, Fintype.card_fin] at h1
    omega
  · obtain ⟨x₀, e, hx₀, hcen, habs⟩ := hB2 i hi ϖ
    obtain ⟨φc, hφc, hexp⟩ := hs
    have hrel := GlobalTheory.T.langlands_lemma_unitary_local F E σ hcm n J hJ r Xf Yf hW hLL v t B S hS i hiS hi (hB1 S hS i hiS hi) ϖ x₀ e hx₀ hcen
      K hK φ hφ V π hπ m T x hT hφx φc hφc L hL
    rw [GlobalTheory.T.modulus_character_at_position_element (Fv F v) n i hi ϖ, ← habs] at hrel
    obtain ⟨c, hc, hn⟩ := GlobalTheory.T.cusp_form_constant_term_vanishes F E σ hcm n J hJ r Xf Yf hW K S hS i hiS φc hφc.1 s hexp e (emb σ J v x₀) hcen L hrel
    exact ⟨c, hc, by rw [hn, habs]⟩

end
