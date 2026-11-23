import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedFockDegreeSpanStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IndLine

theorem actsD_zero_weil {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W)
    (γ : Multiplicative ℝ →* UA σ W.J) :
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(0 : SInf F (Fin n × Fin d)))
      (⇑(0 : SInf F (Fin n × Fin d))) := by
  intro r _ x
  have h0 : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) r = 0 := by
    funext y; simp [tens]
  rw [h0]
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem lowDegInf_le_fixDeg : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      lowDegInf B G.M R.p ≤ fixDeg B G.M om := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  by_contra hlt
  push_neg at hlt
  have h0 : ∀ f ∈ fockDeg G.M B.ψ B.emb (fixDeg B G.M om), R.p f = 0 := by
    intro f hf
    by_contra hne
    exact Nat.notMem_of_lt_sInf hlt ⟨f, hf, hne⟩
  have hall : ∀ m, ∀ f ∈ fockDeg G.M B.ψ B.emb m, IsKFix B om f → R.p f = 0 := by
    intro m
    induction m with
    | zero => exact fun f hf _ => h0 f (fockDeg_mono _ _ _ (Nat.zero_le _) hf)
    | succ m ih =>
      intro f hf hfix
      by_cases hmD : fixDeg B G.M om ≤ m
      · have hspan := GlobalTheory.T.fixed_fock_degree_span hKP F E σ B a a' G X om om' R Rf hM m hmD f hf hfix
        have hle : Submodule.span ℂ ({g | g ∈ fockDeg G.M B.ψ B.emb m ∧ IsKFix B om g} ∪
            {f₁ | ∃ γ ∈ Lines σ G.W, ∃ g ∈ fockDeg G.M B.ψ B.emb m, IsKFix B om g ∧
              ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁}) ≤ LinearMap.ker R.p := by
          refine Submodule.span_le.2 ?_
          rintro g (⟨hg, hgfix⟩ | ⟨γ, hγ, g₀, hg₀, hg₀fix, hd⟩)
          · exact ih g hg hgfix
          · have h := hM.real.lie γ hγ g₀ (fockDeg_le_pol _ _ _ _ hg₀) 0 (zero_mem _) g 0 hd
              (actsD_zero_weil om' γ) (by rw [ih g₀ hg₀ hg₀fix, map_zero])
            rw [map_zero] at h
            exact h
        exact hle hspan
      · push_neg at hmD
        exact h0 f (fockDeg_mono _ _ _ hmD hf)
  have hcov := GlobalTheory.T.low_part_le_fixed_part_image hKP F E σ B a a' G X om om' R Rf hM
  have hfixbot : (fixPart B G.M om (lowDegInf B G.M R.p)).map R.p = ⊥ := by
    rw [fixPart, Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨g, ⟨hg, hgfix⟩, rfl⟩
    exact hall _ g hg hgfix
  have hne : lowPartInf B G.M R.p ≠ ⊥ := by
    apply lowPartInf_ne_bot
    haveI := hM.real.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have hx' : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; trivial
    obtain ⟨f, hf, rfl⟩ := hx'
    exact ⟨f, hf, hx⟩
  exact hne (eq_bot_iff.2 (hcov.trans hfixbot.le))

end GlobalTheory.IndLine
