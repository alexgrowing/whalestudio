import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

namespace GlobalTheory.ThK.ZFinDerPolL

theorem derL_mem_polData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V,
      derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ ∈ GlobalTheory.ThK.PolData B G.M := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hK hT Φ hΦ γ hγ
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  obtain ⟨D, hDm, hDa⟩ := (GlobalTheory.T.polynomial_datum_action_of_pair hK.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp).1 γ hγ
  have key : ∃ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ y,
      HasDerivAt (fun t => om (γ (Multiplicative.ofAdd t), 1) Φ y) (Ψ y) 0 := by
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := h
      refine ⟨pure (D f) φ, Submodule.subset_span ⟨D f, hDm f hf, φ, hSB, hev, rfl⟩, fun y => ?_⟩
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
      have hR := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd
      exact (hDa f hf (D f)).2 rfl _ hR y
    | zero => exact ⟨0, zero_mem _, fun y => by simpa using hasDerivAt_const (0:ℝ) (0:ℂ)⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨Ψ₁, m₁, d₁⟩ := h₁
      obtain ⟨Ψ₂, m₂, d₂⟩ := h₂
      refine ⟨Ψ₁ + Ψ₂, add_mem m₁ m₂, fun y => ?_⟩
      have h := (d₁ y).add (d₂ y)
      simp only [map_add, Pi.add_apply]
      exact h
    | smul r Φ₁ _ h₁ =>
      obtain ⟨Ψ₁, m₁, d₁⟩ := h₁
      refine ⟨r • Ψ₁, Submodule.smul_mem _ r m₁, fun y => ?_⟩
      simpa [map_smul] using (d₁ y).const_mul r
  obtain ⟨Ψ, hΨ, hd⟩ := key
  have : derL om (fun t => γ (Multiplicative.ofAdd t)) Φ = Ψ := funext fun y => (hd y).deriv
  rw [this]; exact hΨ

end GlobalTheory.ThK.ZFinDerPolL
