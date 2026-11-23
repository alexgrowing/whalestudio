import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GermRateLow (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

def GermRateTop (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s = S.G.r + 2 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

theorem germRate_of (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (hL : GermRateLow S v) (hT : GermRateTop S v) :
    GermRate S v := by
  intro ε hε b s hb hs hbs
  rcases Nat.lt_or_ge (b + s) (S.G.r + 2) with h | h
  · exact hL ε hε b s hb hs (by omega)
  · exact hT ε hε b s hb hs (by omega)

end loc

def GermRateLowB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateLow (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

def GermRateTopB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateTop (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

theorem germRateB_of (hL : GermRateLowB) (hT : GermRateTopB) : GermRateB := by
  intro hA Cb
  obtain ⟨c1, h1⟩ := hL hA Cb
  obtain ⟨c2, h2⟩ := hT hA Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  exact germRate_of _ v (h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v)
    (h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v)

end

end Formalism.FourierDecayAlt.P.GermRateSplit

theorem Formalism.FourierDecayAlt.P.germ_rate_bound_of_split :
    Formalism.FourierDecayAlt.P.GermRateSplit.GermRateLowB → Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB → Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.GermRateSplit.germRateB_of
