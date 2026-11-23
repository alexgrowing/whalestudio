import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCorePf

namespace Formalism.L2.Pj.QAt

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7}

def QBridgeAt (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (CR Ch Ah Cc Ac T c : ℝ) : Prop :=
  ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁)
    (cf : Fin (WeightFamilies.rhoP B CR T c j ka) → Module.Dual K₁ (K₁ ⊗[B.KO] B.Cusp j ka))
    (be : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (s : Fin (WeightFamilies.rhoP B CR T c j ka) → HeightOneSpectrum (𝓞 K₁) → ℝ)
    (a : Fin (WeightFamilies.rhoP B CR T c j ka) → InfinitePlace K₁ → ℝ) (Carch Bdeg : ℝ),
    (∀ x : K₁ ⊗[B.KO] B.Cusp j ka, (∀ i, cf i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun F : B.Cusp j ka => (1 : K₁) ⊗ₜ[B.KO] F) ''
        (WeightFamilies.MggK B CR T c j ka : Set (B.Cusp j ka)))) ∧
    (∀ la, 0 ≤ be la) ∧ (Function.support be).Finite ∧
    (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size ∧
    (∀ i, (Function.support (s i)).Finite) ∧
    (∀ (la : HeightOneSpectrum (𝓞 B.KO)) (w : HeightOneSpectrum (𝓞 K₁)), LiesOver w la →
      ∀ i, ∀ F ∈ B.Mlat j ka, cf i ((1 : K₁) ⊗ₜ[B.KO] F) ≠ 0 →
        -((w.asIdeal.ramificationIdx (𝓞 B.KO) : ℝ) * be la) ≤
          (ordAt w (cf i ((1 : K₁) ⊗ₜ[B.KO] F)) : ℝ) + s i w) ∧
    (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) ∧
    (∀ (σ : InfinitePlace K₁) i, ∀ F ∈ B.Mlat j ka, cf i ((1 : K₁) ⊗ₜ[B.KO] F) ≠ 0 →
      Real.log (σ (cf i ((1 : K₁) ⊗ₜ[B.KO] F))) + a i σ ≤
        Real.log (B.supN j ka (σ.embedding.comp (algebraMap B.KO K₁)) F) + Carch) ∧
    (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
        (Module.finrank ℚ K₁ : ℝ) ≤ Bdeg) ∧
    WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg +
                  Real.log (WeightFamilies.rhoP B CR T c j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size

theorem qat_of_bridge (hL : QuotLocalStatement) (hLD : LenDescentStatement) (large₂ : SizeData₂ D)
    (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ck Ch Ah Cc Ac T c : ℝ)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka))
    (hbr : QBridgeAt large₂ B j ka CR Ch Ah Cc Ac T c) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ B j ka CR Ck Ch Ah Cc Ac T c := by
  intro hCR hOb hn hlast hsize hT hc hTc
  obtain ⟨K₁, _, _, _, cf, be, s, a, Carch, Bdeg, hker, hbe, hbefin, hbesum, hsfin, hint, hconj,
    harch, hdeg, hroom⟩ := hbr
  classical
  refine ⟨Finsupp.ofSupportFinite be hbefin, fun la => by rw [Finsupp.ofSupportFinite_coe]; exact hbe la,
    ?_, fun θ hθ hmean => ?_⟩
  · have hsub : (Function.support fun la => be la * WeightFamilies.lnN B la) ⊆
        ((Finsupp.ofSupportFinite be hbefin).support : Set _) := by
      intro la hla
      rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.ofSupportFinite_coe]
      intro h; apply hla; simp [h]
    have : ((Finsupp.ofSupportFinite be hbefin).sum fun la v => v * WeightFamilies.lnN B la) =
        ∑ᶠ la, be la * WeightFamilies.lnN B la := by
      rw [finsum_eq_sum_of_support_subset _ hsub, Finsupp.sum]
      refine Finset.sum_congr rfl fun la _ => by rw [Finsupp.ofSupportFinite_coe]
    rw [this]; exact hbesum
  · obtain ⟨nn, hloc, hsum⟩ := quotCore_of_local hL hLD B.KO K₁ (B.Cusp j ka) (B.Mlat j ka)
      hlat.fg hlat.span_eq_top (WeightFamilies.MggK B CR T c j ka) θ hθ cf hker be s hbe hbefin hsfin hint
      (B.supN j ka) a (WeightFamilies.PPv D large₂ Ch Ah * ka.size) Carch Bdeg hconj (fun i => hmean i)
      (fun σ i k h => harch σ i (θ k) (θ k).2 h) hdeg
    refine ⟨nn, fun la => hloc la, ?_⟩
    have hρ : (0 : ℝ) ≤ (WeightFamilies.rhoP B CR T c j ka : ℝ) := Nat.cast_nonneg _
    have hρeq : (WeightFamilies.rhoP B CR T c j ka : ℝ) =
        (Module.finrank (𝓞 B.KO) (QuotMW (B.Mlat j ka) (WeightFamilies.MggK B CR T c j ka)) : ℝ) := rfl
    calc _ ≤ _ := hsum
      _ = (WeightFamilies.rhoP B CR T c j ka : ℝ) * (WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg +
            Real.log (WeightFamilies.rhoP B CR T c j ka : ℝ) / 2) := by rw [hρeq]; ring
      _ ≤ (WeightFamilies.rhoP B CR T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cc Ac * ka.size := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hroom hρ

end Formalism.L2.Pj.QAt
