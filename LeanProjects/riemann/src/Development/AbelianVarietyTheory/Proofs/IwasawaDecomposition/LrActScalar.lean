import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitude

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.Polar

theorem qR_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (z : Fin M → R ⊗[F] E) :
    qR R σ J (algebraMap R (R ⊗[F] E) r • z) = r * r * qR R σ J z := by
  have hs : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  have h : hR R σ J (algebraMap R (R ⊗[F] E) r • z) (algebraMap R (R ⊗[F] E) r • z)
      = (r * r) • hR R σ J z z := by
    rw [Algebra.smul_def (r * r), map_mul]
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [qR, h, map_smul, smul_eq_mul]
  ring

theorem lrAct_scalar {S : Type} [CommRing S] {n M : ℕ} (c : S) (X : Fin n → Fin M → S) :
    lrAct (c • (1 : Matrix (Fin M) (Fin M) S)) 1 X = c • X := by
  funext a i
  simp [lrAct, Matrix.smul_mulVec, Matrix.one_apply]

theorem polar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J (tupMeas lam 1 M) ν β m → ∀ (W : Set R) (ρ : R → R), MeasurableSet W → (∀ b ∈ W, IsUnit (ρ b) ∧ ρ b * ρ b * β = b) → ∀ f : (Fin 1 → Fin M → R ⊗[F] E) → ℝ≥0∞, Measurable f → (∀ X, qR R σ J (X 0) ∉ W → f X = 0) → ∫⁻ X, f X ∂(tupMeas lam 1 M) = ∫⁻ b in W, ((modu (R ⊗[F] E) (algebraMap R (R ⊗[F] E) (ρ b) ^ M) * (modu R (ρ b * ρ b))⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ X, f (algebraMap R (R ⊗[F] E) (ρ b) • X) ∂m ∂ν := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J lam ν β m hlam hν hβ hfib W ρ hW hρ f hf hf0
  obtain ⟨fib, hfam, hm⟩ := id hfib
  have h2 := hfam.2.1 f hf
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hW]
  refine lintegral_congr fun b => ?_
  by_cases hb : b ∈ W
  · rw [Set.indicator_of_mem hb]
    obtain ⟨hr, hrb⟩ := hρ b hb
    set c : R ⊗[F] E := algebraMap R (R ⊗[F] E) (ρ b) with hc
    have hdet : (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))).det = c ^ M := by
      simp
    have hcu : IsUnit c := hr.map _
    have h1 := GlobalTheory.GaugeEx.fibAt_similitude F E σ R hN M J J lam ν β (ρ b * ρ b) m
      (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hlam hν (by rw [hdet]; exact hcu.pow M)
      (hr.mul hr) (fun z => by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact qR_scalar σ R J (ρ b) z) hfib
    rw [hrb, hdet] at h1
    have hbu : IsUnit b := hrb ▸ (hr.mul hr).mul hβ
    have h3 := (GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hN M J _ ν b _ hν hbu h1).2.2 (fib b)
      ⟨fib, hfam, rfl⟩
    have hl : lrAct (n := 1) (c • (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) 1 = fun X => c • X :=
      funext fun X => lrAct_scalar c X
    have hcont : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => c • X := continuous_const_smul c
    rw [h3, hl, lintegral_smul_measure, lintegral_map hf hcont.measurable]
    rfl
  · rw [Set.indicator_of_notMem hb]
    have h1 := hfam.1 b
    have hae : f =ᵐ[fib b] 0 := by
      refine measure_mono_null (fun X hX => ?_) h1
      intro hX'
      apply hX
      apply hf0
      have : qR R σ J (X 0) = b := hX'.1
      rw [this]; exact hb
    rw [lintegral_congr_ae hae]
    simp

end GlobalTheory.GaugeEx.Polar
