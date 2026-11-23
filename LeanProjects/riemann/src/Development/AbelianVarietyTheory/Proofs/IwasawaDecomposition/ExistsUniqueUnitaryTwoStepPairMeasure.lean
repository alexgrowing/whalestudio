import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSectionStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E)

theorem pairOf_mul_frame (J' : Matrix (Fin M) (Fin M) E) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (g h : HA R σ J) (h' : HA R σ J') (hh : FrameRelR R σ J J' B h h')
    (y' : Fin 1 → Fin M → R ⊗[F] E) :
    pairOf R σ J B y (g * h) y' = pairOf R σ J B y g (h' • y') := by
  unfold pairOf
  congr 2
  have h1 : (h' • y') 0 = ((HA.mat R σ J' h' : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (y' 0) := rfl
  have h2 : ((HA.mat R σ J (g * h) : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) =
      ((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) *
      ((HA.mat R σ J h : GL (Fin (M + 1)) (R ⊗[F] E)) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) := rfl
  unfold FrameRelR at hh
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]
  exact congrArg (fun A => Matrix.mulVec (((HA.mat R σ J g : GL (Fin (M + 1)) (R ⊗[F] E)) :
    Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * A) (y' 0)) hh

variable [TopologicalSpace R] [FiniteDimensional F E] [IsTopologicalRing R]

theorem continuous_pairOf : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
    (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun a => ?_
  fin_cases a
  · exact (by fun_prop : Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => p.1 0)
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end

theorem twoStep_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → ∃! N, TwoStep R σ J x B m m' N := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ M J x a B J' m m' hd horb hm hm' hinv
  obtain ⟨-, ⟨e, he, -⟩, -⟩ := GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ R M J x a B J' hd
  obtain ⟨-, s₀, hs₀m, hs₀⟩ := GlobalTheory.T.measurableSet_orbit_exists_measurable_section (HA R σ J) (Fin 1 → Fin (M + 1) → R ⊗[F] E)
    (ratTup (F := F) R x)
  have hP : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J ×
      (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 :=
    (continuous_pairOf R σ J B).measurable
  have hΦ : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin 1 → Fin M → R ⊗[F] E) =>
      pairOf R σ J B p.1 (s₀ p.1) p.2 :=
    hP.comp (measurable_fst.prodMk ((hs₀m.comp measurable_fst).prodMk measurable_snd))
  have hex : TwoStep R σ J x B m m' ((m.prod m').map fun p => pairOf R σ J B p.1 (s₀ p.1) p.2) := by
    intro f hf s hs
    rw [lintegral_map hf hΦ, lintegral_prod (fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) ×
      (Fin 1 → Fin M → R ⊗[F] E) => f (pairOf R σ J B p.1 (s₀ p.1) p.2)) (hf.comp hΦ).aemeasurable]
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := horb
    filter_upwards [hae] with y hy
    have hst : (s₀ y)⁻¹ * s y ∈ Hstab R σ J x := by
      change ((s₀ y)⁻¹ * s y) • ratTup (F := F) R x = ratTup (F := F) R x
      rw [mul_smul, hs y hy, inv_smul_eq_iff, hs₀ y hy]
    have hfac : s y = s₀ y * ((s₀ y)⁻¹ * s y) := by group
    have hk : Measurable fun y' => f (pairOf R σ J B y (s₀ y) y') :=
      (hf.comp hΦ).comp measurable_prodMk_left
    have hsm : Measurable fun X : Fin 1 → Fin M → R ⊗[F] E => e ⟨_, hst⟩ • X :=
      (continuous_const_smul _).measurable
    calc ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂m'
        = ∫⁻ y', f (pairOf R σ J B y (s₀ y) y') ∂(m'.map fun X => e ⟨_, hst⟩ • X) := by
          rw [hinv]
      _ = ∫⁻ y', f (pairOf R σ J B y (s₀ y) (e ⟨_, hst⟩ • y')) ∂m' := lintegral_map hk hsm
      _ = ∫⁻ y', f (pairOf R σ J B y (s y) y') ∂m' := by
          refine lintegral_congr fun y' => ?_
          rw [← pairOf_mul_frame R σ J B J' y (s₀ y) _ _ (he ⟨_, hst⟩), ← hfac]
  refine ⟨_, hex, fun N hN => ?_⟩
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    hN _ (measurable_one.indicator hA) s₀ hs₀, hex _ (measurable_one.indicator hA) s₀ hs₀]

end GlobalTheory.GaugeEx
