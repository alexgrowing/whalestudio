import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresUniqueAe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QTie

theorem isUnit_of_tmul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {R : Type} [CommRing R] [Algebra F R] {c : R}
    (h : IsUnit (c ⊗ₜ[F] (1 : E))) : IsUnit c := by
  obtain ⟨bb, -, -⟩ := GlobalTheory.CompanionTheory.SW.OneHerm.exists_basis hσ
  have h1 := h.map (Algebra.norm R (S := R ⊗[F] E))
  have h2 := Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) c
  rw [Algebra.TensorProduct.algebraMap_apply] at h2
  have h3 : Algebra.norm R (c ⊗ₜ[F] (1 : E)) = c ^ 2 := by simpa using h2
  rw [h3] at h1
  exact (isUnit_pow_iff two_ne_zero).mp h1

def hermAdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : R ≃+ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf R σ
  left_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf_hermScal R hσ
  right_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ
  map_add' a b := by
    apply Subtype.ext
    ext i j
    change (a + b) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] (1 : E)
    rw [TensorProduct.add_tmul]

end GlobalTheory.CompanionTheory.SW.QTie

open GlobalTheory.CompanionTheory.SW.OneHerm GlobalTheory.CompanionTheory.SW.QTie in

theorem GlobalTheory.CompanionTheory.SW.QTie.fib_eq_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} fib → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → ∀ c : R, IsUnit c → fib c = m (hermScal R σ c) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR μ ν hμ hν hνu hμu fib hfib m hm c hc
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor 1 M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  let q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)
  have hq : ∀ X, q X = hermHalf R σ (g X) := by
    intro X
    change _ = algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((g X : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)
    rw [← hgf X]
    rfl
  have hgq : ∀ X, g X = hermScal R σ (q X) := by
    intro X
    rw [hq, hermScal_hermHalf R hσ]
  have hdet : ∀ S : HermR R σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det ↔ IsUnit (hermHalf R σ S) := by
    intro S
    have hS : ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det = (hermHalf R σ S) ⊗ₜ[F] (1 : E) := by
      conv_lhs => rw [← hermScal_hermHalf R hσ S]
      rw [Matrix.det_fin_one]
      rfl
    rw [hS]
    refine ⟨isUnit_of_tmul_one hσ, fun h => ?_⟩
    exact h.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hU : {X | IsUnit (gramR R σ J X).det} = {X | IsUnit (q X)} := by
    ext X
    simp only [Set.mem_setOf_eq]
    rw [hgf X, hdet, hq]
  have hUnull : μ ({X | IsUnit (gramR R σ J X).det}ᶜ) = 0 := by
    rw [hU]
    exact hμu
  have hemb : MeasurableEmbedding (hermScal R σ) := (hermHomeo R hσ).measurableEmbedding
  have hν' : (ν.map (hermScal R σ)).IsAddHaarMeasure :=
    (hermAdd hσ R).isAddHaarMeasure_map ν (continuous_hermScal R σ) (continuous_hermHalf R σ)
  let m' : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E) := fun S =>
    if IsUnit (hermHalf R σ S) then fib (hermHalf R σ S) else 0
  have hm'u : ∀ s : R, IsUnit s → m' (hermScal R σ s) = fib s := by
    intro s hs
    simp only [m', hermHalf_hermScal R hσ, hs, if_true]
  have hm' : IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m' := by
    refine ⟨?_, ?_, ?_⟩
    · intro S
      by_cases hS : IsUnit (hermHalf R σ S)
      · have : m' S = fib (hermHalf R σ S) := by simp only [m', hS, if_true]
        rw [this]
        refine measure_mono_null ?_ (hf1 (hermHalf R σ S))
        intro X hX hX'
        apply hX
        have hqX : q X = hermHalf R σ S := by simpa using hX'.1
        refine ⟨?_, ?_⟩
        · change gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))
          rw [hgf X, hgq X, hqX, hermScal_hermHalf R hσ]
        · change IsUnit (gramR R σ J X).det
          rw [hgf X, hdet, ← hq, hqX]
          exact hS
      · have : m' S = 0 := by simp only [m', hS, if_false]
        rw [this]
        rfl
    · intro φ hφ
      rw [hemb.lintegral_map]
      have h1 : ∫⁻ v in {X | IsUnit (gramR R σ J X).det}, φ v ∂μ = ∫⁻ v in Set.univ, φ v ∂μ := by
        rw [Measure.restrict_univ]
        rw [Measure.restrict_eq_self_of_ae_mem]
        exact measure_eq_zero_iff_ae_notMem.mp hUnull |>.mono fun x hx => by simpa using hx
      rw [h1, hf2 φ hφ]
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ s ∂ν, IsUnit s := by
        rw [ae_iff]
        exact hνu
      filter_upwards [hae] with s hs
      rw [hm'u s hs]
    · intro φ hφ hφc hφs
      obtain ⟨hi, hcont⟩ := hf3 φ hφ hφc (Set.subset_univ _)
      refine ⟨fun S hS => ?_, ?_⟩
      · have hS' : IsUnit (hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (hermHalf R σ S) := by simp only [m', hS', if_true]
        rw [this]
        exact hi _ hS'
      · have hmaps : Set.MapsTo (hermHalf R σ) {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} {c | IsUnit c} :=
          fun S hS => (hdet S).mp hS
        refine (hcont.comp (continuous_hermHalf R σ).continuousOn hmaps).congr ?_
        intro S hS
        have hS' : IsUnit (hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (hermHalf R σ S) := by simp only [m', hS', if_true]
        simp only [this, Function.comp]
  have := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR 1 μ (ν.map (hermScal R σ)) m hμ hν' hm m' hm'
    (hermScal R σ c)
  rw [this, hm'u c hc]
