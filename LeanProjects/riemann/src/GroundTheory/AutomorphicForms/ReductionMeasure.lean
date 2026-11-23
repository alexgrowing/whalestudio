import Mathlib
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

instance secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  have := GroundTheory.Global.countable_numberField K
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      SecondCountableTopology ↥(v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v =>
    inferInstanceAs (SecondCountableTopology (v.adicCompletionIntegers K))
  have hemb := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
  set O : Set (FiniteAdeleRing (𝓞 K) K) :=
    Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite) with hO
  have hOsc : SecondCountableTopology O :=
    hemb.toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hOopen : IsOpen O := hemb.isOpen_range
  have hOmem : ∀ x : FiniteAdeleRing (𝓞 K) K, x ∈ O ↔
      x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := fun x => by
    constructor
    · rintro ⟨y, rfl⟩ v
      exact (y v).2
    · intro h
      exact ⟨fun v => ⟨x v, h v⟩, rfl⟩
  let U : K → Set (FiniteAdeleRing (𝓞 K) K) := fun k => (· - algebraMap K _ k) ⁻¹' O
  have hU : ∀ k, SecondCountableTopology (U k) := fun k => by
    have he : IsEmbedding (Set.codRestrict
        ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)) ∘
          (Subtype.val : U k → FiniteAdeleRing (𝓞 K) K)) O fun x => x.2) :=
      ((Homeomorph.subRight (algebraMap K (FiniteAdeleRing (𝓞 K) K) k)).isEmbedding.comp
        IsEmbedding.subtypeVal).codRestrict _ _
    exact he.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
    (fun k => hOopen.preimage (continuous_sub_right _)) ?_
  · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles x
    exact ⟨k, (hOmem _).2 hk⟩

instance secondCountableTopology_adeleRing : SecondCountableTopology 𝔸[K] :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance secondCountableTopology_matrix {R : Type*} [TopologicalSpace R] [SecondCountableTopology R]
    {n : ℕ} : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))

instance measurableSpace_adelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.AdelicGL K n) := borel _

instance borelSpace_adelicGL {n : ℕ} : BorelSpace (AdelicGLn.AdelicGL K n) := ⟨rfl⟩

instance measurableSpace_finiteAdelicGL {n : ℕ} : MeasurableSpace (AdelicGLn.FiniteAdelicGL K n) :=
  borel _

instance borelSpace_finiteAdelicGL {n : ℕ} : BorelSpace (AdelicGLn.FiniteAdelicGL K n) := ⟨rfl⟩

instance measurableSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    MeasurableSpace (GL (Fin n) w.Completion) :=
  borel _

instance borelSpace_GL_infinitePlace {n : ℕ} (w : InfinitePlace K) :
    BorelSpace (GL (Fin n) w.Completion) := ⟨rfl⟩

def infFinEquiv {n : ℕ} : AdelicGLn.AdelicGL K n ≃ₜ*
    (Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n :=
  (AdelicGLn.prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (AdelicGLn.infiniteEquiv K n).toMulEquiv (MulEquiv.refl _)
      continuous_toFun :=
        ((AdelicGLn.infiniteEquiv K n).continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun :=
        ((AdelicGLn.infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk continuous_snd }

theorem infFinEquiv_apply_fst {n : ℕ} (g : AdelicGLn.AdelicGL K n) (w : InfinitePlace K) :
    (infFinEquiv g).1 w = infAt w g := rfl

theorem infFinEquiv_apply_snd {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    (infFinEquiv g).2 = (AdelicGLn.prodEquiv K n g).2 := rfl

theorem measure_lt_top_of_forall_mem {n : ℕ} (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] {E : Set (AdelicGLn.AdelicGL K n)}
    (S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion))
    (hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤)
    {F : Set (AdelicGLn.FiniteAdelicGL K n)} (hF : IsCompact F)
    (hE : ∀ g ∈ E, (∀ w, infAt w g ∈ S w) ∧ (AdelicGLn.prodEquiv K n g).2 ∈ F) : μ E < ⊤ := by
  set e := infFinEquiv (K := K) (n := n) with he
  set ρ : Measure ((Π w : InfinitePlace K, GL (Fin n) w.Completion) × AdelicGLn.FiniteAdelicGL K n) :=
    (Measure.pi fun w => (Measure.haar : Measure (GL (Fin n) w.Completion))).prod
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) with hρ
  have hν : (Measure.map e μ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ e.toMulEquiv e.continuous e.symm.continuous
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map e μ) ρ
  set T := (Set.univ.pi S) ×ˢ F with hT
  have hET : E ⊆ e ⁻¹' T := fun g hg => ⟨fun w _ => (hE g hg).1 w, (hE g hg).2⟩
  have hmap : μ (e ⁻¹' T) = Measure.map e μ T :=
    (e.toHomeomorph.toMeasurableEquiv.map_apply T).symm
  have hρT : ρ T = (∏ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w)) *
      (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) F := by
    rw [hρ, hT, Measure.prod_prod, Measure.pi_pi]
  set c := (Measure.map e μ).haarScalarFactor ρ with hc
  calc μ E ≤ μ (e ⁻¹' T) := measure_mono hET
    _ = Measure.map e μ T := hmap
    _ = (c • ρ) T := by rw [← heq]
    _ < ⊤ := by
      rw [Measure.smul_apply, hρT, ENNReal.smul_def, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top
        (ENNReal.prod_lt_top fun w _ => hS w) hF.measure_lt_top)

end Reduction

end

end GroundTheory.Automorphic
