import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain
open scoped HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.WhitFree.CoefLim

theorem repr_map {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis A b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_linear (L : (R ⊗[F] E) →ₗ[R] R) : Continuous L := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (a c : Fin n) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c :=
  (continuous_id.matrix_elem a c).comp continuous_subtype_val

theorem continuous_trace_pair [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) := by
  have h : (fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))))) =
      fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => ∑ a, ∑ c, (Algebra.trace R (R ⊗[F] E) ∘ₗ LinearMap.mulLeft R (T a c))
        ((B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a) := by
    funext B
    simp [Matrix.trace, Matrix.mul_apply, map_sum]
  rw [h]
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ =>
    (continuous_linear _).comp (continuous_entry σ c a)

end Cont

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_intH_iff (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    B ∈ intH σ b S ↔ ∀ v, v ∉ S → ∀ a i k, (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (a i : Fin n) (k : Fin d),
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr
        (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i)) a i) k =
      (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v := by
    intro v a i k
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin]
    rw [repr_map, repr_map]
    rfl
  simp only [intH, HeckeCharacterZeroLocus.SiegelWeilU.latV, Set.mem_setOf_eq, key]

theorem measurableSet_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intH (n := n) σ b S) := by
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : intH (n := n) σ b S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, ⋂ a : Fin n, ⋂ i : Fin n,
      ⋂ k : Fin d, {B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n | (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F} := by
    ext B
    simp only [mem_intH_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) := Valued.isOpen_valuationSubring _
  have hev : Continuous fun y : HeckeCharacterZeroLocus.SiegelWeilU.Af F => y v := RestrictedProduct.continuous_eval v
  have hsnd : Continuous (fun c : HeckeCharacterZeroLocus.SiegelWeilU.AF F => HeckeCharacterZeroLocus.SiegelWeilU.sndA F c) := continuous_snd
  have hc : Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v :=
    hev.comp (hsnd.comp ((continuous_linear (Finsupp.lapply k ∘ₗ
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr.toLinearMap)).comp (continuous_entry σ a i)))
  exact (hO.preimage hc).measurableSet

theorem eventually_mem_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop, B ∈ intH σ b S := by
  have hfin : ∀ (a i : Fin n) (k : Fin d), {v : HeightOneSpectrum (𝓞 F) |
      ¬ (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F}.Finite :=
    fun a i k => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)).2
  have hall : ∀ (a i : Fin n) (k : Fin d), ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop,
      ∀ v, v ∉ S → (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
    intro a i k
    filter_upwards [Filter.eventually_ge_atTop (hfin a i k).toFinset] with S hS v hv
    by_contra hcon
    exact hv (hS ((hfin a i k).mem_toFinset.2 hcon))
  have hall' := Filter.eventually_all.2 fun a : Fin n => Filter.eventually_all.2 fun i : Fin n =>
    Filter.eventually_all.2 fun k : Fin d => hall a i k
  filter_upwards [hall'] with S hS
  exact (mem_intH_iff σ b S B).2 fun v hv a i k => hS a i k v hv

end Adelic

theorem coefS_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ ψ hψ dx db d b Φ hI T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : Continuous fun B : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp ((continuous_const.mul (continuous_trace_pair σ _)).neg)
  have hf := hI.aestronglyMeasurable.mul hchar.aestronglyMeasurable
  unfold coefS coefN
  refine tendsto_integral_filter_of_dominated_convergence (fun B => ‖starN σ J ψ dx Φ B‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable ((intH (n := n) σ b S).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun B => ?_
    have h1 : ‖(intH (n := n) σ b S).indicator (fun _ => (1 : ℂ)) B‖ ≤ 1 := by
      by_cases h : B ∈ intH (n := n) σ b S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun B => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_intH σ b B] with S hS
    simp only [Set.indicator_of_mem hS, one_mul]
    rfl

end GlobalTheory.CompanionTheory.WhitFree.CoefLim
