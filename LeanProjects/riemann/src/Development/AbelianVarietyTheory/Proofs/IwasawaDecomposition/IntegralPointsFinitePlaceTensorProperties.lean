import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

noncomputable section

namespace GlobalTheory.GaugeEx.IntBasis

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem ev_int (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  have h := (algebraMap F (Af F) a).2
  filter_upwards [h] with v hv
  exact hv

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord {d : ℕ}
    (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F := by
  rw [Filter.eventually_all]
  intro k
  exact RestrictedProduct.eventually _ _ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr e k))

theorem eq_sum {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    y = ∑ i, (Algebra.TensorProduct.basis R b).repr y i ⊗ₜ[F] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem mem_intV_iff_basis_repr_mem_integers (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y ∈ _root_.GlobalTheory.GaugeEx.intV b v ↔
      ∀ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F := by
  unfold _root_.GlobalTheory.GaugeEx.intV
  rfl

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem {r : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v}
    (hr : r ∈ v.adicCompletionIntegers F) {e : E}
    (he : ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F) :
    r ⊗ₜ[F] e ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul]
  exact mul_mem hr (he k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' {ι : Type} (s : Finset ι)
    (f : ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    ∑ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_sum, Finsupp.finset_sum_apply]
  exact sum_mem fun i hi => (mem_intV_iff_basis_repr_mem_integers b v (f i)).1 (hf i hi) k

theorem compact_open : IsCompact (intV b v) ∧ IsOpen (intV b v) := by
  let l := (Algebra.TensorProduct.basis (Fv F v) b).equivFun
  have h1 : Continuous l := IsModuleTopology.continuous_of_linearMap l.toLinearMap
  have h2 : Continuous l.symm := by
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap
  let e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) := ⟨l.toEquiv, h1, h2⟩
  have he : intV b v = e ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
    exact isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [he]
  exact ⟨e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hc),
    (isOpen_set_pi Set.finite_univ fun _ _ => ho).preimage e.continuous⟩

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eventually_basis_repr_mem_adicCompletionIntegers {ι : Type} [Finite ι] (e : ι → E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w) (b.repr (e i) k) ∈ w.adicCompletionIntegers F :=
  Filter.eventually_all.2 fun i => _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (e i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eq_sum_basis_repr_tmul_basis (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y = ∑ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).sum_repr y]
  simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem zero_mem_intV : (0 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_zero, Finsupp.zero_apply]
  exact zero_mem _

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem add_mem_intV {y z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E}
    (hy : y ∈ _root_.GlobalTheory.GaugeEx.intV b v) (hz : z ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    y + z ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers] at hy hz ⊢
  intro k
  rw [map_add, Finsupp.add_apply]
  exact add_mem (hy k) (hz k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem intV_subset_intV_of_basis_repr_integral {d' : ℕ} (b' : Module.Basis (Fin d') F E)
    (h : ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b'.repr (b i) k) ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.GaugeEx.intV b v ⊆ _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro y hy
  rw [eq_sum_basis_repr_tmul_basis b v y]
  exact _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b' v _ _ fun i _ =>
    _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b' v
      ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy i) (h i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (_root_.GlobalTheory.GaugeEx.intV b v) ∧ IsOpen (_root_.GlobalTheory.GaugeEx.intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v ∧ (∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, ∀ z ∈ _root_.GlobalTheory.GaugeEx.intV b v, y * z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ y ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ (∀ z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.prV v z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.intV b v = _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro F E _ _ _ _ _ σ d b
  refine ⟨fun v => ?_, ?_, fun z => ?_, fun d' b' => ?_⟩
  · let φ := (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).equivFun
    have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
    have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
    let h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E ≃ₜ (Fin d → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
      { φ.toEquiv with continuous_toFun := hφ, continuous_invFun := hφs }
    have hS : _root_.GlobalTheory.GaugeEx.intV b v =
        h ⁻¹' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))) := by
      ext y
      rw [mem_intV_iff_basis_repr_mem_integers]
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      rfl
    have hO : IsCompact (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :=
      isCompact_iff_compactSpace.mpr (_root_.GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    rw [hS]
    exact ⟨h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hO),
      (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_integer _).preimage h.continuous⟩
  · filter_upwards [_root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (1 : E),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun p : Fin d × Fin d => b p.1 * b p.2),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => σ (b k))] with v hv1 hv2 hv3
    refine ⟨?_, ?_, ?_⟩
    · rw [Algebra.TensorProduct.one_def]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v (one_mem _) hv1
    · intro y hy z hz
      rw [eq_sum_basis_repr_tmul_basis b v y, eq_sum_basis_repr_tmul_basis b v z, Finset.sum_mul_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ =>
        _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun l _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        (mul_mem ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k)
          ((mem_intV_iff_basis_repr_mem_integers b v z).1 hz l)) (hv2 (k, l))
    · intro y hy
      rw [eq_sum_basis_repr_tmul_basis b v y, map_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ => ?_
      simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k) (hv3 k)
  · induction z using TensorProduct.induction_on with
    | zero =>
      exact Filter.Eventually.of_forall fun v => by
        rw [map_zero]
        exact zero_mem_intV b v
    | tmul a e =>
      filter_upwards [RestrictedProduct.eventually _ _ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a),
        _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b e] with v ha he
      simp only [_root_.GlobalTheory.GaugeEx.prV, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v ha he
    | add x y hx hy =>
      filter_upwards [hx, hy] with v hxv hyv
      rw [map_add]
      exact add_mem_intV b v hxv hyv
  · filter_upwards [eventually_basis_repr_mem_adicCompletionIntegers b' (fun k => b k),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => b' k)] with v h h'
    exact Set.Subset.antisymm (intV_subset_intV_of_basis_repr_integral b v b' h)
      (intV_subset_intV_of_basis_repr_integral b' v b h')

end GlobalTheory.GaugeEx.IntBasis
