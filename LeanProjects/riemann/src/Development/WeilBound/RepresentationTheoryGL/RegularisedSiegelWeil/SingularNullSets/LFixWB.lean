import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]

variable (F E) in

abbrev bE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

abbrev bV (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (bE F E)

theorem bV_apply (v : HeightOneSpectrum (𝓞 F)) (k : Fin (Module.finrank F E)) : bV (E := E) v k = 1 ⊗ₜ[F] bE F E k :=
  Algebra.TensorProduct.basis_apply _ _

theorem crd_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) (k : Fin (Module.finrank F E)) :
    (bV v).repr (a ⊗ₜ[F] e) k = a * algebraMap F (Fv F v) ((bE F E).repr e k) := by
  simp [bV, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem exists_den (x : E) : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

def den (x : E) : ℤ := Classical.choose (exists_den x)

theorem den_ne (x : E) : den x ≠ 0 := (Classical.choose_spec (exists_den x)).1

theorem den_int (x : E) : IsIntegral ℤ ((den x : E) * x) := (Classical.choose_spec (exists_den x)).2

variable (F E) in

def trM : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F := fun i j => Algebra.trace F E (bE F E i * bE F E j)

theorem trM_det : (trM F E).det ≠ 0 := by
  have h := Algebra.discr_not_zero_of_basis F (bE F E)
  rw [Algebra.discr_def] at h
  convert h using 2
  ext i j
  simp [trM, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

def IsGood (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)),
      algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F) ∧
    algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F

theorem eventually_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

theorem eventually_good : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsGood F E v :=
  (eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and (eventually_int _))))

theorem eventually_coord (y : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ k, algebraMap F (Fv F v) ((bE F E).repr y k) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun _ => eventually_int _

variable {v : HeightOneSpectrum (𝓞 F)}

theorem IsGood.half (hv : IsGood F E v) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := hv.2.2.2.2

theorem IsGood.ogen (hv : IsGood F E v) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
  hv.1 l k

theorem IsGood.deninv (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F := hv.2.1 k

theorem IsGood.trinv (hv : IsGood F E v) (i j : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F := hv.2.2.1 i j

theorem IsGood.trb (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F := hv.2.2.2.1 k

theorem one_tmul_b_mem (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    (1 : Fv F v) ⊗ₜ[F] bE F E k ∈ intLoc F E v := by
  have hN : (den (bE F E k) : F) ≠ 0 := by exact_mod_cast den_ne (bE F E k)
  let o : 𝓞 E := ⟨(den (bE F E k) : E) * bE F E k, den_int (bE F E k)⟩
  have ho : (o : E) = (den (bE F E k) : E) * bE F E k := rfl
  have e : (1 : Fv F v) ⊗ₜ[F] bE F E k = algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ⊗ₜ[F] (o : E) := by
    rw [ho]
    have : ((den (bE F E k) : E) * bE F E k) = (den (bE F E k) : F) • bE F E k := by
      rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hN,
      map_one]
  rw [e]
  exact tmul_mem_intLoc (hv.deninv k) o

theorem tmul_one_mem {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) ha (1 : 𝓞 E)

theorem mem_intLoc_iff (hv : IsGood F E v) (z : Fv F v ⊗[F] E) :
    z ∈ intLoc F E v ↔ ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hz
    refine intLoc_induction (p := fun z => ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F) (fun a ha x k => ?_)
      (fun k => by simp) (fun y z hy hz k => by rw [map_add, Finsupp.add_apply]; exact add_mem (hy k) (hz k))
      (fun y hy k => by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)) hz
    rw [crd_tmul]
    refine mul_mem ha ?_
    let L : 𝓞 E →+ F := ((Finsupp.applyAddHom k).comp (bE F E).repr.toLinearMap.toAddMonoidHom).comp
      (algebraMap (𝓞 E) E).toAddMonoidHom
    have e : L x = ∑ l, ((RingOfIntegers.basis E).repr x l) • L (RingOfIntegers.basis E l) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      rw [map_sum]
      simp only [map_zsmul]
    change algebraMap F (Fv F v) (L x) ∈ _
    rw [e, map_sum]
    refine sum_mem fun l _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (hv.ogen l k) _
  · intro h
    rw [← (bV v).sum_repr z]
    refine sum_mem fun k _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : (bV v).repr z k ⊗ₜ[F] bE F E k = ((bV v).repr z k ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] bE F E k) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact mul_mem (tmul_one_mem (h k)) (one_tmul_b_mem hv k)

theorem trace_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F (Fv F v) (Algebra.trace F E e) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (bV v), Algebra.trace_eq_matrix_trace (bE F E), Matrix.trace, Matrix.trace,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    bV_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, crd_tmul]

theorem trace_eq_sum (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z =
      ∑ k, (bV v).repr z k * algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) := by
  conv_lhs => rw [← (bV v).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, trace_tmul]

theorem trace_mem (hv : IsGood F E v) {z : Fv F v ⊗[F] E} (hz : z ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  rw [trace_eq_sum]
  exact sum_mem fun k _ => mul_mem (((mem_intLoc_iff hv z).1 hz) k) (hv.trb k)

theorem mem_of_trace (hv : IsGood F E v) (c : Fv F v ⊗[F] E)
    (h : ∀ t ∈ intLoc F E v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * t) ∈ v.adicCompletionIntegers F) :
    c ∈ intLoc F E v := by
  classical
  set u : Fin (Module.finrank F E) → Fv F v := fun j => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (1 ⊗ₜ[F] bE F E j))
  have hu : ∀ j, u j ∈ v.adicCompletionIntegers F := fun j => h _ (one_tmul_b_mem hv j)
  have hu' : ∀ j, u j = ∑ l, (bV v).repr c l * algebraMap F (Fv F v) (trM F E l j) := by
    intro j
    simp only [u]
    conv_lhs => rw [← (bV v).sum_repr c]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      trace_tmul]
    rfl
  have hT : trM F E * (trM F E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 trM_det)
  refine (mem_intLoc_iff hv c).2 fun k => ?_
  have e : (bV v).repr c k = ∑ j, u j * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) := by
    have h1 : ∀ l, ∑ j, algebraMap F (Fv F v) (trM F E l j) * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) =
        if l = k then 1 else 0 := by
      intro l
      have := congrFun (congrFun hT l) k
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp_rw [← map_mul, ← map_sum, this]
      split_ifs <;> simp
    simp_rw [hu', Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h1]
    simp
  rw [e]
  exact sum_mem fun j _ => mul_mem (hu j) (hv.trinv j k)

end PositivityTheory.Rg.Rsw.L.LFixW

end
