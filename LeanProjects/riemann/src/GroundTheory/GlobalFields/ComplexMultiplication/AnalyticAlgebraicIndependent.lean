import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicPoints

open Filter Topology Set Polynomial
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem meromorphicAt_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem germ_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i, Meromorphic (f i)) :
    germ (fun z ↦ ∑ i ∈ s, f i z) = ∑ i ∈ s, germ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [germ_const, map_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : Meromorphic fun z ↦ ∑ i ∈ s, f i z := fun x ↦
      meromorphicAt_fun_sum s fun i ↦ hf i x
    rw [← ih]
    exact germ_add (hf a) hs

theorem lt_meromorphicOrderAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) {c : ℤ}
    (hc : ∀ i ∈ s, (c : WithTop ℤ) < meromorphicOrderAt (f i) x) :
    (c : WithTop ℤ) < meromorphicOrderAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)]
    exact WithTop.coe_lt_top c
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := meromorphicAt_fun_sum s hf
    have h1 := hc a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    exact lt_of_lt_of_le (lt_min h1 h2) (meromorphicOrderAt_add (hf a) hs)

theorem exists_int_of_real_mul_mem (L : PeriodPair) {r : ℝ} (h : (r : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ a : ℤ, r = a := by
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - r) (n : ℝ) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast]
    linear_combination e)
  exact ⟨m, (sub_eq_zero.1 this.1).symm⟩

theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.2 two_pos).ne'

theorem injective_mk_div_sqrt_two (L : PeriodPair) :
    Function.Injective fun m : ℕ ↦ Torus.mk L ((m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ)) := by
  intro m m' hm
  simp only at hm
  rw [Torus.mk_eq_mk_iff] at hm
  have e : (m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) - (m' : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) =
      ((((m : ℝ) - m') / Real.sqrt 2 : ℝ) : ℂ) * L.ω₁ := by
    push_cast
    ring
  rw [e] at hm
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L hm
  by_contra hne
  have hd : ((m : ℝ) - m') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    exact hd ((div_eq_zero_iff.1 ha).resolve_right (Real.sqrt_pos.2 two_pos).ne')
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hs : Real.sqrt 2 = ((m : ℝ) - m') / a := by
    rw [eq_div_iff ha0]
    rw [div_eq_iff hs2] at ha
    linear_combination (-1 : ℝ) * ha
  exact irrational_sqrt_two ⟨((m : ℚ) - m') / a, by push_cast; exact hs.symm⟩

theorem meromorphicOrderAt_weierstrassP_sqrt_two (L : PeriodPair) {z₀ : ℂ}
    (hz : (Real.sqrt 2 : ℂ) * z₀ + 0 ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul (Real.sqrt 2 : ℂ)).add_const 0
    rw [h1.deriv, mul_one]
    exact sqrt_two_ne_zero
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

theorem ellEval_indep (L : PeriodPair) (p : (weierstrassCurve L).toAffine.FunctionField[X])
    (hp : p ≠ 0) :
    (p.map (ellEval L).toRingHom).eval (germ fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) ≠ 0 := by
  set t : ℂ := (Real.sqrt 2 : ℂ)
  set h : ℂ → ℂ := fun z ↦ ℘[L] (t * z + 0)
  have mh : Meromorphic h := meromorphic_weierstrassP_affine L t 0
  choose f hf hfe using fun i ↦ exists_isEllipticFunction_ellEval_eq L (p.coeff i)
  set n := p.natDegree
  have mt : ∀ i, Meromorphic fun z ↦ f i z * h z ^ i := fun i x ↦
    ((hf i).1 x).mul ((mh x).pow i)
  have heval : (p.map (ellEval L).toRingHom).eval (germ h) =
      germ fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (ellEval_injective L),
      germ_sum _ mt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      germ_mul (hf i).1 (mh.pow (n := i)), germ_pow mh]
    congr 1
    exact hfe i
  intro h0
  rw [heval, germ_eq_zero_iff (fun x ↦ meromorphicAt_fun_sum _ fun i ↦ mt i x)] at h0

  have hfn : ¬ f n =ᶠ[codiscrete ℂ] 0 := by
    intro hz
    have h1 : ellEval L (p.coeff n) = 0 := by
      rw [hfe n, ← germ_zero]
      exact germ_congr (hf n).1 hz
    rw [map_eq_zero_iff _ (ellEval_injective L)] at h1
    exact hp (leadingCoeff_eq_zero.1 h1)

  set bad : Set ℂ := (⋃ i ∈ Finset.range (n + 1), singularSet (f i)) ∪ singularSet (f n)⁻¹
  have hbad : (Torus.mk L '' bad).Finite := by
    rw [image_union, image_iUnion₂]
    refine Finite.union (Finite.biUnion (Finset.finite_toSet _) fun i _ ↦
      finite_image_singularSet L (hf i).1 (hf i).2) ?_
    exact finite_image_singularSet L (hf n).1.inv fun z l hl ↦ by
      simp only [Pi.inv_apply, (hf n).2 z l hl]
  obtain ⟨m, hm⟩ := (hbad.preimage (injective_mk_div_sqrt_two L).injOn).infinite_compl.nonempty
  set z₀ : ℂ := (m : ℂ) * L.ω₁ / t
  have hz₀ : z₀ ∉ bad := fun hb ↦ hm ⟨z₀, hb, rfl⟩
  have hpole : t * z₀ + 0 ∈ L.lattice := by
    have : t * z₀ + 0 = (m : ℤ) • L.ω₁ := by
      simp only [z₀, t, add_zero, zsmul_eq_mul, Int.cast_natCast]
      field_simp [sqrt_two_ne_zero]
    rw [this]
    exact L.lattice.smul_mem (m : ℤ) L.ω₁_mem_lattice
  have han : ∀ i ∈ Finset.range (n + 1), AnalyticAt ℂ (f i) z₀ := fun i hi ↦ by
    by_contra hna
    exact hz₀ (Or.inl (mem_iUnion₂.2 ⟨i, hi, hna⟩))
  have haninv : AnalyticAt ℂ (f n)⁻¹ z₀ := by
    by_contra hna
    exact hz₀ (Or.inr hna)
  have hoh : meromorphicOrderAt h z₀ = -2 := meromorphicOrderAt_weierstrassP_sqrt_two L hpole
  have hon : meromorphicOrderAt (f n) z₀ = 0 := by
    have h1 := (han n (Finset.self_mem_range_succ n)).meromorphicOrderAt_nonneg
    have h2 := haninv.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_inv] at h2
    have hne : meromorphicOrderAt (f n) z₀ ≠ ⊤ := fun ht ↦
      hfn (eventuallyEq_zero_codiscrete_of_nhdsNE (hf n).1 (meromorphicOrderAt_eq_top_iff.1 ht))
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hk] at h1 h2 ⊢
    have : (0 : ℤ) ≤ k := by exact_mod_cast h1
    have : (0 : ℤ) ≤ -k := by exact_mod_cast h2
    have : k = 0 := by omega
    rw [this]
    rfl
  have hterm : ∀ i, meromorphicOrderAt (fun z ↦ f i z * h z ^ i) z₀ =
      meromorphicOrderAt (f i) z₀ + ((i * (-2) : ℤ) : WithTop ℤ) := fun i ↦ by
    rw [show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      meromorphicOrderAt_mul ((hf i).1 z₀) ((mh z₀).pow i), meromorphicOrderAt_pow (mh z₀), hoh]
    congr 1
  have htop : meromorphicOrderAt (fun z ↦ f n z * h z ^ n) z₀ = ((-2 * n : ℤ) : WithTop ℤ) := by
    rw [hterm, hon, zero_add]
    congr 1
    ring
  have hrest : ((-2 * n : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i) z₀ := by
    apply lt_meromorphicOrderAt_sum _ (fun i ↦ mt i z₀)
    intro i hi
    rw [hterm]
    have hi' : i < n := Finset.mem_range.1 hi
    have h0 := (han i (Finset.mem_range.2 (by omega))).meromorphicOrderAt_nonneg
    cases hc : meromorphicOrderAt (f i) z₀ with
    | top =>
      rw [top_add]
      exact WithTop.coe_lt_top _
    | coe k =>
      rw [hc] at h0
      have : (0 : ℤ) ≤ k := by exact_mod_cast h0
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      omega
  have hsum : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ =
      ((-2 * n : ℤ) : WithTop ℤ) := by
    have e : (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) =
        (fun z ↦ f n z * h z ^ n) + fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i := by
      funext z
      simp only [Finset.sum_range_succ, Pi.add_apply]
      ring
    rw [e, meromorphicOrderAt_add_eq_left_of_lt (meromorphicAt_fun_sum _ fun i ↦ mt i z₀)
      (htop ▸ hrest), htop]
  have hzero : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (eventuallyEq_zero_codiscrete_iff.1 h0 z₀)
  rw [hsum] at hzero
  exact WithTop.coe_ne_top hzero

end Elliptic
end GroundTheory.Global
