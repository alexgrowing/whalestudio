import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ResidueFieldTeichmullerLiftExists
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixAbs

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

section Closure

variable {S K : Type} [CommRing S] [NormedField K] [IsUltrametricDist K] {p : ℕ} (i : S →+* K)

private structure Gd (p : ℕ) (i : S →+* K) : Prop where
  pos : 0 < ‖(p : K)‖
  lt : ‖(p : K)‖ < 1
  le : ∀ y, ‖i y‖ ≤ 1
  un : ∀ y, ¬ (p : S) ∣ y → IsUnit y

variable {i}

private theorem norm_unit {T : Type} [CommRing T] {f : T →+* K} (h : ∀ y, ‖f y‖ ≤ 1) {y : T} (hy : IsUnit y) :
    ‖f y‖ = 1 := by
  obtain ⟨z, hz⟩ := hy.exists_right_inv
  have e : ‖f y‖ * ‖f z‖ = 1 := by rw [← norm_mul, ← map_mul, hz, map_one, norm_one]
  nlinarith [h y, h z, norm_nonneg (f y), norm_nonneg (f z)]

private theorem norm_of_dvd {T : Type} [CommRing T] {f : T →+* K} (h : ∀ y, ‖f y‖ ≤ 1) {n : ℕ} {y : T}
    (hy : (p : T) ^ n ∣ y) : ‖f y‖ ≤ ‖(p : K)‖ ^ n := by
  obtain ⟨z, rfl⟩ := hy
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (h z)

private theorem Gd.dvd_of_lt (h : Gd p i) (n : ℕ) : ∀ y : S, ‖i y‖ < ‖(p : K)‖ ^ n → (p : S) ^ (n + 1) ∣ y := by
  have h0 : ∀ y : S, ‖i y‖ < 1 → (p : S) ∣ y := fun y hy => by
    by_contra hc
    exact hy.ne (norm_unit h.le (h.un y hc))
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro y hy
    obtain ⟨z, rfl⟩ := h0 y (hy.trans_le (pow_le_one₀ h.pos.le h.lt.le))
    rw [map_mul, map_natCast, norm_mul, pow_succ'] at hy
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih z (lt_of_mul_lt_mul_left hy h.pos.le))

private theorem Gd.dvd_of_le (h : Gd p i) (n : ℕ) (y : S) (hy : ‖i y‖ ≤ ‖(p : K)‖ ^ n) : (p : S) ^ n ∣ y := by
  cases n with
  | zero => simp
  | succ n => exact h.dvd_of_lt n y (hy.trans_lt (pow_lt_pow_right_of_lt_one₀ h.pos h.lt n.lt_succ_self))

private theorem Gd.norm_map_le (h : Gd p i) (φ : S →+* S) (y : S) : ‖i (φ y)‖ ≤ ‖i y‖ := by
  have key : ∀ n, ‖i y‖ < ‖(p : K)‖ ^ n → ‖i (φ y)‖ ≤ ‖(p : K)‖ ^ (n + 1) := fun n hn => by
    refine norm_of_dvd h.le ?_
    simpa using map_dvd φ (h.dvd_of_lt n y hn)
  by_contra hc
  push Not at hc
  have all : ∀ n, ‖i (φ y)‖ ≤ ‖(p : K)‖ ^ n := fun n => by
    induction n with
    | zero => simpa using h.le _
    | succ n ih => exact key n (hc.trans_le ih)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ((norm_nonneg _).trans_lt hc) h.lt
  exact absurd (all n) (not_le.2 hn)

variable (i) in
private abbrev Cl : Subring K := i.range.topologicalClosure

private theorem mem_Cl {x : K} : x ∈ Cl i ↔ ∀ ε > 0, ∃ y, ‖x - i y‖ < ε := by
  change x ∈ closure (i.range : Set K) ↔ _
  rw [RingHom.coe_range, Metric.mem_closure_range_iff]
  simp only [dist_eq_norm]

variable (i) in
private def inc : S →+* Cl i := i.codRestrict _ fun y => i.range.le_topologicalClosure ⟨y, rfl⟩

private theorem inc_coe (y : S) : (inc i y : K) = i y := rfl

private theorem dense_inc : DenseRange (inc i) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, hy⟩ := mem_Cl.1 x.2 ε hε
  exact ⟨y, by rwa [Subtype.dist_eq, dist_eq_norm]⟩

private theorem closed_Cl : IsClosed (Cl i : Set K) := i.range.isClosed_topologicalClosure

private theorem Gd.cl_le (h : Gd p i) (x : Cl i) : ‖(Cl i).subtype x‖ ≤ 1 :=
  dense_inc.induction_on x (isClosed_le (by fun_prop) continuous_const) h.le

private theorem Gd.cl_dvd (h : Gd p i) (x : Cl i) (hx : ‖(x : K)‖ < 1) : (p : Cl i) ∣ x := by
  have hp : (p : K) ≠ 0 := norm_pos_iff.1 h.pos
  have : (x : K) / p ∈ Cl i := by
    refine mem_Cl.2 fun ε hε => ?_
    obtain ⟨y, hy⟩ := mem_Cl.1 x.2 (min (ε * ‖(p : K)‖) 1) (lt_min (mul_pos hε h.pos) one_pos)
    have h1 : ‖i y‖ < ‖(p : K)‖ ^ 0 := by
      have e : i y = x + -(x - i y) := by ring
      rw [e, pow_zero]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx ?_)
      rw [norm_neg]
      exact hy.trans_le (min_le_right _ _)
    obtain ⟨z, rfl⟩ := h.dvd_of_lt 0 y h1
    refine ⟨z, ?_⟩
    have e : (x : K) / p - i z = (x - i ((p : S) ^ (0 + 1) * z)) / p := by
      simp only [map_mul, map_natCast, zero_add, pow_one]
      field_simp
    rw [e, norm_div, div_lt_iff₀ h.pos]
    exact hy.trans_le (min_le_left _ _)
  refine ⟨⟨_, this⟩, Subtype.ext ?_⟩
  push_cast
  field_simp

private theorem Gd.cl_unit (h : Gd p i) (x : Cl i) (hx : ¬ (p : Cl i) ∣ x) : IsUnit x := by
  have h1 : ‖(x : K)‖ = 1 := le_antisymm (h.cl_le x) (not_lt.1 fun hc => hx (h.cl_dvd x hc))
  have h0 : (x : K) ≠ 0 := norm_pos_iff.1 (h1 ▸ one_pos)
  have : (x : K)⁻¹ ∈ Cl i := by
    refine mem_Cl.2 fun ε hε => ?_
    obtain ⟨y, hy⟩ := mem_Cl.1 x.2 (min ε 1) (lt_min hε one_pos)
    have h2 : ¬ ‖i y‖ < 1 := fun hc => by
      have e : (x : K) = (x - i y) + i y := by ring
      rw [e] at h1
      exact ((IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hy.trans_le (min_le_right _ _)) hc)).ne h1
    have h3 : IsUnit y := h.un y fun hd => h2 <| by
      have := norm_of_dvd (n := 1) h.le (by simpa using hd)
      rw [pow_one] at this
      exact this.trans_lt h.lt
    obtain ⟨z, hz⟩ := h3.exists_right_inv
    have hz' : i y * i z = 1 := by rw [← map_mul, hz, map_one]
    refine ⟨z, ?_⟩
    have e : (x : K)⁻¹ - i z = -(x - i y) * (x : K)⁻¹ * i z := by
      field_simp
      linear_combination (-1 : K) * hz'
    rw [e, norm_mul, norm_mul, norm_neg, norm_inv, h1, inv_one, mul_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) (h.le z)).trans_lt (hy.trans_le (min_le_left _ _))
  exact IsUnit.of_mul_eq_one ⟨_, this⟩ (Subtype.ext (mul_inv_cancel₀ h0))

private theorem Gd.cl (h : Gd p i) : Gd p (Cl i).subtype := ⟨h.pos, h.lt, h.cl_le, h.cl_unit⟩

private theorem Gd.mem_iff (h : Gd p i) (n : ℕ) (y : S) :
    y ∈ Ideal.span {(p : S) ^ n} ↔ ‖i y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.mem_span_singleton]
  exact ⟨norm_of_dvd h.le, h.dvd_of_le n y⟩

private theorem Gd.cl_prime (h : Gd p i) : Prime (p : Cl i) := by
  refine ⟨fun h0 => ?_, fun hu => ?_, fun a b hab => ?_⟩
  · have := congrArg (Cl i).subtype h0
    rw [map_natCast, map_zero] at this
    exact norm_pos_iff.1 h.pos this
  · have := norm_unit h.cl_le hu
    rw [map_natCast] at this
    exact h.lt.ne this
  · by_contra hc
    push Not at hc
    have h1 := norm_unit h.cl_le ((h.cl_unit a hc.1).mul (h.cl_unit b hc.2))
    have h2 := norm_of_dvd (n := 1) h.cl_le (by simpa using hab)
    rw [h1, pow_one] at h2
    exact h.lt.not_ge h2

private theorem Gd.approx (h : Gd p i) (x : Cl i) (n : ℕ) :
    ∃ y : S, x - inc i y ∈ Ideal.span {(p : Cl i) ^ n} := by
  obtain ⟨y, hy⟩ := mem_Cl.1 x.2 _ (pow_pos h.pos n)
  exact ⟨y, (h.cl.mem_iff n _).2 hy.le⟩

private theorem Gd.cl_complete [CompleteSpace K] (h : Gd p i) :
    IsAdicComplete (Ideal.span {(p : Cl i)}) (Cl i) := by
  have hm : ∀ (n : ℕ) (a b : Cl i), a ≡ b [SMOD (Ideal.span {(p : Cl i)} ^ n • ⊤ : Submodule (Cl i) (Cl i))] ↔
      ‖(a : K) - b‖ ≤ ‖(p : K)‖ ^ n := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h.cl.mem_iff]
    rfl
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one h.pos.le h.lt
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by simpa using (hm n x 0).1 (hx n)
    exact Subtype.ext (norm_le_zero_iff.1 this)
  · have hc : CauchySeq fun n => (f n : K) :=
      cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by
        rw [dist_eq_norm]
        exact (hm n _ _).1 (hf hnm)) ht
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨⟨L, closed_Cl.mem_of_tendsto hL (.of_forall fun n => (f n).2)⟩, fun n => (hm n _ _).2 ?_⟩
    refine le_of_tendsto (hL.const_sub (f n : K)).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hnm using (hm n _ _).1 (hf hnm)

private theorem Gd.ext_hom [CompleteSpace K] (h : Gd p i) (φ : S →+* S) :
    ∃ τ : Cl i →+* Cl i, Continuous τ ∧ ∀ y, τ (inc i y) = inc i (φ y) := by
  letI : PseudoMetricSpace S := PseudoMetricSpace.induced (inc i) inferInstance
  haveI : CompleteSpace (Cl i) := closed_Cl.completeSpace_coe
  have hi : Isometry (inc i) := fun _ _ => rfl
  have hf : UniformContinuous ((inc i).comp φ) := by
    refine (LipschitzWith.mk_one fun a b => ?_).uniformContinuous
    rw [← hi.dist_eq, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have := h.norm_map_le φ (a - b)
    simp only [map_sub] at this
    exact this
  refine ⟨IsDenseInducing.extendRingHom hi.isUniformInducing dense_inc hf, ?_, fun y => ?_⟩
  · exact (uniformContinuous_uniformly_extend hi.isUniformInducing dense_inc hf).continuous
  · exact (hi.isUniformInducing.isDenseInducing dense_inc).extend_eq hf.continuous y

private theorem Gd.ext_equiv [CompleteSpace K] (h : Gd p i) (φ : S ≃+* S) :
    ∃ σ : Cl i ≃+* Cl i, Continuous σ ∧ ∀ y, σ (inc i y) = inc i (φ y) := by
  obtain ⟨τ, c, e⟩ := h.ext_hom (φ : S →+* S)
  obtain ⟨τ', c', e'⟩ := h.ext_hom (φ.symm : S →+* S)
  refine ⟨RingEquiv.ofRingHom τ τ' (RingHom.ext fun x => ?_) (RingHom.ext fun x => ?_), c, e⟩
  · refine dense_inc.induction_on x (isClosed_eq (c.comp c') continuous_id) fun y => ?_
    simp [e, e']
  · refine dense_inc.induction_on x (isClosed_eq (c'.comp c) continuous_id) fun y => ?_
    simp [e, e']

private theorem Gd.cl_frob (h : Gd p i) (φ : S ≃+* S) (hφ : ∀ y, φ y - y ^ p ∈ Ideal.span {(p : S)})
    (σ : Cl i ≃+* Cl i) (c : Continuous σ) (e : ∀ y, σ (inc i y) = inc i (φ y)) (x : Cl i) :
    σ x - x ^ p ∈ Ideal.span {(p : Cl i)} := by
  have h1 := h.cl.mem_iff 1 (σ x - x ^ p)
  rw [pow_one] at h1
  rw [h1]
  refine dense_inc.induction_on x (isClosed_le (by fun_prop) continuous_const) fun y => ?_
  rw [e, ← map_pow, ← map_sub]
  exact (h.mem_iff 1 _).1 (by simpa using hφ y)

private theorem Gd.cl_closed [Nontrivial S] (h : Gd p i)
    (hS : ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x : S, P.eval x ∈ Ideal.span {(p : S)})
    (P : Polynomial (Cl i)) (hP : P.Monic) (hd : 0 < P.natDegree) :
    ∃ x : Cl i, P.eval x ∈ Ideal.span {(p : Cl i)} := by
  choose c hc using fun k => h.approx (P.coeff k) 1
  simp only [pow_one] at hc
  have hdeg : (∑ k : Fin P.natDegree, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ) : Polynomial S).degree
      < P.natDegree := Polynomial.degree_sum_fin_lt _
  obtain ⟨y, hy⟩ := hS _ (Polynomial.monic_X_pow_add hdeg) (by
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
    exact hd)
  refine ⟨inc i y, ?_⟩
  have h1 := Ideal.mem_map_of_mem (inc i) hy
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at h1
  have h2 : ∑ k : Fin P.natDegree, (P.coeff k - inc i (c k)) * inc i y ^ (k : ℕ) ∈ Ideal.span {(p : Cl i)} :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hc k)
  convert Ideal.add_mem _ h1 h2 using 1
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, Finset.sum_range]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, map_add, map_pow, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib]
  ring

end Closure

private def act {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {g : G ℚ Ω} (hg : g ∈ Dec (F := ℚ) A) :
    R0 A →+* R0 A :=
  ((g : Ω →+* Ω).comp (R0 A).subtype).codRestrict _ fun y =>
    ⟨(apply_mem_iff_of_mem_Dec hg _).2 y.2.1, fun s hs => by
      have := congrArg g (y.2.2 _ (conj_mem_Ine ((Dec (F := ℚ) A).inv_mem hg) hs))
      simpa using this⟩

private def actE {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {g : G ℚ Ω} (hg : g ∈ Dec (F := ℚ) A) :
    R0 A ≃+* R0 A :=
  RingEquiv.ofRingHom (act hg) (act ((Dec (F := ℚ) A).inv_mem hg))
    (RingHom.ext fun y => Subtype.ext (g.apply_symm_apply y))
    (RingHom.ext fun y => Subtype.ext (g.symm_apply_apply y))

theorem pFrEx3 : SFrEx := by
  intro l hl h2 Ω _ _ _ A hA j hj
  obtain ⟨⟨fr, hd, hf, hc⟩, -⟩ := pFrobEx l h2 Ω A hA
  let i : R0 A →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (j.comp (R0 A).subtype)
  have hn : ∀ x : PadicAlgCl l, ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := fun x => PadicComplex.norm_extends l x
  let a : ℤ_[l] →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (algebraMap ℤ_[l] (PadicAlgCl l))
  have ha : ∀ z, ‖a z‖ = ‖z‖ := fun z => by
    change ‖algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℤ_[l] (PadicAlgCl l) z)‖ = _
    rw [hn, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    rfl
  have hp : ‖(l : ℂ_[l])‖ = ‖(l : ℤ_[l])‖ := by rw [← ha, map_natCast]
  have hun : ∀ y : R0 A, ¬ (l : R0 A) ∣ y → IsUnit y := fun y hy =>
    inertia_invariant_valuation_uniformizer_bound l h2 Ω A hA y (by rwa [Ideal.mem_span_singleton])
  have h : Gd l i := ⟨norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero),
    hp ▸ PadicInt.norm_lt_one_iff_dvd _ |>.2 dvd_rfl, fun y => (hn _).trans_le (hj _ y.2.1), hun⟩
  have hac : Continuous a := (AddMonoidHomClass.isometry_of_norm a ha).continuous
  have ham : ∀ z, a z ∈ Cl i := fun z =>
    PadicInt.denseRange_intCast.induction_on z (closed_Cl.preimage hac) fun n => by
      rw [map_intCast]
      exact intCast_mem _ n
  letI : Algebra ℤ_[l] (Cl i) := (a.codRestrict _ ham).toAlgebra
  obtain ⟨σ, c, e⟩ := h.ext_equiv (actE hd)
  have hφ : ∀ y, actE hd y - y ^ l ∈ Ideal.span {(l : R0 A)} := fun y => by
    by_contra hy
    obtain ⟨z, hz⟩ := (inertia_invariant_valuation_uniformizer_bound l h2 Ω A hA _ hy).exists_right_inv
    have h1 : A.valuation ((actE hd y - y ^ l : R0 A) : Ω) < 1 := hf.2 y ((A.valuation_le_one_iff _).2 y.2.1)
    have h3 := congrArg (fun t : R0 A => A.valuation (t : Ω)) hz
    simp only [Subring.coe_mul, map_mul, Subring.coe_one, map_one] at h3
    exact ((mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 z.2.1)).trans_lt h1).ne h3
  have hcl := h.cl_closed (residue_field_teichmuller_lift_exists l h2 Ω A hA)
  have fl : FrobLift (Cl i) l σ := ⟨inferInstance, h.cl_prime, h.cl_complete, h.cl_frob _ hφ σ c e, fun x => by
    simpa using hcl (Polynomial.X ^ l - Polynomial.C x) (Polynomial.monic_X_pow_sub_C x hl.out.ne_zero)
      (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hl.out.pos)⟩
  exact ⟨{
    R := Cl i
    σ := σ
    fl := fl
    closed := hcl
    unit := fun x hx => h.cl_unit x (by rwa [Ideal.mem_span_singleton] at hx)
    fixed := pFixAbs _ l σ fl
    i0 := inc i
    dense := h.approx
    sep := fun y n hy => (h.mem_iff n y).2 ((h.cl.mem_iff n _).1 hy)
    fr := fr
    fr_dec := hd
    fr_frob := hf
    fr_cyc := hc
    frobenius_compat_inclusion := fun y y' hy => by
      rw [e]
      exact congrArg _ (Subtype.ext hy.symm)
    jh := (Cl i).subtype
    jh_comp_incl := fun _ => rfl
    jh_alg := fun _ => rfl
    jh_le := h.cl_le }⟩

end UpperTheory.Kd.C7
