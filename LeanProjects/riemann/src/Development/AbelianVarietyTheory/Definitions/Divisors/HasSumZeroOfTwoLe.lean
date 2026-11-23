import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfVal

noncomputable section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal.ObjModel
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem hatO_integral {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v (y v) ≤ 1 := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  have : y ∈ {y : Af E | y v ∈ v.adicCompletionIntegers E} := by
    refine closure_minimal ?_ hc hy
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
    have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
      rw [map_add]; rfl
    rw [this]
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)
  exact this

theorem modF_unit {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have h1 : Valued.v ((u : Af E) v) ≤ 1 := hatO_integral hu.1 v
  have h2 : Valued.v ((↑u⁻¹ : Af E) v) ≤ 1 := hatO_integral hu.2 v
  have h3 : Valued.v ((u : Af E) v) * Valued.v ((↑u⁻¹ : Af E) v) = 1 := by
    rw [← map_mul]
    have : (u : Af E) v * (↑u⁻¹ : Af E) v = 1 := (coord v u).val_inv
    rw [this, map_one]
  have h4 : Valued.v ((u : Af E) v) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((u : Af E) v) * 1 := by gcongr
      _ = _ := mul_one _
  simp [h4]

theorem lattice_top_one (x : E) : x ∈ lattice (⊤ : Ideal (OF E)) 1 ↔ ∃ b : 𝓞 E, x = algebraMap (𝓞 E) E b := by
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E x fun v =>
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).symm.trans_le (hatO_integral h v)
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, rfl⟩
    exact algebraMap_mem_hatO (mem_orderC.2 ⟨0, b, by simp [Ideal.map_top], by simp⟩)

variable {I : Type} [Fintype I]

theorem prod_normSq [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  push_cast at h1
  rw [← h1]
  refine Fintype.prod_bijective (fun i => InfinitePlace.mk (φ i)) ⟨fun i j hij => ?_, fun w => ?_⟩ _ _ fun i => ?_
  · obtain ⟨l, -, hl⟩ := h (φ i)
    have h2 := InfinitePlace.mk_eq_iff.1 hij.symm
    rw [hl i (Or.inl rfl), hl j (h2.imp Eq.symm Eq.symm)]
  · obtain ⟨l, hl, -⟩ := h w.embedding
    refine ⟨l, ?_⟩
    rw [← w.mk_embedding]
    exact InfinitePlace.mk_eq_iff.2 (hl.imp Eq.symm Eq.symm)
  · rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]

theorem prod_cpow (t : Finset I) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i) (z : ℂ) :
    ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ z = ((∏ i ∈ t, r i : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr a) (Finset.prod_nonneg fun i _ => hr i)]

theorem term_unit [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x : E := algebraMap (OF E) E u with hx
  have hn : ∏ i, ‖φ i x‖ ^ 2 = 1 := by
    rw [prod_normSq h]
    have := NumberField.Units.norm E (Units.map (algebraMap (OF E) (𝓞 E)).toMonoidHom u)
    exact_mod_cast this
  have hn1 : ∏ i, ‖φ i x‖ = 1 := by
    rw [Finset.prod_pow] at hn
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).1 hn
  have hr : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => ((u : OF E) : maximalRealSubfield E).2 (φ i)
  have h0 : ∀ i, φ i x ≠ 0 := fun i => by
    rw [map_ne_zero]; exact (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  unfold term
  rw [Finset.prod_mul_distrib, prod_cpow _ _ (fun i => norm_nonneg _), hn1]
  have : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * (starRingEnd ℂ (φ i x)) ^ κ i = (((‖φ i x‖ ^ 2 : ℝ) : ℂ)⁻¹) ^ s := fun i => by
    have h2 : ((‖φ i x‖ ^ 2 : ℝ) : ℂ) = φ i x ^ 2 := by
      push_cast
      rw [← Complex.mul_conj', hr, sq]
    have := h0 i
    rw [h2, hr, pow_add, pow_mul, mul_assoc, ← mul_pow, inv_mul_cancel₀ this, inv_pow]
    simp
  simp only [this]
  rw [Finset.prod_pow, Finset.prod_inv_distrib, ← Complex.ofReal_prod, hn]
  simp

theorem term_out [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    term φ (2 * s) κ σ (Quotient.mk (unitRel (E := E)) x).out = term φ (2 * s) κ σ x := by
  obtain ⟨u, hu⟩ : (unitRel (E := E)).r x (Quotient.mk (unitRel (E := E)) x).out := Quotient.exact (Quotient.out_eq _).symm
  rw [hu, term_mul, term_unit h, one_mul]

theorem term_differentiable (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) {a : E} (ha : a ≠ 0) :
    Differentiable ℂ fun σ => term φ k κ σ a := by
  unfold term
  refine Differentiable.fun_finset_prod fun i _ => Differentiable.const_mul ?_ _
  refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
  simpa using ha

theorem isLatSum_single [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) {a : E} (ha : a ≠ 0) :
    IsLatSum φ (2 * s) κ {a} fun σ => term φ (2 * s) κ σ a := by
  refine ⟨term_differentiable φ _ κ ha, fun σ _ => ?_⟩
  have := hasSum_single (f := fun q : modUnits ({a} : Set E) => term φ (2 * s) κ σ q.1.out)
    (⟨Quotient.mk _ a, a, rfl, ha, rfl⟩ : modUnits ({a} : Set E)) (by
      rintro ⟨_, x, rfl, _, rfl⟩ hb
      exact absurd rfl hb)
  rwa [term_out h] at this

def mulQ (a : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (a * ·) (by rintro x y ⟨u, rfl⟩; exact ⟨u, by ring⟩)

theorem hasSum_smul [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) {s : ℕ} {κ : I → ℕ} {L L' : Set E} (a : Eˣ)
    (hL : ∀ x, (a : E) * x ∈ L' ↔ x ∈ L) {σ S : ℂ} (hS : HasSum (fun q : modUnits L => term φ (2 * s) κ σ q.1.out) S) :
    HasSum (fun q : modUnits L' => term φ (2 * s) κ σ q.1.out) (term φ (2 * s) κ σ a * S) := by
  let f : modUnits L → modUnits L' := fun q => ⟨mulQ a q.1, by
    obtain ⟨x, hx, h0, hq⟩ := q.2
    exact ⟨a * x, (hL x).2 hx, mul_ne_zero a.ne_zero h0, by rw [← hq]; rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨_, x, hx, h0, rfl⟩ ⟨_, x', hx', h0', rfl⟩ hq
      obtain ⟨u, hu⟩ : (unitRel (E := E)).r (a * x) (a * x') := Quotient.exact (congrArg Subtype.val hq)
      refine Subtype.ext (Quotient.sound ⟨u, mul_left_cancel₀ a.ne_zero ?_⟩)
      rw [hu]; ring
    · rintro ⟨_, x, hx, h0, rfl⟩
      refine ⟨⟨Quotient.mk _ ((↑a⁻¹ : E) * x), _, (hL _).1 (by simpa using hx), mul_ne_zero a⁻¹.ne_zero h0, rfl⟩, ?_⟩
      refine Subtype.ext ?_
      show Quotient.mk _ ((a : E) * ((↑a⁻¹ : E) * x)) = Quotient.mk _ x
      simp
  rw [← (Equiv.ofBijective f hf).hasSum_iff]
  refine (hS.mul_left (term φ (2 * s) κ σ a)).congr_fun ?_
  rintro ⟨_, x, hx, h0, rfl⟩
  show term φ (2 * s) κ σ (Quotient.mk (unitRel (E := E)) ((a : E) * x)).out = _
  rw [term_out h, term_out h, term_mul]

theorem isLatSum_smul [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) {s : ℕ} {κ : I → ℕ} {L L' : Set E} (a : Eˣ)
    (hL : ∀ x, (a : E) * x ∈ L' ↔ x ∈ L) {S : ℂ → ℂ} (hS : IsLatSum φ (2 * s) κ L S) :
    IsLatSum φ (2 * s) κ L' fun σ => term φ (2 * s) κ σ a * S σ :=
  ⟨(term_differentiable φ _ κ a.ne_zero).mul hS.1, fun σ hσ => hasSum_smul h a hL (hS.2 σ hσ)⟩

theorem toric_term_class [IsTotallyComplex E] {φ : I → E →+* ℂ} (h : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    {χ : HChar E} (hχ : ∀ u ∈ hatOUnits c, finPart χ u = 1) (hi : HasInf χ φ fun i => (κ i : ℤ) + s)
    {y y' : (Af E)ˣ} (hy : (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y') {S S' : ℂ → ℂ}
    (hS : IsLatSum φ (2 * s) κ (lattice c y) S) (hS' : IsLatSum φ (2 * s) κ (lattice c y') S') :
    ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹ * S' 0 := by
  obtain ⟨_, ⟨a, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hy)
  have hy' : y' = Units.map (algebraMap E (Af E)).toMonoidHom a * y * u := by
    rw [eq_inv_mul_iff_mul_eq] at hau
    rw [← hau, mul_assoc, mul_left_comm]
  rw [hy', lattice_mul_unit _ hu] at hS'
  have h1 := hS'.unique (isLatSum_smul h a (mul_mem_lattice_princ c y a) hS)
  have h2 := term_mul_inf hi a
  have h3 : ((finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom a) : ℂˣ) : ℂ) * ((χ.inf a : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  have h4 : ∏ i, (φ i a * starRingEnd ℂ (φ i a)) ^ s = ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ s : ℝ) : ℂ) := by
    rw [← prod_normSq h, Finset.prod_pow]
    simp [Complex.mul_conj']
  have h5 : (|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)|) ≠ 0 := by simp [Algebra.norm_eq_zero_iff]
  rw [h4] at h2
  rw [h1, hy', map_mul, map_mul, hχ u hu, mul_one, modF_mul, modF_mul, modF_unit hu, mul_one, modF_princ]
  generalize (|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)|) = n at *
  have h6 : (n : ℂ) ≠ 0 := by exact_mod_cast h5
  have h7 : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modF_pos y).ne'
  have h8 : ((χ.inf a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  beta_reduce
  rw [Units.val_mul, eq_inv_of_mul_eq_one_left h3, eq_inv_of_mul_eq_one_left h2]
  push_cast
  rw [mul_pow, inv_pow]
  field_simp

theorem summable_int {φ : E →+* ℂ} (h : IsCMType fun _ : Unit => φ) (h2 : Module.finrank ℚ E = 2) {r : ℝ} (hr : r < -2) :
    Summable fun b : 𝓞 E => ‖φ b‖ ^ r := by
  let f : 𝓞 E →ₗ[ℤ] ℂ := (φ.comp (algebraMap (𝓞 E) E)).toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := φ.injective.comp RingOfIntegers.coe_injective
  let M : Submodule ℤ ℂ := LinearMap.range f
  have hfin : {z : M | ‖z‖ < 1}.Finite := by
    have h1 := (Embeddings.finite_of_norm_le E ℂ 1).image φ
    refine (h1.preimage (f := fun z : M => (z : ℂ)) Subtype.val_injective.injOn).subset ?_
    rintro ⟨_, b, rfl⟩ hb
    refine ⟨b, ⟨b.isIntegral_coe, fun ψ => ?_⟩, rfl⟩
    have hb' : ‖φ b‖ < 1 := hb
    obtain ⟨_, hψ | hψ, -⟩ := h ψ
    · rw [hψ]; exact hb'.le
    · rw [hψ]; simpa using hb'.le
  haveI : DiscreteTopology M := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have ho : IsOpen {z : M | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
    have := ho.sdiff (hfin.subset (Set.diff_subset (t := {0}))).isClosed
    convert this using 1
    ext z
    by_cases hz : z = 0 <;> simp [hz]
  have hrk : (Module.finrank ℤ M : ℝ) ≤ 2 := by
    have := LinearMap.finrank_range_le f
    rw [RingOfIntegers.rank, h2] at this
    exact_mod_cast this
  have hs := ZLattice.summable_norm_rpow M r (by linarith)
  exact hs.comp_injective (i := fun b : 𝓞 E => (⟨f b, b, rfl⟩ : M)) fun a b hab => hf (congrArg Subtype.val hab)

theorem norm_term_unit (φ : E →+* ℂ) (k κ : ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term (fun _ : Unit => φ) k (fun _ => κ) σ x‖ = ‖φ x‖ ^ (-(k : ℝ) - 2 * σ.re) := by
  have h0 : 0 < ‖φ x‖ := by simpa using hx
  unfold term
  rw [Fintype.prod_unique, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, norm_pow, norm_pow, norm_inv,
    Complex.norm_conj, sub_eq_add_neg, Real.rpow_add h0, Real.rpow_neg h0.le, Real.rpow_natCast]
  congr 1
  · rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ h0.ne', one_pow, mul_one, inv_pow]
  · simp

theorem summable_term {φ : E →+* ℂ} (h : IsCMType fun _ : Unit => φ) (h2 : Module.finrank ℚ E = 2) (k κ : ℕ) {σ : ℂ}
    (hσ : 1 < (k : ℝ) / 2 + σ.re) :
    Summable fun q : modUnits (lattice (⊤ : Ideal (OF E)) 1) => term (fun _ : Unit => φ) k (fun _ => κ) σ q.1.out := by
  choose b hb using fun q : modUnits (lattice (⊤ : Ideal (OF E)) 1) => (lattice_top_one _).1 (out_mem_lattice q).1
  have hi : Function.Injective b := fun q q' hq => Subtype.ext (Quotient.out_injective (by rw [hb, hb, hq]))
  refine Summable.of_norm (((summable_int h h2 (r := -(k : ℝ) - 2 * σ.re) (by linarith)).comp_injective hi).congr fun q => ?_)
  rw [norm_term_unit φ k κ σ (out_mem_lattice q).2, hb]
  rfl

theorem isLatSum_int [IsTotallyComplex E] {φ : E →+* ℂ} (h : IsCMType fun _ : Unit => φ) (h2 : Module.finrank ℚ E = 2)
    (z : (𝓞 E)ˣ) {s κ : ℕ} (hz : φ (z : 𝓞 E) ^ (2 * (s + κ)) ≠ 1) :
    IsLatSum (fun _ : Unit => φ) (2 * s) (fun _ => κ) (lattice (⊤ : Ideal (OF E)) 1) 0 := by
  refine ⟨differentiable_const _, fun σ hσ => ?_⟩
  have hs := (summable_term h h2 (2 * s) κ hσ).hasSum
  let a : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom z
  have hL : ∀ x, (a : E) * x ∈ lattice (⊤ : Ideal (OF E)) 1 ↔ x ∈ lattice (⊤ : Ideal (OF E)) 1 := fun x => by
    rw [lattice_top_one, lattice_top_one]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨(↑z⁻¹ : 𝓞 E) * b, ?_⟩
      rw [map_mul, ← hb, ← mul_assoc]
      show x = (↑a⁻¹ : E) * a * x
      simp
    · rintro ⟨b, rfl⟩
      exact ⟨z * b, by rw [map_mul]; rfl⟩
  have h3 := hs.unique (hasSum_smul h a hL hs)
  have h4 : term (fun _ : Unit => φ) (2 * s) (fun _ => κ) σ a ≠ 1 := by
    have ha : φ a ^ (2 * (s + κ)) ≠ 1 := hz
    have hn : ‖φ a‖ = 1 := by
      have h5 := prod_normSq h (a : E)
      have h6 : |((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| = 1 := by exact_mod_cast NumberField.Units.norm E z
      rw [h6, Fintype.prod_unique] at h5
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
    have hc : starRingEnd ℂ (φ a) = (φ a)⁻¹ := by rw [Complex.inv_eq_conj hn]
    unfold term
    rw [Fintype.prod_unique, hn, hc, ← pow_add, show 2 * s + κ + κ = 2 * (s + κ) by ring, inv_pow]
    simpa using ha
  have h5 : (∑' q : modUnits (lattice (⊤ : Ideal (OF E)) 1), term (fun _ : Unit => φ) (2 * s) (fun _ => κ) σ q.1.out) = 0 := by
    by_contra h0
    exact h4 ((mul_left_eq_self₀.1 h3.symm).resolve_right h0)
  rwa [h5] at hs

theorem mem_hatO_top {y : Af E} : y ∈ hatO (⊤ : Ideal (OF E)) ↔ ∀ v, Valued.v (y v) ≤ 1 :=
  ⟨hatO_integral, fun h => GlobalTheory.IntDense.mem_of_isClosed E (C := (hatO (⊤ : Ideal (OF E)) : Set (Af E))) (Subring.isClosed_topologicalClosure _)
    (fun b => algebraMap_mem_hatO (c := ⊤) (mem_orderC.2 ⟨0, b, by simp [Ideal.map_top], by simp⟩)) y h⟩

theorem exists_princ [IsPrincipalIdealRing (𝓞 E)] (y : (Af E)ˣ) :
    ∃ (a : Eˣ) (u : (Af E)ˣ), u ∈ hatOUnits (⊤ : Ideal (OF E)) ∧ y = Units.map (algebraMap E (Af E)).toMonoidHom a * 1 * u := by
  classical
  have hp : ∀ v : HeightOneSpectrum (𝓞 E), ∃ p : E, v.valuation E p = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w ≠ v → w.valuation E p = 1 := fun v => by
    obtain ⟨r, hr⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
    have h0 : r ≠ 0 := by rintro rfl; exact v.ne_bot (by simpa using hr)
    refine ⟨r, ?_, fun w hw => ?_⟩
    · rw [HeightOneSpectrum.valuation_of_algebraMap]; exact v.intValuation_singleton h0 hr
    · rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      refine hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top ?_).symm)
      rw [hr]; exact (Ideal.span_singleton_le_iff_mem _).2 hm
  choose p hp1 hp2 using hp
  have hf := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at hf
  let a : E := ∏ v ∈ hf.toFinset, p v ^ (-WithZero.log (Valued.v ((y : Af E) v)))
  have ha : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E a = Valued.v ((y : Af E) w) := fun w => by
    simp only [a, map_prod, map_zpow₀]
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hp2 v w hv.symm, one_zpow]) (fun hw => by
      have : Valued.v ((y : Af E) w) = 1 := by simpa using hw
      simp [this]), hp1, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log (coord_ne y w)]
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ fun h => by
    have := hp1 v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  let b : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom (Units.mk0 a ha0)
  have hb : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((b : Af E) w) = Valued.v ((y : Af E) w) := fun w =>
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a).trans (ha w)
  have key : ∀ b y : (Af E)ˣ, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((b : Af E) w) = Valued.v ((y : Af E) w)) →
      ((b⁻¹ * y : (Af E)ˣ) : Af E) ∈ hatO (⊤ : Ideal (OF E)) := fun b y h => mem_hatO_top.2 fun w => by
    have h1 : ((b⁻¹ * y : (Af E)ˣ) : Af E) w = (↑b⁻¹ : Af E) w * (y : Af E) w := rfl
    have h2 : (↑b⁻¹ : Af E) w * (b : Af E) w = 1 := (coord w b).inv_val
    rw [h1, map_mul, ← h, ← map_mul, h2, map_one]
  refine ⟨Units.mk0 a ha0, b⁻¹ * y, ⟨key b y hb, ?_⟩, by simp [b]⟩
  have := key y b fun w => (hb w).symm
  rw [show y⁻¹ * b = (b⁻¹ * y)⁻¹ by rw [mul_inv, inv_inv, mul_comm]] at this
  exact this

theorem subsingleton_picO [IsPrincipalIdealRing (𝓞 E)] : Subsingleton (PicO (⊤ : Ideal (OF E))) := by
  refine QuotientGroup.subsingleton_iff.2 (eq_top_iff.2 fun y _ => ?_)
  obtain ⟨a, u, hu, rfl⟩ := exists_princ y
  rw [mul_one]
  exact Subgroup.mul_mem_sup ⟨a, rfl⟩ hu

theorem isToricSum_int [IsTotallyComplex E] [IsPrincipalIdealRing (𝓞 E)] {φ : E →+* ℂ} (h : IsCMType fun _ : Unit => φ)
    (h2 : Module.finrank ℚ E = 2) (z : (𝓞 E)ˣ) {s κ : ℕ} (hz : φ (z : 𝓞 E) ^ (2 * (s + κ)) ≠ 1) (χ : HChar E) :
    IsToricSum (fun _ : Unit => φ) s (fun _ => κ) ⊤ χ 0 := by
  haveI := subsingleton_picO (E := E)
  refine ⟨inferInstance, fun _ => 0, fun q => ?_, by simp⟩
  obtain ⟨a, u, hu, hq⟩ := exists_princ q.out
  rw [hq, lattice_mul_unit _ hu]
  have := isLatSum_smul h a (mul_mem_lattice_princ ⊤ 1 a) (isLatSum_int h h2 z hz)
  simpa [Pi.zero_def] using this

abbrev Eis : Type := CyclotomicField 3 ℚ

instance : IsCyclotomicExtension {3} ℚ Eis := CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsCMField Eis := IsCyclotomicExtension.Rat.isCMField Eis (S := {3}) ⟨3, rfl, by norm_num⟩

theorem isToricSum_eis : ∃ φ : Eis →+* ℂ, IsCMType (fun _ : Unit => φ) ∧
    ∀ χ : HChar Eis, IsToricSum (fun _ : Unit => φ) 1 (fun _ => 1) ⊤ χ 0 := by
  have h2 : Module.finrank ℚ Eis = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 3) Eis (Polynomial.cyclotomic.irreducible_rat (by norm_num))]; rfl
  have hc : Fintype.card (InfinitePlace Eis) = 1 := by
    have := IsTotallyComplex.finrank Eis
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces Eis
    rw [IsTotallyComplex.nrRealPlaces_eq_zero] at h3
    omega
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 hc
  have hφ : IsCMType fun _ : Unit => w.embedding := fun σ =>
    ⟨(), (InfinitePlace.mk_eq_iff.1 (w.mk_embedding.trans (hw _).symm)).imp Eq.symm Eq.symm, fun _ _ => rfl⟩
  have hz := IsCyclotomicExtension.zeta_spec 3 ℚ Eis
  haveI := IsCyclotomicExtension.Rat.three_pid Eis
  refine ⟨_, hφ, isToricSum_int hφ h2 (hz.toInteger_isPrimitiveRoot.isUnit (by norm_num)).unit ?_⟩
  have h4 : IsPrimitiveRoot (w.embedding (IsCyclotomicExtension.zeta 3 ℚ Eis)) 3 := hz.map_of_injective w.embedding.injective
  intro h5
  exact absurd ((h4.pow_eq_one_iff_dvd _).1 h5) (by decide)

theorem hasSum_zero_of_two_le {φ : I → E →+* ℂ} {s : ℕ} (hs : 2 ≤ s) {κ : I → ℕ} {L : Set E} {S : ℂ → ℂ}
    (h : IsLatSum φ (2 * s) κ L S) : HasSum (fun q : modUnits L => term φ (2 * s) κ 0 q.1.out) (S 0) := by
  refine h.2 0 ?_
  have : (2 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast
  simp only [Complex.zero_re]
  linarith

theorem hasInfRatio_conj (χ : HChar E) (φ : I → E →+* ℂ) (m : I → ℤ) :
    HasInfRatio χ (fun i => ComplexEmbedding.conjugate (φ i)) m ↔ HasInfRatio χ φ fun i => -m i := by
  rw [hasInfRatio_iff, hasInfRatio_iff]
  refine forall_congr' fun k => ?_
  have : ∀ i, (ComplexEmbedding.conjugate (φ i) (k : E) / starRingEnd ℂ (ComplexEmbedding.conjugate (φ i) (k : E))) ^ m i =
      (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ (-m i) := fun i => by
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, zpow_neg, ← inv_zpow, inv_div]
  simp only [this]

theorem not_isLatSum_empty (φ : Empty → E →+* ℂ) (k : ℕ) (κ : Empty → ℕ) {L : Set E} (hL : (modUnits L).Infinite) (S : ℂ → ℂ) :
    ¬ IsLatSum φ k κ L S := fun h => by
  have h1 := (h.2 2 (by simp only [Complex.re_ofNat]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).summable
  simp only [term, Finset.univ_eq_empty, Finset.prod_empty] at h1
  haveI := hL.to_subtype
  have h2 := h1.tendsto_cofinite_zero
  exact one_ne_zero (tendsto_const_nhds_iff.1 h2)

section RatL
open GlobalTheory.CMVal.ValEx Rat.HeightOneSpectrum

theorem absNorm_rat (p : HeightOneSpectrum (𝓞 ℚ)) : Ideal.absNorm p.asIdeal = (primesEquiv p : ℕ) := by
  have e := Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (span_natGenerator p)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv]
  have := Ideal.absNorm_span_singleton ((natGenerator p : ℕ) : ℤ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  rw [this]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]
  rfl

theorem hasProd_one {s : ℂ} (hs : 1 < s.re) : HasProd (eulerFactor (1 : HChar ℚ) s) (riemannZeta s) := by
  have := (primesEquiv (R := 𝓞 ℚ)).hasProd_iff.2 (riemannZeta_eulerProduct_hasProd hs)
  refine this.congr_fun fun p => ?_
  have h : (1 : HChar ℚ).UnrAt p := fun _ _ => rfl
  have h' : (1 : HChar ℚ).val p = 1 := rfl
  simp only [eulerFactor, if_pos h, h', absNorm_rat, Function.comp_apply, Units.val_one, one_mul]

theorem not_isHeckeL_one (Λ : ℂ → ℂ) : ¬ IsHeckeL (1 : HChar ℚ) Λ := by
  rintro ⟨h1, h2⟩
  have hf : Differentiable ℂ fun s => (s - 1) * Λ s := by fun_prop
  have hg : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ 1) := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have := entire_eq_of_halfPlane hf hg 1 fun s hs => by
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [(h2 s hs).unique (hasProd_one hs)]
    simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
      DirichletCharacter.LFunction_modOne_eq]
  have h3 := congrFun this 1
  simp [DirichletCharacter.LFunctionTrivChar₁] at h3

theorem mem_rat (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ p.asIdeal ↔ (primesEquiv p : ℕ) ∣ n := by
  change _ ↔ natGenerator p ∣ n
  rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem val_rat_one (p : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h : ¬ (primesEquiv p : ℕ) ∣ n) : p.valuation ℚ (n : ℚ) = 1 := by
  have e : (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff, mem_rat]
  exact h

theorem val_rat_self (p : HeightOneSpectrum (𝓞 ℚ)) : p.valuation ℚ ((primesEquiv p : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) :=
  val_prime (primesEquiv p).2 (by
    rw [Rat.numberField_discr]
    exact_mod_cast (primesEquiv p).2.not_dvd_one) p ((mem_rat p _).2 dvd_rfl)

theorem finOrder_rat (k : ℚˣ) (h : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.valuation ℚ (k : ℚ) = 1) : IsOfFinOrder k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ (k : ℚ) fun p => (h p).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ ((k⁻¹ : ℚˣ) : ℚ) fun p => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, h p, inv_one]
  obtain ⟨a', ha'⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral ℤ (k : ℚ) from ha ▸ a.isIntegral_coe)
  obtain ⟨b', hb'⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral ℤ ((k⁻¹ : ℚˣ) : ℚ) from hb ▸ b.isIntegral_coe)
  have h1 : a' * b' = 1 := by
    have : algebraMap ℤ ℚ (a' * b') = 1 := by rw [map_mul, ha', hb', Units.mul_inv]
    exact (algebraMap ℤ ℚ).injective_int (this.trans (map_one _).symm)
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨2, two_pos, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, ← ha']
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with rfl | rfl <;> simp

theorem exists_dirichlet (G : ℚˣ →* ℂˣ)
    (hG : ∀ (n m : ℕ) (hn : (n : ℚ) ≠ 0) (hm : (m : ℚ) ≠ 0), ¬ 3 ∣ n → n ≡ m [MOD 9] → G (Units.mk0 n hn) = G (Units.mk0 m hm)) :
    ∃ D : DirichletCharacter ℂ 9, ∀ (n : ℕ) (hn : (n : ℚ) ≠ 0), ¬ 3 ∣ n → D n = G (Units.mk0 n hn) := by
  have h3 : ∀ u : (ZMod 9)ˣ, ¬ 3 ∣ (u : ZMod 9).val := fun u h => by
    have := Nat.Coprime.eq_one_of_dvd ((ZMod.val_coe_unit_coprime u).coprime_dvd_left h) (by norm_num)
    omega
  have h0 : ∀ u : (ZMod 9)ˣ, (((u : ZMod 9).val : ℕ) : ℚ) ≠ 0 := fun u h => h3 u (by
    have : (u : ZMod 9).val = 0 := by exact_mod_cast h
    simp [this])
  let f : (ZMod 9)ˣ →* ℂˣ := MonoidHom.mk' (fun u => G (Units.mk0 _ (h0 u))) fun u v => by
    rw [← map_mul, hG _ ((u : ZMod 9).val * (v : ZMod 9).val) _ (by push_cast; exact mul_ne_zero (h0 u) (h0 v)) (h3 _)
      (by rw [Units.val_mul, ZMod.val_mul]; exact Nat.mod_modEq _ _)]
    congr 1
    ext
    simp
  refine ⟨MulChar.ofUnitHom f, fun n hn h => ?_⟩
  have hc : n.Coprime 9 := by
    have := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
    exact Nat.Coprime.pow_right 2 this
  rw [← ZMod.coe_unitOfCoprime n hc, MulChar.ofUnitHom_coe]
  congr 1
  exact hG _ _ _ _ (h3 _) (by rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]; exact Nat.mod_modEq _ _)

theorem exists_isHeckeL : ∃ (χ : HChar ℚ) (D : DirichletCharacter ℂ 9), IsUnitary χ ∧ D ≠ 1 ∧ (∃ w, ¬ χ.UnrAt w) ∧
    IsHeckeL χ (DirichletCharacter.LFunction D) := by
  let w : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm ⟨3, Nat.prime_three⟩
  have hw : (primesEquiv w : ℕ) = 3 := congrArg Subtype.val (primesEquiv.apply_symm_apply _)
  have hw3 : w.valuation ℚ ((3 : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by rw [← hw]; exact val_rat_self w
  let u : ℚˣ := Units.mk0 ((4 : ℕ) : ℚ) (by norm_num)
  obtain ⟨ch, hc1, hc2, hc3, hc4, hc5⟩ := exists_locChar Nat.prime_three (by norm_num) w hw3 1 u (by simp [u]; norm_num)
  obtain ⟨χ, h1, h3, h4, h5⟩ := exists_unitary_char_of_open_subgroup_and_hom (Ideles ℚ) ℚˣ unitI isOpen_unitI
    (Neutral.B1.diagUnits ℚ) 1 (ch.comp ((locU w).comp finOf))
    (hc1.comp ((continuous_locU w).comp continuous_finOf)) (fun x => hc2 _) (by simp) (fun k hk => by
      have := hc4 k (finOrder_rat k fun p => by rw [← val_alg]; exact mem_unitI.1 hk p)
      exact this.symm)
  let X : HChar ℚ := ⟨χ, h1, fun k => h5 k⟩
  have hloc : ∀ P (x : (P.adicCompletion ℚ)ˣ), Valued.v (x : P.adicCompletion ℚ) = 1 → X.loc P x = ch (locU w (single P x)) :=
    fun P x hx => h4 _ (finIdele_mem (suppAt_single P x) (by rw [single_self, hx]))
  obtain ⟨D, hD⟩ := exists_dirichlet (ch.comp (toLoc w))⁻¹ fun n m hn hm h3n hnm => by
    have h3m : ¬ 3 ∣ m := fun h => h3n ((hnm.dvd_iff (by norm_num)).2 h)
    have vn := val_rat_one w (n := n) (by rwa [hw])
    have vm := val_rat_one w (n := m) (by rwa [hw])
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inj, eq_comm, ← div_eq_one, ← map_div]
    obtain ⟨t, ht⟩ := hnm.dvd
    have ht' : (m : ℚ) - n = 3 * 3 * t := by exact_mod_cast ht
    refine hc3 _ ⟨?_, ?_⟩
    · change Valued.v (algebraMap ℚ (w.adicCompletion ℚ) _) = 1
      rw [val_alg]; simp [vn, vm]
    · change Valued.v (algebraMap ℚ (w.adicCompletion ℚ) _ - 1) ≤ _
      rw [← map_one (algebraMap ℚ (w.adicCompletion ℚ)), ← map_sub, val_alg]
      have e : ((Units.mk0 (m : ℚ) hm / Units.mk0 (n : ℚ) hn : ℚˣ) : ℚ) - 1 = ((3 : ℕ) : ℚ) * ((3 : ℕ) : ℚ) * t / n := by
        rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]
        push_cast
        rw [← ht']; field_simp
      rw [e, map_div₀, vn, div_one, map_mul, map_mul, hw3, exp_one_sq]
      exact (mul_le_mul' le_rfl (val_int_le _ t)).trans (by simp)
  have hram : ¬ X.UnrAt w := fun h => hc5 (by
    have hv : Valued.v ((toLoc w u : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ) = 1 :=
      (val_alg w _).trans (val_rat_one w (n := 4) (by rw [hw]; norm_num))
    have := h _ hv
    rwa [hloc _ _ hv, locU_single] at this)
  have hD1 : D ≠ 1 := fun h => hc5 (by
    have := hD 4 (by norm_num) (by norm_num)
    rw [h, MulChar.one_apply (by rw [ZMod.isUnit_iff_coprime]; norm_num), MonoidHom.inv_apply] at this
    have h2 : (ch (toLoc w u))⁻¹ = 1 := Units.ext this.symm
    exact inv_eq_one.1 h2)
  refine ⟨X, D, h3, hD1, ⟨w, hram⟩, DirichletCharacter.differentiable_LFunction hD1, fun s hs => ?_⟩
  rw [DirichletCharacter.LFunction_eq_LSeries D hs]
  have := (primesEquiv (R := 𝓞 ℚ)).hasProd_iff.2 (DirichletCharacter.LSeries_eulerProduct_hasProd D hs)
  refine this.congr_fun fun p => ?_
  by_cases hp : p = w
  · rw [hp]
    have h0 : D ((primesEquiv w : ℕ) : ZMod 9) = 0 := D.map_nonunit (by rw [hw, ZMod.isUnit_iff_coprime]; norm_num)
    simp only [eulerFactor, if_neg hram, h0, Function.comp_apply, zero_mul, sub_zero, inv_one]
  · have hun : X.UnrAt p := fun x hx => by
      rw [hloc p x hx, locU_of_supp (suppAt_single p x) (Ne.symm hp), map_one]
    have hne : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ≠ p → ¬ (primesEquiv q : ℕ) ∣ (primesEquiv p : ℕ) := fun q hq h =>
      hq (primesEquiv.injective (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (primesEquiv q).2 (primesEquiv p).2).1 h)))
    have hP0 : (((primesEquiv p : ℕ)) : ℚ) ≠ 0 := by exact_mod_cast (primesEquiv p).2.ne_zero
    let k : ℚˣ := Units.mk0 _ hP0
    have hk : X.loc p (toLoc p k) = X.val p := X.val_eq hun _ ((val_alg p _).trans (val_rat_self p))
    have hfin : ∀ q, locU q (finOf (Neutral.B1.diagUnits ℚ k / finIdele ℚ (single p (toLoc p k)))) =
        toLoc q k / locU q (single p (toLoc p k)) := fun q => by
      rw [map_div, map_div]; rfl
    have hmem : Neutral.B1.diagUnits ℚ k / finIdele ℚ (single p (toLoc p k)) ∈ unitI := mem_unitI.2 fun q => by
      refine (congrArg (fun y : (q.adicCompletion ℚ)ˣ => Valued.v (y : q.adicCompletion ℚ)) (hfin q)).trans ?_
      by_cases hq : q = p
      · subst hq; rw [locU_single, div_self']; simp
      · rw [locU_of_supp (suppAt_single p _) hq, div_one]
        exact (val_alg q _).trans (val_rat_one q (hne q hq))
    have h6 := h4 _ hmem
    rw [map_div, h5, MonoidHom.comp_apply, MonoidHom.comp_apply, hfin, locU_of_supp (suppAt_single p _) (Ne.symm hp), div_one,
      MonoidHom.one_apply, one_div] at h6
    have h7 : X.val p = (ch (toLoc w k))⁻¹ := by rw [← hk, ← h6, inv_inv]; rfl
    have h8 := hD _ hP0 (by rw [← hw]; exact hne w (Ne.symm hp))
    simp only [eulerFactor, if_pos hun, Function.comp_apply, absNorm_rat, h8, h7]
    rfl

end RatL

end GlobalTheory.CMVal.ObjModel
