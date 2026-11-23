import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.WittIntegral

theorem exists_isUnit_sub {O : Type} [CommRing O] (s : O →+* O) (hs : ∀ z, s (s z) = z) (β t : O)
    (hβ : IsUnit β) (u : Fin 3 → O) (hu : ∀ i j, i ≠ j → IsUnit (u i - u j))
    (hloc : ∀ a : Fin 3 → O, (∀ i, s (a i) = a i) → ∑ i, a i = 2 → ∃ i, IsUnit (a i)) :
    ∃ i, IsUnit (β - u i * t) := by
  set D : Fin 3 → O := fun i => β - u i * t with hD
  have key : ∀ m : Ideal O, m ≠ ⊤ → ∀ i j, i ≠ j → D i ∈ m → D j ∈ m → False := by
    intro m hm i j hij hi hj
    have h1 : (u i - u j) * t ∈ m := by
      have := m.sub_mem hj hi
      convert this using 1
      simp only [hD]; ring
    have h2 : t ∈ m := (m.unit_mul_mem_iff_mem (hu i j hij)).1 h1
    have h3 : β ∈ m := by
      have := m.add_mem hi (m.mul_mem_left (u i) h2)
      simpa [hD] using this
    exact hm (m.eq_top_of_isUnit_mem h3 hβ)
  have htop : Ideal.span (Set.range fun i => D i * s (D i)) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm' : m.comap s ≠ ⊤ := Ideal.comap_ne_top s hm.ne_top
    have h : ∀ i, D i ∈ m ∨ D i ∈ m.comap s := fun i =>
      hm.isPrime.mem_or_mem (hle (Ideal.subset_span ⟨i, rfl⟩))
    have k1 := key m hm.ne_top
    have k2 := key _ hm'
    rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h 2 with h2 | h2
    all_goals first
      | exact k1 0 1 (by decide) h0 h1
      | exact k1 0 2 (by decide) h0 h2
      | exact k1 1 2 (by decide) h1 h2
      | exact k2 0 1 (by decide) h0 h1
      | exact k2 0 2 (by decide) h0 h2
      | exact k2 1 2 (by decide) h1 h2
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 ((Ideal.eq_top_iff_one _).1 htop)
  have hc' : ∑ i, s (c i) * (D i * s (D i)) = 1 := by
    have := congrArg s hc
    simp only [map_sum, map_mul, hs, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨i, hi⟩ := hloc (fun i => (c i + s (c i)) * (D i * s (D i)))
    (fun i => by simp only [map_mul, map_add, hs]; ring)
    (by simp only [add_mul, Finset.sum_add_distrib, hc, hc']; norm_num)
  exact ⟨i, isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hi)⟩

theorem exists_unitary {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (hs : ∀ z, s (s z) = z)
    (O : Subring A) (hO : ∀ z ∈ O, s z ∈ O) (J : Matrix (Fin M) (Fin M) A)
    (hJ : ∀ i j, s (J j i) = J i j) (hJO : ∀ i j, J i j ∈ O) (x y : Fin M → A)
    (hx : ∀ i, x i ∈ O) (hy : ∀ i, y i ∈ O) (β : A) (hxx : Formalism.UG.hform s J x x = β)
    (hyy : Formalism.UG.hform s J y y = β) (u : A) (huO : u ∈ O) (hu : s u * u = 1) (c : A) (hcO : c ∈ O)
    (hc : (β - s u * Formalism.UG.hform s J y x) * c = 1) :
    ∃ g : GL (Fin M) A, g ∈ Formalism.UG.UJ s J ∧ (g : Matrix (Fin M) (Fin M) A).mulVec x = y ∧
      (∀ i j, (g : Matrix (Fin M) (Fin M) A) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) i j ∈ O := by
  have hf : ∀ p q : Fin M → A, Formalism.UG.hform s J p q = (Matrix.vecMul (fun i => s (p i)) J) ⬝ᵥ q := by
    intro p q
    simp only [Formalism.UG.hform, Matrix.vecMul, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  have hsym : ∀ p q : Fin M → A, s (Formalism.UG.hform s J p q) = Formalism.UG.hform s J q p := by
    intro p q
    simp only [Formalism.UG.hform, map_sum, map_mul, hs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ]; ring
  set t := Formalism.UG.hform s J y x with ht
  set w : Fin M → A := fun i => x i - u * y i with hw
  set l : Fin M → A := Matrix.vecMul (fun i => s (w i)) J with hl
  have hsβ : s β = β := by rw [← hxx, hsym]
  have hlin : ∀ q, l ⬝ᵥ q = Formalism.UG.hform s J x q - s u * Formalism.UG.hform s J y q := by
    intro q
    rw [hl, ← hf]
    simp only [Formalism.UG.hform, hw, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hlx : l ⬝ᵥ x = β - s u * t := by rw [hlin, hxx]
  have hly : l ⬝ᵥ y = s t - s u * β := by rw [hlin, hyy, ht, hsym]
  have hlw : l ⬝ᵥ w = (β - s u * t) + (β - u * s t) := by
    have : w = x - u • y := by ext i; simp [hw]
    rw [this, dotProduct_sub, dotProduct_smul, hlx, hly, smul_eq_mul]
    linear_combination β * hu
  have hc' : (β - u * s t) * s c = 1 := by
    have := congrArg s hc
    simpa only [map_mul, map_sub, hs, hsβ, map_one] using this
  set P : Matrix (Fin M) (Fin M) A := Matrix.vecMulVec w l with hP
  have hPP : P * P = (l ⬝ᵥ w) • P := by
    ext i j
    simp only [hP, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : Formalism.UG.cT s P * J = J * P := by
    ext i j
    simp only [hP, hl, Formalism.UG.cT, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.vecMul, dotProduct, map_mul, map_sum, hs, hJ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring
  have hcc : c * s c * (l ⬝ᵥ w) = c + s c := by
    rw [hlw]; linear_combination s c * hc + c * hc'
  have h1 : (1 - s c • P) * (1 - c • P) = 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hPP, smul_smul, smul_sub]
    rw [show c * (s c * l ⬝ᵥ w) = c + s c by rw [← hcc]; ring, add_smul]
    abel
  have h2 : (u • (1 - s c • P)) * (s u • (1 - c • P)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, h1, smul_smul, mul_comm, hu, one_smul]
  have hwO : ∀ i, w i ∈ O := fun i => O.sub_mem (hx i) (O.mul_mem huO (hy i))
  have hPO : ∀ i j, P i j ∈ O := fun i j =>
    O.mul_mem (hwO i) (O.sum_mem (t := Finset.univ) fun k _ => O.mul_mem (hO _ (hwO k)) (hJO k j))
  have h1O : ∀ i j, (1 : Matrix (Fin M) (Fin M) A) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
  refine ⟨⟨s u • (1 - c • P), u • (1 - s c • P), mul_eq_one_comm.1 h2, h2⟩, ?_, ?_, ?_, ?_⟩
  · change Formalism.UG.cT s (s u • (1 - c • P)) * J * (s u • (1 - c • P)) = J
    have : Formalism.UG.cT s (s u • (1 - c • P)) = u • (1 - s c • Formalism.UG.cT s P) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul, map_mul, map_sub, hs, Matrix.one_apply, eq_comm (a := j), apply_ite s, map_one, map_zero]
    rw [this]
    have h3 : (u • (1 - s c • Formalism.UG.cT s P)) * J = J * (u • (1 - s c • P)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.mul_smul, hPJ]
    rw [h3, Matrix.mul_assoc, h2, Matrix.mul_one]
  · change (s u • (1 - c • P)).mulVec x = y
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hP,
      Matrix.vecMulVec_mulVec, hlx]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hw, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    linear_combination (y i) * hu - s u * (x i - u * y i) * hc
  · intro i j
    exact O.mul_mem (hO _ huO) (O.sub_mem (h1O i j) (O.mul_mem hcO (hPO i j)))
  · intro i j
    exact O.mul_mem huO (O.sub_mem (h1O i j) (O.mul_mem (hO _ hcO) (hPO i j)))

theorem exists_three {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ u : Fin 3 → E, Function.Injective u ∧ ∀ i, σ (u i) * u i = 1 := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := by
    by_contra hne
    push Not at hne
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := h.2.2.2 τ x
    rw [hne] at this
    exact this.symm
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ :=
    ⟨y - σ y, sub_ne_zero.2 hy.symm, by rw [map_sub, hσ]; ring⟩
  have h1 : 1 - δ ≠ 0 := by
    intro h0
    have h2 := congrArg σ h0
    rw [map_sub, map_one, hδ, map_zero] at h2
    exact two_ne_zero (α := E) (by linear_combination h0 + h2)
  have h1' : 1 + δ ≠ 0 := by
    intro h0
    have h2 := congrArg σ h0
    rw [map_add, map_one, hδ, map_zero] at h2
    exact two_ne_zero (α := E) (by linear_combination h0 + h2)
  have a1 : (1 : E) ≠ -1 := fun h0 => two_ne_zero (α := E) (by linear_combination h0)
  have a2 : (1 : E) ≠ (1 + δ) / (1 - δ) := by
    intro h0
    rw [eq_div_iff h1] at h0
    exact mul_ne_zero (two_ne_zero (α := E)) hδ0 (by linear_combination - h0)
  have a3 : (-1 : E) ≠ (1 + δ) / (1 - δ) := by
    intro h0
    rw [eq_div_iff h1] at h0
    exact two_ne_zero (α := E) (by linear_combination - h0)
  refine ⟨![1, -1, (1 + δ) / (1 - δ)], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij a1 | exact absurd hij a2 | exact absurd hij a3
      | exact absurd hij a1.symm | exact absurd hij a2.symm | exact absurd hij a3.symm
  · intro i
    fin_cases i
    · simp
    · simp
    · change σ ((1 + δ) / (1 - δ)) * ((1 + δ) / (1 - δ)) = 1
      rw [map_div₀, map_add, map_sub, map_one, hδ, sub_neg_eq_add, ← sub_eq_add_neg]
      field_simp

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem ae_mem (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem ae_incl (e : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    inclR (F := F) (Fv F v) e ∈ intV b v := by
  filter_upwards [Filter.eventually_all.2 fun k => ae_mem (b.repr e k)] with v hv k
  have : (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) e) k =
      algebraMap F (Fv F v) (b.repr e k) := by
    change (Algebra.TensorProduct.basis (Fv F v) b).repr (1 ⊗ₜ e) k = _
    simp [Algebra.TensorProduct.basis_repr_tmul]
  rw [this]
  exact hv k

theorem repr_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) k =
      a * algebraMap F (Fv F v) (b.repr 1 k) := by
  change (Algebra.TensorProduct.basis (Fv F v) b).repr (a ⊗ₜ 1) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_algebraMap : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ a : Fv F v,
    algebraMap (Fv F v) (Fv F v ⊗[F] E) a ∈ intV b v ↔ a ∈ v.adicCompletionIntegers F := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr 1 k ≠ 0 := by
    by_contra hne
    push Not at hne
    exact one_ne_zero (b.repr.map_eq_zero_iff.1 (Finsupp.ext hne))
  filter_upwards [Filter.eventually_all.2 fun k => ae_mem (b.repr 1 k), ae_mem (b.repr 1 k)⁻¹] with v h1 h2 a
  constructor
  · intro ha
    have := mul_mem (ha k) h2
    rwa [repr_algebraMap, mul_assoc, ← map_mul, mul_inv_cancel₀ hk, map_one, mul_one] at this
  · intro ha j
    rw [repr_algebraMap]
    exact mul_mem ha (h1 j)

end Loc

theorem witt_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) (β : F), IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y ∈ latV (M := M) (n := 1) b v, qR (Fv F v) σ J (y 0) = algebraMap F (Fv F v) β → ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) x = y ∧ ∀ i j, ((HA.mat (Fv F v) σ J g : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v ∧ ((HA.mat (Fv F v) σ J g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ intV b v := by
  intro F E _ _ _ _ _ σ h d b M J x β hJ hβ hx
  obtain ⟨u, hui, hu⟩ := exists_three h
  filter_upwards [(GlobalTheory.GaugeEx.IntBasis.main F E σ d b).2.1, ae_algebraMap b, ae_mem (2⁻¹ : F), ae_mem β, ae_mem β⁻¹,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_incl b (J i j),
    Filter.eventually_all.2 fun i => ae_incl b (x 0 i),
    Filter.eventually_all.2 fun i => ae_incl b (u i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_incl b (u i - u j)⁻¹]
    with v ⟨h1, hmul, hsig⟩ halg h2 hb hb' hJO hxO huO hdO y hy hq
  let O : Subring (Fv F v ⊗[F] E) :=
    { carrier := intV b v
      one_mem' := h1
      mul_mem' := fun {p q} hp hq => hmul p hp q hq
      zero_mem' := fun k => by simp
      add_mem' := fun {p q} hp hq k => by
        rw [map_add, Finsupp.add_apply]; exact add_mem (hp k) (hq k)
      neg_mem' := fun {p} hp k => by
        rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hp k) }
  have hss := GlobalTheory.SelfDualLatticeCompare.sigR_sigR (Fv F v) h
  have hsi : ∀ e, sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := fun e => rfl
  let s : O →+* O := (sigR (Fv F v) σ).restrict O O hsig
  let φ : v.adicCompletionIntegers F →+* O :=
    ((algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype).codRestrict O
      fun a => (halg a).2 a.2
  have hinj : Function.Injective (algebraMap (Fv F v) (Fv F v ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hunit : ∀ a : F, a ≠ 0 → ∀ (p : algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F),
      algebraMap F (Fv F v) a⁻¹ ∈ v.adicCompletionIntegers F →
      IsUnit (⟨_, p⟩ : v.adicCompletionIntegers F) := by
    intro a ha p q
    refine IsUnit.of_mul_eq_one ⟨_, q⟩ (Subtype.ext ?_)
    change algebraMap F (Fv F v) a * algebraMap F (Fv F v) a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h2u : IsUnit (2 : v.adicCompletionIntegers F) := by
    refine IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext ?_)
    change (2 : Fv F v) * algebraMap F (Fv F v) 2⁻¹ = 1
    rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hloc : ∀ a : Fin 3 → O, (∀ i, s (a i) = a i) → ∑ i, a i = 2 → ∃ i, IsUnit (a i) := by
    intro a ha hsum
    have hex : ∀ i, ∃ α : v.adicCompletionIntegers F, φ α = a i := by
      intro i
      have e1 : sigR (Fv F v) σ (a i) = a i := congrArg Subtype.val (ha i)
      have e2 := GlobalTheory.SelfDualLatticeCompare.trace_tensor (Fv F v) h (a i : Fv F v ⊗[F] E)
      have e3 : algebraMap (Fv F v) (Fv F v ⊗[F] E)
          (2⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a i)) = a i := by
        have e4 : (2 : Fv F v) ≠ 0 := (h2u.map (v.adicCompletionIntegers F).subtype).ne_zero
        rw [map_mul, e2, e1, ← two_mul, ← mul_assoc,
          ← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ e4, map_one,
          one_mul]
      exact ⟨⟨_, (halg _).1 (by rw [e3]; exact (a i).2)⟩, Subtype.ext e3⟩
    choose α hα using hex
    have hφ : Function.Injective φ := fun p q hpq =>
      Subtype.ext (hinj (congrArg Subtype.val hpq))
    have hs2 : ∑ i, α i = 2 := hφ (by rw [map_sum, map_ofNat, ← hsum]; simp only [hα])
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hs2 ▸ h2u)
    exact ⟨i, hα i ▸ hi.map φ⟩
  have hJO' : ∀ i j, JR (Fv F v) J i j ∈ O := hJO
  have hxO' : ∀ i, ratTup (F := F) (Fv F v) x 0 i ∈ O := hxO
  have hyO : ∀ i, y 0 i ∈ O := hy 0
  have htO : Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (ratTup (F := F) (Fv F v) x 0) ∈ O :=
    O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hsig _ (hyO i)) (hJO' i j)) (hxO' j)
  obtain ⟨i, hi⟩ := exists_isUnit_sub s (fun z => Subtype.ext (hss z)) (φ ⟨_, hb⟩) ⟨_, htO⟩
    ((hunit β hβ hb hb').map φ) (fun i => s ⟨_, huO i⟩) (fun i j hij => by
      rw [← map_sub]
      refine IsUnit.map s (IsUnit.of_mul_eq_one ⟨_, hdO i j⟩ (Subtype.ext ?_))
      change (inclR (F := F) (Fv F v) (u i) - inclR (F := F) (Fv F v) (u j)) *
        inclR (F := F) (Fv F v) (u i - u j)⁻¹ = 1
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (sub_ne_zero.2 (hui.ne hij)), map_one]) hloc
  obtain ⟨c, hc⟩ := hi.exists_right_inv
  have hxx : Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (ratTup (F := F) (Fv F v) x 0)
      (ratTup (F := F) (Fv F v) x 0) = algebraMap (Fv F v) _ (algebraMap F (Fv F v) β) := by
    have e := congrArg (inclR (F := F) (Fv F v)) hx
    simp only [hE, Formalism.UG.hform, map_sum, map_mul] at e
    refine Eq.trans e ?_
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes β
  have hyy : Formalism.UG.hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (y 0) =
      algebraMap (Fv F v) _ (algebraMap F (Fv F v) β) := by
    rw [← hq]
    exact GlobalTheory.SelfDualLatticeCompare.hR_self (Fv F v) h hJ (y 0)
  obtain ⟨g, hg, hgx, hgO, hgO'⟩ := exists_unitary (sigR (Fv F v) σ) hss O hsig (JR (Fv F v) J)
    (fun i j => congrArg (inclR (F := F) (Fv F v)) (hJ.1 i j)) hJO' _ _ hxO' hyO
    (algebraMap (Fv F v) _ (algebraMap F (Fv F v) β)) hxx hyy (inclR (Fv F v) (u i)) (huO i)
    (by rw [hsi, ← map_mul, hu, map_one]) c c.2 (congrArg Subtype.val hc)
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, fun i j => ⟨hgO i j, hgO' i j⟩⟩
  funext a
  rw [Subsingleton.elim a 0]
  exact hgx

end GlobalTheory.WittIntegral
