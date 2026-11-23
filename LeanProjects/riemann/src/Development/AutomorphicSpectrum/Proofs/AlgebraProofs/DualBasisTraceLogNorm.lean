import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealPadicGeneratorLogNormStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCoordinate

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RelDual

open Classical in

theorem sum_dual_embeddings {L E Ω : Type} [Field L] [Field E] [Algebra L E] [FiniteDimensional L E]
    [Algebra.IsSeparable L E] [Field Ω] [Algebra L Ω] [IsAlgClosed Ω] {f : ℕ} (b b' : Fin f → E)
    (hcard : Module.finrank L E = f)
    (h : ∀ i k, Algebra.trace L E (b' i * b k) = if i = k then 1 else 0) (τ τ' : E →ₐ[L] Ω) :
    ∑ k, τ (b' k) * τ' (b k) = if τ' = τ then 1 else 0 := by
  let M : Matrix (Fin f) (E →ₐ[L] Ω) Ω := fun i τ => τ (b' i)
  let N : Matrix (E →ₐ[L] Ω) (Fin f) Ω := fun τ k => τ (b k)
  have hMN : M * N = 1 := by
    ext i k
    rw [Matrix.mul_apply]
    have h1 := trace_eq_sum_embeddings (K := L) (L := E) (x := b' i * b k) Ω
    simp only [map_mul] at h1
    simp only [M, N]
    rw [← h1, h i k, Matrix.one_apply]
    split_ifs <;> simp
  have e : Fin f ≃ (E →ₐ[L] Ω) := Fintype.equivOfCardEq (by simp [AlgHom.card, hcard])
  have hNM : N * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMN
  have h2 := congrFun (congrFun hNM τ') τ
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  simp only [M, N] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Kf (H : Host E) : IntermediateField ℚ E := IntermediateField.adjoin ℚ {(H.rt : E)}

theorem rt_sq (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
  simpa using this

theorem d_pos (H : Host E) : 0 < H.d := H.d_prime.pos

theorem rt_ne (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq H
  rw [h] at h1
  have : (H.d : E) = 0 := by simpa using h1.symm
  exact (d_pos H).ne' (by exact_mod_cast this)

theorem two_weight_eq_one_add_root (H : Host E) : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  simpa [map_ofNat] using this

theorem rt_integral (H : Host E) : IsIntegral ℚ (H.rt : E) := Algebra.IsIntegral.isIntegral _

theorem exists_coord' (H : Host E) {y : E} (hy : y ∈ Algebra.adjoin ℚ {(H.rt : E)}) :
    ∃ u v : ℚ, y = u + v * (H.rt : E) :=
  _root_.UpperTheory.Reformulated.B.ExistsCoordinate.exists_coord H hy

theorem exists_coord (H : Host E) (x : Kf H) : ∃ u v : ℚ, (x : E) = u + v * (H.rt : E) := by
  refine exists_coord' H ?_
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (rt_integral H).isAlgebraic]
  exact x.2

theorem minpoly_rt (H : Host E) :
    minpoly ℚ (H.rt : E) = Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) := by
  have hd : (0 : ℚ) < H.d := by exact_mod_cast d_pos H
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) : Polynomial ℚ).natDegree = 2 :=
    Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) : Polynomial ℚ) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun x hx => ?_
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hx
    nlinarith [sq_nonneg x]
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ ?_).symm
  · simp [rt_sq H]
  · exact Polynomial.monic_X_pow_add_C _ (by norm_num)

theorem finrank_Kf (H : Host E) : Module.finrank ℚ (Kf H) = 2 := by
  rw [IntermediateField.adjoin.finrank (rt_integral H), minpoly_rt]
  exact Polynomial.natDegree_X_pow_add_C

def rtL (H : Host E) : Kf H := IntermediateField.AdjoinSimple.gen ℚ (H.rt : E)

@[simp] theorem coe_rtL (H : Host E) : ((rtL H : Kf H) : E) = H.rt := rfl

theorem trace_rtL (H : Host E) : Algebra.trace ℚ (Kf H) (rtL H) = 0 := by
  have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly
    (IntermediateField.adjoin.powerBasis (rt_integral H))
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, minpoly_rt] at h
  refine h.trans ?_
  rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [Polynomial.natDegree_X_pow_add_C]; norm_num),
    Polynomial.natDegree_X_pow_add_C]
  simp [Polynomial.coeff_X, Polynomial.coeff_C]

theorem trace_coord (H : Host E) (x : Kf H) (u v : ℚ) (hx : (x : E) = u + v * (H.rt : E)) :
    Algebra.trace ℚ (Kf H) x = 2 * u := by
  have h : x = algebraMap ℚ (Kf H) u + v • rtL H := by
    apply Subtype.ext
    rw [hx]
    simp [Algebra.smul_def]
  rw [h, map_add, map_smul, trace_rtL, Algebra.trace_algebraMap, finrank_Kf]
  simp

theorem trace_div_rt (H : Host E) (x : Kf H) (u v : ℚ) (hx : (x : E) = u + v * (H.rt : E)) :
    Algebra.trace ℚ (Kf H) (x * (rtL H)⁻¹) = 2 * v := by
  have hd : (H.d : E) ≠ 0 := by exact_mod_cast (d_pos H).ne'
  refine trace_coord H _ v (-u / H.d) ?_
  have h0 := rt_ne H
  have h2 := rt_sq H
  push_cast
  simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, coe_rtL, hx]
  field_simp
  linear_combination (u : E) * h2

abbrev Ord (H : Host E) : Subalgebra ℤ (𝓞 E) := Algebra.adjoin ℤ {H.w0}

theorem cm_generator_sq_quadratic_eq (H : Host E) : ∃ t : ℤ, H.w0 ^ 2 = H.w0 - t := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, H.d + 1 = 4 * t := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  refine ⟨t, ?_⟩
  apply RingOfIntegers.coe_injective
  have h1 := two_weight_eq_one_add_root H
  have h2 := rt_sq H
  have h3 : (H.d : E) + 1 = 4 * t := by exact_mod_cast ht
  have h4 : (H.rt : E) = 2 * H.w0 - 1 := by rw [h1]; ring
  rw [h4] at h2
  have h5 : (4 : E) * ((H.w0 : E) ^ 2 - (H.w0 - t)) = 0 := by
    linear_combination h2 - h3
  have h6 : (H.w0 : E) ^ 2 - (H.w0 - t) = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · norm_num at h
    · exact h
  have h7 : (H.w0 : E) ^ 2 = H.w0 - t := sub_eq_zero.1 h6
  simpa using h7

theorem ord_coord (H : Host E) {c : 𝓞 E} (hc : c ∈ Ord H) : ∃ m n : ℤ, c = m + n * H.w0 := by
  obtain ⟨t, ht⟩ := cm_generator_sq_quadratic_eq H
  induction hc using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨0, 1, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨u', v', rfl⟩ := hb
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨u', v', rfl⟩ := hb
    refine ⟨u * u' - v * v' * t, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination ((v : 𝓞 E) * v') * ht

theorem cmHalfIntegralGenerator_mem_algebraicClosure (H : Host E) : H.w0 ∈ Ord H := Algebra.self_mem_adjoin_singleton ℤ _

theorem int_mem (H : Host E) (m : ℤ) : (m : 𝓞 E) ∈ Ord H := by
  simpa using (Ord H).algebraMap_mem m

theorem weight_coordinate_half (H : Host E) : (H.w0 : E) = (1 / 2 : ℚ) + (1 / 2 : ℚ) * (H.rt : E) := by
  have h := two_weight_eq_one_add_root H
  push_cast
  linear_combination (1 / 2 : E) * h

theorem mem_Kf_of_ord (H : Host E) {c : 𝓞 E} (hc : c ∈ Ord H) : (c : E) ∈ Kf H := by
  obtain ⟨m, n, rfl⟩ := ord_coord H hc
  have h1 : (H.rt : E) ∈ Kf H := IntermediateField.mem_adjoin_simple_self ℚ _
  have h2 : (H.w0 : E) ∈ Kf H := by
    rw [weight_coordinate_half]
    exact add_mem ((Kf H).algebraMap_mem _) (mul_mem ((Kf H).algebraMap_mem _) h1)
  have h3 : ∀ z : ℤ, (z : E) ∈ Kf H := fun z => by simpa using (Kf H).algebraMap_mem (z : ℚ)
  simpa using add_mem (h3 m) (mul_mem (h3 n) h2)

def w0L (H : Host E) : Kf H := ⟨H.w0, mem_Kf_of_ord H (cmHalfIntegralGenerator_mem_algebraicClosure H)⟩

@[simp] theorem coe_w0L (H : Host E) : ((w0L H : Kf H) : E) = H.w0 := rfl

theorem trace_div_rt_ord (H : Host E) (x : Kf H) {c : 𝓞 E} (hc : c ∈ Ord H) (hx : (x : E) = c) :
    ∃ z : ℤ, Algebra.trace ℚ (Kf H) (x * (rtL H)⁻¹) = z := by
  obtain ⟨m, n, rfl⟩ := ord_coord H hc
  refine ⟨n, ?_⟩
  rw [trace_div_rt H x (m + n / 2 : ℚ) (n / 2 : ℚ) ?_]
  · ring
  · rw [hx]
    have h := two_weight_eq_one_add_root H
    rw [show (((m : 𝓞 E) + n * H.w0 : 𝓞 E) : E) = (m : E) + n * (H.w0 : E) by simp]
    push_cast
    linear_combination ((n : E) / 2) * h

theorem ord_of_trace (H : Host E) (x : Kf H)
    (h1 : ∃ z : ℤ, Algebra.trace ℚ (Kf H) (x * (rtL H)⁻¹) = z)
    (h2 : ∃ z : ℤ, Algebra.trace ℚ (Kf H) (x * w0L H * (rtL H)⁻¹) = z) :
    ∃ c ∈ Ord H, (c : E) = x := by
  obtain ⟨u, v, hx⟩ := exists_coord H x
  obtain ⟨z1, hz1⟩ := h1
  obtain ⟨z2, hz2⟩ := h2
  rw [trace_div_rt H x u v hx] at hz1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, H.d + 1 = 4 * t := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have ht' : (H.d : ℚ) = 4 * t - 1 := by
    have : (H.d : ℚ) + 1 = 4 * t := by exact_mod_cast ht
    linarith
  have hxw : ((x * w0L H : Kf H) : E) = ((u - v * H.d) / 2 : ℚ) + ((u + v) / 2 : ℚ) * (H.rt : E) := by
    have h := rt_sq H
    simp only [IntermediateField.coe_mul, coe_w0L, hx]
    rw [weight_coordinate_half]
    push_cast
    linear_combination ((v : E) / 2) * h
  rw [trace_div_rt H _ _ _ hxw] at hz2
  have hv : v = z1 / 2 := by linarith
  have hu : u = z2 - z1 / 2 := by
    have : 2 * ((u + v) / 2) = z2 := hz2
    linarith
  refine ⟨(z2 : 𝓞 E) - z1 + z1 * H.w0 , ?_, ?_⟩
  · exact add_mem (sub_mem (int_mem H _) (int_mem H _)) (mul_mem (int_mem H _) (cmHalfIntegralGenerator_mem_algebraicClosure H))
  · rw [hx, hu, hv]
    have h := two_weight_eq_one_add_root H
    rw [show (((z2 : 𝓞 E) - z1 + z1 * H.w0 : 𝓞 E) : E) = (z2 : E) - z1 + z1 * (H.w0 : E) by simp]
    push_cast
    linear_combination ((z1 : E) / 2) * h

theorem trace_mul_coe (H : Host E) (y : E) (l : Kf H) :
    Algebra.trace ℚ E (y * (l : E)) = Algebra.trace ℚ (Kf H) (Algebra.trace (Kf H) E y * l) := by
  have h : y * (l : E) = l • y := by
    rw [Algebra.smul_def, mul_comm]
    rfl
  rw [h, ← Algebra.trace_trace (S := Kf H), map_smul, smul_eq_mul, mul_comm]

theorem bridge_down (H : Host E) (y : E)
    (h : ∀ a : 𝓞 E, ∃ c ∈ Ord H, (c : E) = (Algebra.trace (Kf H) E (y * a) : Kf H)) (a : 𝓞 E) :
    ∃ z : ℤ, Algebra.trace ℚ E (y / (H.rt : E) * a) = z := by
  obtain ⟨c, hc, hca⟩ := h a
  have e : y / (H.rt : E) * a = y * a * (((rtL H)⁻¹ : Kf H) : E) := by
    simp only [IntermediateField.coe_inv, coe_rtL]
    field_simp [rt_ne H]
  rw [e, trace_mul_coe]
  exact trace_div_rt_ord H _ hc hca.symm

theorem bridge_up (H : Host E) (y : E)
    (h : ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (y / (H.rt : E) * a) = z) (a : 𝓞 E) :
    ∃ c ∈ Ord H, (c : E) = (Algebra.trace (Kf H) E (y * a) : Kf H) := by
  refine ord_of_trace H _ ?_ ?_
  · obtain ⟨z, hz⟩ := h a
    refine ⟨z, ?_⟩
    rw [← trace_mul_coe, ← hz]
    congr 1
    simp only [IntermediateField.coe_inv, coe_rtL]
    field_simp [rt_ne H]
  · obtain ⟨z, hz⟩ := h (a * H.w0)
    refine ⟨z, ?_⟩
    rw [_root_.mul_assoc, ← trace_mul_coe, ← hz]
    congr 1
    simp only [IntermediateField.coe_inv, IntermediateField.coe_mul, coe_rtL, coe_w0L]
    have := rt_ne H
    simp only [map_mul, RingOfIntegers.coe_eq_algebraMap]
    field_simp

theorem coe_int_add_mul (p q : ℤ) (w : 𝓞 E) :
    (((p : 𝓞 E) + (q : 𝓞 E) * w : 𝓞 E) : E) = (p : E) + (q : E) * (w : E) := by simp

theorem exists_int_mul (H : Host E) (x : Kf H) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ c ∈ Ord H, (c : E) = N * x := by
  obtain ⟨u, v, hx⟩ := exists_coord H x
  refine ⟨u.den * v.den, by simp, (u.num * v.den - v.num * u.den : ℤ) + (2 * v.num * u.den : ℤ) * H.w0,
    add_mem (int_mem H _) (mul_mem (int_mem H _) (cmHalfIntegralGenerator_mem_algebraicClosure H)), ?_⟩
  have hu : (u.den : E) * (u : E) = u.num := by exact_mod_cast Rat.den_mul_eq_num u
  have hv : (v.den : E) * (v : E) = v.num := by exact_mod_cast Rat.den_mul_eq_num v
  have h := two_weight_eq_one_add_root H
  rw [hx]
  rw [coe_int_add_mul]
  push_cast
  linear_combination ((v.num : E) * u.den) * h - (v.den : E) * hu - (u.den : E) * (H.rt : E) * hv

theorem exists_basis (H : Host E) (ℓ f : ℕ) (b : Fin f → 𝓞 E) (h : IsLocBasis (Ord H) ℓ b) :
    ∃ B : Module.Basis (Fin f) (Kf H) E, ∀ k, B k = (b k : E) := by
  classical
  obtain ⟨hli, n, hn, hspan⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (dvd_zero _)
  have inj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective (𝓞 E) E
  have li : LinearIndependent (Kf H) (fun k => (b k : E)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose N hN c hc hcN using fun k => exists_int_mul H (g k)
    set P : ℕ := ∏ k, N k with hPdef
    have hP : (P : E) ≠ 0 := by
      have : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hN k
      exact_mod_cast this
    have hdiv : ∀ k, ∃ e : ℕ, P = N k * e := fun k => Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    choose e he using hdiv
    let c' : Fin f → Ord H := fun k =>
      ⟨((e k : ℤ) : 𝓞 E) * c k, mul_mem (int_mem H _) (hc k)⟩
    have hc' : ∀ k, (((c' k : Ord H) : 𝓞 E) : E) = P * (g k : E) := fun k => by
      have : (((c' k : Ord H) : 𝓞 E) : E) = (e k : E) * (c k : E) := by simp [c']
      rw [this, hcN k, he k]
      push_cast
      ring
    have hz : ∑ k, c' k • b k = 0 := by
      apply inj
      rw [map_sum, map_zero]
      have h1 : ∀ k, algebraMap (𝓞 E) E (c' k • b k) = P * (g k • (b k : E)) := fun k => by
        rw [Subalgebra.smul_def, smul_eq_mul, map_mul, Algebra.smul_def, ← _root_.mul_assoc]
        exact congrArg (· * _) (hc' k)
      simp only [h1]
      rw [← Finset.mul_sum, hg, mul_zero]
    have h2 := Fintype.linearIndependent_iff.1 hli c' hz i
    have h3 := hc' i
    rw [h2] at h3
    have h4 : (P : E) * (g i : E) = 0 := by simpa using h3.symm
    have h5 : (g i : E) = 0 := (mul_eq_zero.1 h4).resolve_left hP
    exact Subtype.ext h5
  have sp : ⊤ ≤ Submodule.span (Kf H) (Set.range fun k => (b k : E)) := by
    intro y _
    obtain ⟨N, hN, hI⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y)).exists_integral_multiple
    have hmap : ∀ z ∈ Submodule.span (Ord H) (Set.range b),
        algebraMap (𝓞 E) E z ∈ Submodule.span (Kf H) (Set.range fun k => (b k : E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        have : algebraMap (𝓞 E) E (a • x) = (⟨_, mem_Kf_of_ord H a.2⟩ : Kf H) • algebraMap (𝓞 E) E x := by
          rw [Subalgebra.smul_def, smul_eq_mul, map_mul, Algebra.smul_def]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    let y' : 𝓞 E := IsIntegralClosure.mk' (𝓞 E) (N • y) hI
    have hy' : algebraMap (𝓞 E) E y' = N • y := IsIntegralClosure.algebraMap_mk' _ _ _
    have h1 := hmap _ (hspan y')
    have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
    have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
    have h2 : y = algebraMap ℚ (Kf H) ((n : ℚ) * N)⁻¹ • algebraMap (𝓞 E) E (n • y') := by
      have e : ((algebraMap ℚ (Kf H) ((n : ℚ) * N)⁻¹ : Kf H) : E) = ((n : E) * N)⁻¹ := by
        show algebraMap ℚ E ((n : ℚ) * N)⁻¹ = _
        simp
      rw [map_nsmul, hy', Algebra.smul_def, IntermediateField.algebraMap_apply, e]
      simp only [zsmul_eq_mul, nsmul_eq_mul]
      field_simp
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  exact ⟨Module.Basis.mk li sp, fun k => by simp⟩

theorem int_of_mem_dual {c x : E}
    (hc : ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (c * a) = z) {δ : 𝓞 E}
    (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) (hx : x = c * δ) : ∃ r : 𝓞 E, (r : E) = x := by
  have h1 : (δ : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule _ _).mpr ⟨δ, hδ, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ] at h1
  have h2 : c ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨z, hz⟩ := hc y
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hz.symm
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp ((Submodule.mem_div_iff_forall_mul_mem.mp h1) _ h2)
  refine ⟨r, ?_⟩
  rw [hx, _root_.mul_comm]
  exact hr

theorem mem_dual_of_int {c : E}
    (hc : ∀ x ∈ differentIdeal ℤ (𝓞 E), ∃ r : 𝓞 E, (r : E) = c * x) (a : 𝓞 E) :
    ∃ z : ℤ, Algebra.trace ℚ E (c * a) = z := by
  have hD : (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hI : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    rw [coeIdeal_differentIdeal ℤ ℚ]
    exact inv_ne_zero hD
  have h1 : c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) /
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_div_iff_of_ne_zero hI]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    obtain ⟨r, hr⟩ := hc x hx
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨r, hr⟩
  have h0 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := one_ne_zero
  rw [coeIdeal_differentIdeal ℤ ℚ, one_div, inv_inv, FractionalIdeal.mem_dual h0] at h1
  obtain ⟨z, hz⟩ := h1 (a : E) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
  refine ⟨z, ?_⟩
  rw [Algebra.traceForm_apply] at hz
  simpa using hz.symm

theorem norm_le_one_of_integral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le_one {p : ℕ} [Fact p.Prime] (j : E →+* ℂ_[p]) (a : 𝓞 E) : ‖j (a : E)‖ ≤ 1 :=
  norm_le_one_of_integral (map_isIntegral_int j a.isIntegral_coe)

theorem norm_nat_eq_one {p : ℕ} [Fact p.Prime] (j : E →+* ℂ_[p]) {n : ℕ} (h : ¬ p ∣ n) :
    ‖j (n : E)‖ = 1 := by
  have e : j (n : E) = algebraMap ℚ_[p] ℂ_[p] (n : ℚ_[p]) := by
    rw [map_natCast, map_natCast]
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.2 h)

theorem agree_on_Kf (H : Host E) {K : Type} [Field K] (σ σ' : E →+* K)
    (h : σ (H.rt : E) = σ' (H.rt : E)) (l : Kf H) : σ (l : E) = σ' (l : E) := by
  obtain ⟨u, v, hx⟩ := exists_coord H l
  rw [hx]
  simp only [map_add, map_mul, map_ratCast, h]

theorem trace_dual_apply (H : Host E) {f : ℕ} (B : Module.Basis (Fin f) (Kf H) E) (i k : Fin f) :
    Algebra.trace (Kf H) E (B.traceDual i * B k) = if i = k then 1 else 0 := by
  have h := B.traceDual_repr_apply (B.traceDual i) k
  rw [Module.Basis.repr_self, Finsupp.single_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem orth_of_dual (H : Host E) {f : ℕ} (B : Module.Basis (Fin f) (Kf H) E) (K : Type) [Field K]
    (σ σ' : E →+* K) (h : σ (H.rt : E) = σ' (H.rt : E)) :
    (σ = σ' → ∑ k, σ (B.traceDual k) * σ' (B k) = 1) ∧
      (σ ≠ σ' → ∑ k, σ (B.traceDual k) * σ' (B k) = 0) := by
  classical
  let Ω := AlgebraicClosure K
  let em : K →+* Ω := algebraMap K Ω
  have hem : Function.Injective em := em.injective
  letI : Algebra (Kf H) Ω := (em.comp (σ.comp (algebraMap (Kf H) E))).toAlgebra
  let τ : E →ₐ[Kf H] Ω := { em.comp σ with commutes' := fun l => rfl }
  let τ' : E →ₐ[Kf H] Ω :=
    { em.comp σ' with
      commutes' := fun l => by
        show em (σ' (l : E)) = em (σ (l : E))
        rw [agree_on_Kf H σ σ' h l] }
  have hs := sum_dual_embeddings (Ω := Ω) B B.traceDual
    (by rw [Module.finrank_eq_card_basis B]; simp) (trace_dual_apply H B) τ τ'
  have hm : em (∑ k, σ (B.traceDual k) * σ' (B k)) = ∑ k, τ (B.traceDual k) * τ' (B k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul em _ _
  rw [← hm] at hs
  have heq : τ' = τ ↔ σ = σ' := by
    constructor
    · intro e
      ext x
      exact (hem (congrArg (fun g : E →ₐ[Kf H] Ω => g x) e)).symm
    · rintro rfl
      rfl
  constructor
  · intro e
    rw [if_pos (heq.2 e)] at hs
    exact hem (hs.trans (map_one em).symm)
  · intro e
    rw [if_neg (fun x => e (heq.1 x))] at hs
    exact hem (hs.trans (map_zero em).symm)

theorem trace_dual_mem (H : Host E) {f : ℕ} (B : Module.Basis (Fin f) (Kf H) E) (b : Fin f → 𝓞 E)
    (hB : ∀ k, B k = (b k : E)) (n : ℕ) (hspan : ∀ y : 𝓞 E, n • y ∈ Submodule.span (Ord H) (Set.range b))
    (k : Fin f) (a : 𝓞 E) :
    ∃ c ∈ Ord H, (c : E) = (Algebra.trace (Kf H) E ((n : E) * B.traceDual k * a) : Kf H) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Ord H)).1 (hspan a)
  let cK : Fin f → Kf H := fun i => ⟨(((c i : Ord H) : 𝓞 E) : E), mem_Kf_of_ord H (c i).2⟩
  have hx : (n : E) * a = ∑ i, cK i • B i := by
    have h1 := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_sum, map_nsmul] at h1
    rw [nsmul_eq_mul] at h1
    refine h1.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Subalgebra.smul_def, smul_eq_mul, map_mul, Algebra.smul_def, hB]
    rfl
  have h2 := B.traceDual.traceDual_repr_apply ((n : E) * a) k
  rw [Module.Basis.traceDual_traceDual, hx, Module.Basis.repr_sum_self, Algebra.traceForm_apply, ← hx] at h2
  refine ⟨c k, (c k).2, ?_⟩
  have h3 : (n : E) * B.traceDual k * a = (n : E) * a * B.traceDual k := by ring
  rw [h3, ← h2]

theorem relative_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (f : ℕ) (b : Fin f → 𝓞 E), IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → ∃ b' : Fin f → E, (∀ (K : Type) [Field K] (σ σ' : E →+* K), σ (H.rt : E) = σ' (H.rt : E) → (σ = σ' → ∑ k, σ (b' k) * σ' (b k : E) = 1) ∧ (σ ≠ σ' → ∑ k, σ (b' k) * σ' (b k : E) = 0)) ∧ ∀ j : E →+* ℂ_[ℓ], 0 < (⨆ k, ‖j (b' k)‖) ∧ Real.log (⨆ k, ‖j (b' k)‖) = Real.log ‖j (H.rt : E)‖ - logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ H ℓ f b hb
  obtain ⟨B, hB⟩ := exists_basis H ℓ f b hb
  refine ⟨B.traceDual, fun K _ σ σ' h => ?_, fun j => ?_⟩
  · have := orth_of_dual H B K σ σ' h
    simpa only [hB] using this
  obtain ⟨-, n, hn, hspan⟩ := hb
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨δ, hδ, hδ0, ⟨n0, hn0, hn0'⟩, hlog⟩ := GlobalTheory.T.ideal_padic_generator_log_norm E (differentIdeal ℤ (𝓞 E)) ℓ hne
  have hrt := rt_ne H
  have hδE : (δ : E) ≠ 0 := by simpa using hδ0
  have hjrt : ‖j (H.rt : E)‖ ≠ 0 := by simpa using hrt
  have hjδ : ‖j (δ : E)‖ ≠ 0 := by simpa using hδE
  have hjrt' : 0 < ‖j (H.rt : E)‖ := lt_of_le_of_ne (norm_nonneg _) hjrt.symm
  have hjδ' : 0 < ‖j (δ : E)‖ := lt_of_le_of_ne (norm_nonneg _) hjδ.symm
  set C : ℝ := ‖j (H.rt : E)‖ / ‖j (δ : E)‖ with hC
  have hCpos : 0 < C := div_pos hjrt' hjδ'

  have hup : ∀ k, ‖j (B.traceDual k)‖ ≤ C := by
    intro k
    have h1 := bridge_down H ((n : E) * B.traceDual k)
      (fun a => trace_dual_mem H B b hB n hspan k a)
    obtain ⟨r, hr⟩ := int_of_mem_dual h1 hδ rfl
    have h2 := norm_int_le_one j r
    rw [hr, map_mul, map_div₀, map_mul, norm_mul, norm_div, norm_mul, norm_nat_eq_one j hn, _root_.one_mul] at h2
    rw [hC, le_div_iff₀ hjδ']
    rwa [div_mul_eq_mul_div, div_le_one hjrt'] at h2

  have hnn : 0 ≤ ⨆ k, ‖j (B.traceDual k)‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hbdd : BddAbove (Set.range fun k => ‖j (B.traceDual k)‖) := (Set.finite_range _).bddAbove
  have hlow : C ≤ ⨆ k, ‖j (B.traceDual k)‖ := by
    set y : E := (n0 : E) * H.rt / δ with hy
    have hc : ∀ x ∈ differentIdeal ℤ (𝓞 E), ∃ r : 𝓞 E, (r : E) = (n0 : E) / δ * x := by
      intro x hx
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hn0' x hx)
      refine ⟨s, ?_⟩
      have h1 := congrArg (algebraMap (𝓞 E) E) hs
      rw [map_mul, map_mul, map_natCast] at h1
      show algebraMap (𝓞 E) E s = _
      field_simp
      exact h1
    have h1 : ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (y / (H.rt : E) * a) = z := by
      intro a
      have e : y / (H.rt : E) = (n0 : E) / δ := by
        rw [hy]
        field_simp
      rw [e]
      exact mem_dual_of_int hc a
    have h2 := bridge_up H y h1
    have h3 : y = ∑ k, (B.traceDual.repr y k) • B.traceDual k := (B.traceDual.sum_repr y).symm
    have h4 : ‖j y‖ ≤ ⨆ k, ‖j (B.traceDual k)‖ := by
      rw [h3, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun k _ => ?_
      obtain ⟨c, -, hc'⟩ := h2 (b k)
      have e : B.traceDual.repr y k = Algebra.trace (Kf H) E (y * (b k : E)) := by
        rw [B.traceDual_repr_apply, Algebra.traceForm_apply, hB]
      rw [e, Algebra.smul_def, map_mul, norm_mul]
      have e2 : j (algebraMap (Kf H) E (Algebra.trace (Kf H) E (y * (b k : E)))) = j (c : E) := by
        rw [hc']
        rfl
      rw [e2]
      calc ‖j (c : E)‖ * ‖j (B.traceDual k)‖ ≤ 1 * ‖j (B.traceDual k)‖ :=
            mul_le_mul_of_nonneg_right (norm_int_le_one j c) (norm_nonneg _)
        _ = ‖j (B.traceDual k)‖ := _root_.one_mul _
        _ ≤ _ := le_ciSup hbdd k
    have h5 : ‖j y‖ = C := by
      rw [hy, map_div₀, map_mul, norm_div, norm_mul, norm_nat_eq_one j hn0, _root_.one_mul]
    rwa [h5] at h4
  have heq : (⨆ k, ‖j (B.traceDual k)‖) = C := le_antisymm (Real.iSup_le hup hCpos.le) hlow
  rw [heq]
  refine ⟨hCpos, ?_⟩
  rw [hC, Real.log_div hjrt hjδ, hlog]

end GlobalTheory.CompanionTheory.Ar.RelDual
