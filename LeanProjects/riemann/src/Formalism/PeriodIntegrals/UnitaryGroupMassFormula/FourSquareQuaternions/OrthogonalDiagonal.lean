import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.FourSqOf

noncomputable section
open scoped BigOperators
open Module

namespace PI.KerIso.FourSqW

section Conj

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : K := Classical.choose (hc.2.1 k)

theorem conjFun_spec (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    algebraMap K E (conjFun cj hc k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (hc.2.1 k)).symm

theorem conjFun_conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    conjFun cj hc (conjFun cj hc k) = k :=
  (algebraMap K E).injective (by rw [conjFun_spec, conjFun_spec, hc.1])

def conjK (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) : K ≃+* K where
  toFun := conjFun cj hc
  invFun := conjFun cj hc
  left_inv := conjFun_conjFun cj hc
  right_inv := conjFun_conjFun cj hc
  map_mul' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_mul, map_mul, map_mul, conjFun_spec, conjFun_spec])
  map_add' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_add, map_add, map_add, conjFun_spec, conjFun_spec])

theorem conjK_apply (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : conjK cj hc k = conjFun cj hc k := rfl

theorem trace_cj (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (z : E) :
    algebraMap K E (Algebra.trace K E (cj z)) = cj (algebraMap K E (Algebra.trace K E z)) := by
  have he : (algebraMap K E).comp (conjK cj hc : K →+* K) = (cj.toRingEquiv : E →+* E).comp (algebraMap K E) := by
    ext k
    simp only [RingHom.comp_apply, RingHom.coe_coe, conjK_apply, conjFun_spec]
    rfl
  have h1 := Algebra.trace_eq_of_equiv_equiv (conjK cj hc) cj.toRingEquiv he z
  have h2 : conjK cj hc (Algebra.trace K E z) = Algebra.trace K E (cj z) := by
    rw [h1, RingEquiv.apply_symm_apply]
    rfl
  rw [← h2, conjK_apply, conjFun_spec]

theorem fixed_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2) (k : K)
    (hk : cj (algebraMap K E k) = algebraMap K E k) : ∃ r : ℚ, k = (r : K) := by
  let φ : K →ₗ[ℚ] E := (IsScalarTower.toAlgHom ℚ K E).toLinearMap
  let L : K →ₗ[ℚ] E := cj.toLinearMap.comp φ - φ
  have hL : ∀ x, L x = cj (algebraMap K E x) - algebraMap K E x := fun x => rfl
  have hker : ∀ x, x ∈ LinearMap.ker L ↔ cj (algebraMap K E x) = algebraMap K E x := by
    intro x; rw [LinearMap.mem_ker, hL, sub_eq_zero]
  have hrange : LinearMap.range L ≠ ⊥ := by
    obtain ⟨k0, hk0⟩ := hc.2.2
    intro h
    rw [LinearMap.range_eq_bot] at h
    apply hk0
    have := congrArg (fun f : K →ₗ[ℚ] E => f k0) h
    simp only [LinearMap.zero_apply, hL, sub_eq_zero] at this
    exact this
  have hr1 : 1 ≤ finrank ℚ (LinearMap.range L) := Submodule.one_le_finrank_iff.mpr hrange
  have hsum := L.finrank_range_add_finrank_ker
  have hk1 : finrank ℚ (LinearMap.ker L) ≤ 1 := by omega
  have h1mem : (1 : K) ∈ LinearMap.ker L := by
    rw [hker, map_one, map_one]
  have hle : Submodule.span ℚ {(1 : K)} ≤ LinearMap.ker L := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1mem
  have hfr : finrank ℚ (Submodule.span ℚ {(1 : K)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hkmem : k ∈ Submodule.span ℚ {(1 : K)} := by rw [heq, hker]; exact hk
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hkmem
  exact ⟨r, by rw [← hr, Rat.smul_one_eq_cast]⟩

end Conj

section Orth

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def trL (cj : E ≃ₐ[ℚ] E) (y : E) : E →ₗ[K] K :=
  (Algebra.trace K E).comp (LinearMap.mulRight K (cj y))

theorem trL_apply (cj : E ≃ₐ[ℚ] E) (y x : E) : trL (K := K) cj y x = Algebra.trace K E (x * cj y) := rfl

theorem tr_swap (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E) :
    algebraMap K E (Algebra.trace K E (y * cj x)) = cj (algebraMap K E (Algebra.trace K E (x * cj y))) := by
  rw [← trace_cj cj hc, map_mul cj, hc.1, mul_comm]

theorem tr_swap_zero (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E)
    (h : Algebra.trace K E (x * cj y) = 0) : Algebra.trace K E (y * cj x) = 0 := by
  apply (algebraMap K E).injective
  rw [tr_swap cj hc, h, map_zero, map_zero]

theorem tr_self_ne (cj : E ≃ₐ[ℚ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x))
    (x : E) (hx : x ≠ 0) : Algebra.trace K E (x * cj x) ≠ 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro h
  have := hpos x hx
  rw [← Algebra.trace_trace (S := K), h, map_zero] at this
  exact lt_irrefl _ this

theorem tr_self_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (x : E) (hx : x ≠ 0) :
    ∃ r : ℚ, 0 < r ∧ Algebra.trace K E (x * cj x) = (r : K) := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  have hfix : cj (algebraMap K E (Algebra.trace K E (x * cj x))) = algebraMap K E (Algebra.trace K E (x * cj x)) :=
    (tr_swap cj hc x x).symm
  obtain ⟨r, hr⟩ := fixed_rat cj hc h2 _ hfix
  refine ⟨r, ?_, hr⟩
  have := hpos x hx
  rw [← Algebra.trace_trace (S := K), hr] at this
  have h3 : Algebra.trace ℚ K (r : K) = 2 * r := by
    rw [show (r : K) = algebraMap ℚ K r from rfl, Algebra.trace_algebraMap, h2, nsmul_eq_mul]
    norm_num
  rw [h3] at this
  linarith

theorem exists_orth (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) :
    ∀ m : ℕ, m ≤ finrank K E → ∃ e : Fin m → E, (∀ i, e i ≠ 0) ∧
      ∀ i j, i ≠ j → Algebra.trace K E (e i * cj (e j)) = 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨e, he0, heo⟩ := ih (by omega)
    let F : E →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => trL cj (e i))
    have hF : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fin_fun]; omega)
    obtain ⟨x, hxk, hx0⟩ := (Submodule.ne_bot_iff _).mp hF
    have hxo : ∀ i, Algebra.trace K E (x * cj (e i)) = 0 := by
      intro i
      have := congrArg (fun f => f i) (LinearMap.mem_ker.mp hxk)
      simpa [F, trL_apply] using this
    refine ⟨Fin.snoc e x, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx0
      · simpa using he0 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using hxo j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using tr_swap_zero cj hc _ _ (hxo i)
        | cast j =>
          have : i ≠ j := fun h => hij (by rw [h])
          simpa using heo i j this

theorem orth_linInd {n : Type} [Fintype n] (cj : E ≃ₐ[ℚ] E)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (v : n → E)
    (hv0 : ∀ i, v i ≠ 0) (hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (trL (K := K) cj (v j)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single j] at h
  · rw [map_smul, trL_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (tr_self_ne cj hpos _ (hv0 j))
  · intro i _ hij
    rw [map_smul, trL_apply, hvo i j hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem orthogonal_diagonal : OrthDiag := by
  intro K E _ _ _ _ _ cj n _ h2 hn hc hpos
  classical
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  obtain ⟨e, he0, heo⟩ := exists_orth (K := K) cj hc hpos (finrank K E) le_rfl
  let σ : n ≃ Fin (finrank K E) := Fintype.equivFinOfCardEq hn
  let v : n → E := fun i => e (σ i)
  have hv0 : ∀ i, v i ≠ 0 := fun i => he0 _
  have hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0 :=
    fun i j hij => heo _ _ (fun h => hij (σ.injective h))
  have hli := orth_linInd (K := K) cj hpos v hv0 hvo
  let b : Basis n K E := basisOfLinearIndependentOfCardEqFinrank' v hli hn
  have hb : ∀ i, b i = v i := fun i => by simp [b]
  choose q hq0 hq using fun i => tr_self_rat (K := K) cj hc h2 hpos (v i) (hv0 i)
  refine ⟨b, q, hq0, ?_⟩

  have hcol : ∀ y i, Algebra.trace K E (y * cj (v i)) = b.repr y i * (q i : K) := by
    intro y i
    have h := congrArg (trL (K := K) cj (v i)) (b.sum_repr y)
    rw [map_sum, Finset.sum_eq_single i] at h
    · rw [← trL_apply, ← h, map_smul, trL_apply, hb, hq, smul_eq_mul]
    · intro j _ hji
      rw [map_smul, trL_apply, hb, hvo j i hji, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  intro x y
  have hx := congrArg (fun z => algebraMap K E (trL (K := K) cj y z)) (b.sum_repr x)
  simp only [map_sum, map_smul, trL_apply, smul_eq_mul, map_mul] at hx
  rw [← hx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hb, tr_swap cj hc, hcol, map_mul, map_mul, map_ratCast, map_ratCast]
  ring

end Orth

end PI.KerIso.FourSqW
