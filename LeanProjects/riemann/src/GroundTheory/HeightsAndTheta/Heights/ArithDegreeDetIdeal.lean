import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin r → 𝓞 K)) : Ideal (𝓞 K) :=
  Ideal.span {d | ∃ v : Fin r → Fin r → 𝓞 K, (∀ i, v i ∈ E) ∧ (Matrix.of v).det = d}

omit [NumberField K] in
theorem det_mem_detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin r → 𝓞 K)) (v : Fin r → Fin r → 𝓞 K)
    (hv : ∀ i, v i ∈ E) : (Matrix.of v).det ∈ detIdeal E :=
  Ideal.subset_span ⟨v, hv, rfl⟩

def consZero (r : ℕ) : (Fin r → 𝓞 K) →ₗ[𝓞 K] (Fin (r + 1) → 𝓞 K) where
  toFun y := Fin.cons 0 y
  map_add' y z := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> simp
  map_smul' c y := by
    ext i
    refine Fin.cases ?_ (fun k ↦ ?_) i <;> simp

omit [NumberField K] in
theorem consZero_zero {r : ℕ} (y : Fin r → 𝓞 K) : consZero r y 0 = 0 := rfl

omit [NumberField K] in

theorem range_consZero (r : ℕ) :
    LinearMap.range (consZero (K := K) r) = LinearMap.ker (LinearMap.proj 0) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · rintro ⟨y, rfl⟩; rfl
  · intro hx
    refine ⟨Fin.tail x, ?_⟩
    rw [← Fin.cons_self_tail x, hx]
    rfl

omit [NumberField K] in

theorem card_quotient_succ {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    Nat.card ((Fin (r + 1) → 𝓞 K) ⧸ E) =
      Nat.card ((Fin r → 𝓞 K) ⧸ E.comap (consZero r)) *
        Nat.card (𝓞 K ⧸ E.map (LinearMap.proj 0)) := by
  set π : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K := LinearMap.proj 0
  set S := E ⊔ LinearMap.ker π
  rw [← Submodule.card_quotient_mul_card_quotient S E le_sup_left]
  congr 1
  · have hS : S.map E.mkQ = LinearMap.range (E.mkQ ∘ₗ consZero r) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp,
        range_consZero]
    have hker : LinearMap.ker (E.mkQ ∘ₗ consZero r) = E.comap (consZero r) := by
      ext y
      simp [Submodule.Quotient.mk_eq_zero]
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (E.map π).mkQ ∘ₗ π
    have hπ : Function.Surjective π := fun a ↦ ⟨fun _ ↦ a, rfl⟩
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp hπ
    have hker : LinearMap.ker φ = S := by
      ext x
      simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_map, S,
        Submodule.mem_sup]
      constructor
      · rintro ⟨e, he, hex⟩
        refine ⟨e, he, x - e, ?_, add_sub_cancel _ _⟩
        show π (x - e) = 0
        rw [map_sub, hex, sub_self]
      · rintro ⟨e, he, k, hk, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [map_add, LinearMap.mem_ker.mp hk, add_zero]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv

omit [NumberField K] in

theorem mul_le_detIdeal {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) ≤ detIdeal E := by
  rw [Ideal.mul_le]
  intro a ha d hd
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp ha
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨v', hv', rfl⟩ := hd
    let v : Fin (r + 1) → Fin (r + 1) → 𝓞 K := Fin.cons w (fun k ↦ consZero r (v' k))
    have hv : ∀ i, v i ∈ E := by
      intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · exact hw
      · exact hv' k
    have hdet : (Matrix.of v).det = w 0 * (Matrix.of v').det := by
      rw [det_succ_column_zero, Fin.sum_univ_succ]
      simp only [v, of_apply, Fin.cons_zero, Fin.cons_succ, consZero_zero, Fin.succAbove_zero,
        Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      congr 2
    rw [LinearMap.proj_apply, ← hdet]
    exact det_mem_detIdeal E v hv
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ c hx

theorem detIdeal_le_mul {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    detIdeal E ≤ E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) := by
  classical
  set π : (Fin (r + 1) → 𝓞 K) →ₗ[𝓞 K] 𝓞 K := LinearMap.proj 0
  set 𝔞 := E.map π
  set E' := E.comap (consZero r)
  let πE : E →ₗ[𝓞 K] 𝔞 := (π ∘ₗ E.subtype).codRestrict 𝔞 (fun x ↦ Submodule.mem_map_of_mem x.2)
  have hπE : Function.Surjective πE := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp ha
    exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨t, ht⟩ := Module.projective_lifting_property πE LinearMap.id hπE
  have htπ : ∀ a : 𝔞, π (t a) = a := fun a ↦ congrArg Subtype.val (LinearMap.congr_fun ht a)
  rw [detIdeal, Ideal.span_le]
  rintro _ ⟨v, hv, rfl⟩
  let a : Fin (r + 1) → 𝔞 := fun i ↦ ⟨π (v i), Submodule.mem_map_of_mem (hv i)⟩
  let w : Fin (r + 1) → Fin (r + 1) → 𝓞 K := fun i ↦ (t (a i) : Fin (r + 1) → 𝓞 K)
  let e : Fin (r + 1) → Fin (r + 1) → 𝓞 K := fun i ↦ v i - w i
  have hw0 : ∀ i, w i 0 = (a i : 𝓞 K) := fun i ↦ htπ (a i)
  have he0 : ∀ i, e i 0 = 0 := fun i ↦ by
    simp only [e, Pi.sub_apply, hw0]
    exact sub_self _
  have he' : ∀ i, Fin.tail (e i) ∈ E' := by
    intro i
    show consZero r (Fin.tail (e i)) ∈ E
    have : consZero r (Fin.tail (e i)) = e i := by
      conv_rhs => rw [← Fin.cons_self_tail (e i), he0]
      rfl
    rw [this]
    exact E.sub_mem (hv i) (t (a i)).2
  have hvew : v = e + w := by
    funext i
    simp [e]
  have hprop : ∀ i j, (a j : 𝓞 K) • w i = (a i : 𝓞 K) • w j := by
    intro i j
    have h1 : (a j : 𝓞 K) • t (a i) = (a i : 𝓞 K) • t (a j) := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp only [SetLike.val_smul, smul_eq_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val h1
  have hwzero : ∀ j, (a j : 𝓞 K) = 0 → w j = 0 := by
    intro j hj
    have : a j = 0 := Subtype.ext hj
    simp only [w, this, map_zero, ZeroMemClass.coe_zero]
  rw [hvew]
  change (detRowAlternating : (Fin (r + 1) → 𝓞 K) [⋀^Fin (r + 1)]→ₗ[𝓞 K] 𝓞 K) (e + w) ∈ _
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_add_univ]
  refine Ideal.sum_mem _ fun S _ ↦ ?_
  set R := S.piecewise e w
  change (Matrix.of R).det ∈ _
  have hRS : ∀ k ∈ S, R k = e k := fun k hk ↦ Finset.piecewise_eq_of_mem _ _ _ hk
  have hRT : ∀ k ∉ S, R k = w k := fun k hk ↦ Finset.piecewise_eq_of_notMem _ _ _ hk
  set T := Finset.univ \ S
  have hT : ∀ k, k ∈ T ↔ k ∉ S := fun k ↦ by simp [T]
  by_cases h2 : 1 < T.card
  ·
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
    have hi' := (hT i).mp hi
    have hj' := (hT j).mp hj
    suffices (Matrix.of R).det = 0 by rw [this]; exact Ideal.zero_mem _
    by_cases haj : (a j : 𝓞 K) = 0
    · apply det_eq_zero_of_row_eq_zero j
      intro k
      rw [of_apply, hRT j hj', hwzero j haj]
      rfl
    · have key : (a j : 𝓞 K) * (Matrix.of R).det = 0 := by
        have hRi : (Matrix.of R) i = w i := hRT i hi'
        have e1 : (a j : 𝓞 K) * (Matrix.of R).det =
            (updateRow (Matrix.of R) i ((a j : 𝓞 K) • w i)).det := by
          rw [det_updateRow_smul, ← hRi, updateRow_eq_self]
        rw [e1, hprop i j, det_updateRow_smul]
        refine mul_eq_zero_of_right _ (det_zero_of_row_eq hij ?_)
        rw [updateRow_self, updateRow_ne (Ne.symm hij)]
        exact (hRT j hj').symm
      exact (mul_eq_zero.mp key).resolve_left haj
  · rcases Nat.lt_or_ge T.card 1 with h0 | h1
    ·
      have hTe : T = ∅ := Finset.card_eq_zero.mp (by omega)
      suffices (Matrix.of R).det = 0 by rw [this]; exact Ideal.zero_mem _
      apply det_eq_zero_of_column_eq_zero 0
      intro k
      have hk : k ∈ S := by
        by_contra hk
        have := (hT k).mpr hk
        rw [hTe] at this
        exact Finset.notMem_empty k this
      rw [of_apply, hRS k hk, he0]
    ·
      obtain ⟨j, hTj⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
      have hjS : j ∉ S := (hT j).mp (by rw [hTj]; exact Finset.mem_singleton_self j)
      have hkS : ∀ k, k ≠ j → k ∈ S := by
        intro k hk
        by_contra hkS
        have := (hT k).mpr hkS
        rw [hTj, Finset.mem_singleton] at this
        exact hk this
      rw [det_succ_column_zero, Finset.sum_eq_single j]
      · rw [of_apply, hRT j hjS, hw0]
        have hsub : (Matrix.of R).submatrix j.succAbove Fin.succ =
            Matrix.of fun k ↦ Fin.tail (e (j.succAbove k)) := by
          ext k l
          simp only [submatrix_apply, of_apply, Fin.tail]
          rw [hRS _ (hkS _ (Fin.succAbove_ne j k))]
        rw [hsub, mul_assoc]
        exact Ideal.mul_mem_left _ _
          (Ideal.mul_mem_mul (a j).2 (det_mem_detIdeal E' _ fun k ↦ he' _))
      · intro k _ hk
        rw [of_apply, hRS k (hkS k hk), he0, mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h

theorem detIdeal_succ {r : ℕ} (E : Submodule (𝓞 K) (Fin (r + 1) → 𝓞 K)) :
    detIdeal E = E.map (LinearMap.proj 0) * detIdeal (E.comap (consZero r)) :=
  le_antisymm (detIdeal_le_mul E) (mul_le_detIdeal E)

theorem card_quotient_eq_absNorm_detIdeal :
    ∀ (r : ℕ) (E : Submodule (𝓞 K) (Fin r → 𝓞 K)),
      Nat.card ((Fin r → 𝓞 K) ⧸ E) = Ideal.absNorm (detIdeal E)
  | 0, E => by
    have hE : E = ⊤ := Subsingleton.elim _ _
    have hd : detIdeal E = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      have := det_mem_detIdeal E (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
      rwa [det_isEmpty] at this
    rw [hd, Ideal.absNorm_top, hE]
    exact Nat.card_unique
  | r + 1, E => by
    rw [card_quotient_succ, card_quotient_eq_absNorm_detIdeal r, detIdeal_succ, map_mul,
      Ideal.absNorm_apply (E.map (LinearMap.proj 0)), Submodule.cardQuot_apply, mul_comm]

end

end GroundTheory.Heights₂.Heights
