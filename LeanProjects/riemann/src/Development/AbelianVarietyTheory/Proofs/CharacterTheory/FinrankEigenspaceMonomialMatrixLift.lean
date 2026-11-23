import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.MonoEigen

def orbProd {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (m : ℕ) (j : Fin n) : K :=
  ∏ i ∈ Finset.range m, a ((σ ^ i) j)

def GoodRep {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (j : Fin n) : Prop :=
  (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1

section
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)

lemma orbProd_succ (m : ℕ) (j : Fin n) :
    orbProd σ a (m + 1) j = orbProd σ a m j * a ((σ ^ m) j) := by
  simp [orbProd, Finset.prod_range_succ]

lemma orbProd_add (d m : ℕ) (j : Fin n) :
    orbProd σ a (d + m) j = orbProd σ a d j * orbProd σ a m ((σ ^ d) j) := by
  unfold orbProd
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]

lemma orbProd_eq {j : Fin n} (hj : ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1)
    (m m' : ℕ) (h : (σ ^ m) j = (σ ^ m') j) : orbProd σ a m j = orbProd σ a m' j := by
  wlog hle : m ≤ m' generalizing m m'
  · exact (this m' m h.symm (le_of_not_ge hle)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
  have hd : (σ ^ d) j = j := by
    rw [add_comm, pow_add, Equiv.Perm.mul_apply] at h
    exact ((σ ^ m).injective h).symm
  rw [orbProd_add, hj d hd, hd, one_mul]

lemma apply_pow {v : Fin n → K} (hv : ∀ j, v (σ j) = a j * v j) (m : ℕ) (j : Fin n) :
    v ((σ ^ m) j) = orbProd σ a m j * v j := by
  induction m with
  | zero => simp [orbProd]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hv, ih, orbProd_succ]; ring

lemma exists_back (m : ℕ) (j : Fin n) : ∃ m' : ℕ, (σ ^ m') ((σ ^ m) j) = j := by
  have h : σ.SameCycle ((σ ^ m) j) j := by
    rw [Equiv.Perm.sameCycle_pow_left]
  exact h.exists_nat_pow_eq

lemma exists_rep (i : Fin n) : ∃ j : Fin n, (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∃ m : ℕ, (σ ^ m) j = i := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => ∃ m : ℕ, (σ ^ m) i = j) id ⟨i, by simpa using ⟨0, by simp⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hj hmin
  obtain ⟨m, rfl⟩ := hj
  refine ⟨_, fun k => hmin _ ⟨k + m, by rw [pow_add, Equiv.Perm.mul_apply]⟩, exists_back σ m i⟩

lemma exists_vec {s : Fin n} (hs : GoodRep σ a s) :
    ∃ v : Fin n → K, (∀ j, v (σ j) = a j * v j) ∧ v s = 1 ∧
      ∀ t, GoodRep σ a t → t ≠ s → v t = 0 := by
  classical
  let v : Fin n → K := fun i => if h : ∃ m : ℕ, (σ ^ m) s = i then orbProd σ a h.choose s else 0
  have hv : ∀ m : ℕ, v ((σ ^ m) s) = orbProd σ a m s := by
    intro m
    have h : ∃ m' : ℕ, (σ ^ m') s = (σ ^ m) s := ⟨m, rfl⟩
    simp only [v, dif_pos h]
    exact orbProd_eq σ a hs.2 _ _ h.choose_spec
  refine ⟨v, fun j => ?_, by simpa [orbProd] using hv 0, fun t ht hts => ?_⟩
  · by_cases h : ∃ m : ℕ, (σ ^ m) s = j
    · obtain ⟨m, rfl⟩ := h
      rw [← Equiv.Perm.mul_apply, ← pow_succ', hv, hv, orbProd_succ, mul_comm]
    · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = σ j := by
        rintro ⟨m, hm⟩
        obtain ⟨m', hm'⟩ := exists_back σ 1 j
        refine h ⟨m' + m, ?_⟩
        rw [pow_add, Equiv.Perm.mul_apply, hm]
        simpa using hm'
      simp only [v, dif_neg h, dif_neg h', mul_zero]
  · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = t := by
      rintro ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := exists_back σ m s
      have h1 := ht.1 m'
      rw [hm'] at h1
      exact hts (le_antisymm h1 (hs.1 m))
    simp only [v, dif_neg h']

theorem finrank_eq_card (E : Submodule K (Fin n → K))
    (hE : ∀ v, v ∈ E ↔ ∀ j, v (σ j) = a j * v j) :
    Module.finrank K E = Nat.card {j // GoodRep σ a j} := by
  classical
  let f : E →ₗ[K] ({j // GoodRep σ a j} → K) :=
    (LinearMap.funLeft K K Subtype.val).comp E.subtype
  have hf : ∀ (v : E) s, f v s = v.1 s.1 := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v h0
    have hv := (hE _).1 v.2
    ext i
    obtain ⟨j, hj, m, rfl⟩ := exists_rep σ i
    have : v.1 j = 0 := by
      by_cases hg : GoodRep σ a j
      · have := congrFun h0 ⟨j, hg⟩
        simpa [hf] using this
      · have : ¬ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1 := fun h => hg ⟨hj, h⟩
        push_neg at this
        obtain ⟨r, hr, hne⟩ := this
        have h2 := apply_pow σ a hv r j
        rw [hr] at h2
        by_contra h3
        exact hne (mul_right_cancel₀ h3 (by rw [← h2, one_mul]))
    simp [apply_pow σ a hv, this]
  have hsurj : Function.Surjective f := by
    intro w
    choose u hu h1 h0 using fun s : {j // GoodRep σ a j} => exists_vec σ a s.2
    refine ⟨∑ s, w s • ⟨u s, (hE _).2 (hu s)⟩, ?_⟩
    ext t
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [hf, h1]
    · intro s _ hst
      simp [hf, h0 s t.1 t.2 (fun h => hst (Subtype.ext h).symm)]
    · simp
  rw [(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

lemma mem_eigenspace_iff (c : Fin n → K) (μ : K) (hμ : μ ≠ 0) (v : Fin n → K) :
    v ∈ Module.End.eigenspace
      (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ ↔
      ∀ j, v (σ j) = (c j * μ⁻¹) * v j := by
  rw [Module.End.mem_eigenspace_iff, funext_iff, ← σ.forall_congr_right]
  refine forall_congr' fun j => ?_
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    EmbeddingLike.apply_eq_iff_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]; field_simp

end

theorem finrank_eigenspace_monomial_lift :
    ∀ (k : Type) [Field k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → ∀ μ : k, μ ≠ 0 → Module.finrank k (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) = Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  intro k _ θ hθ n σ c hc μ hμ
  have hmul : θ μ * θ μ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
  have hθμ : θ μ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (θ μ)⁻¹ = θ μ⁻¹ := inv_eq_of_mul_eq_one_right hmul
  rw [finrank_eq_card σ (fun j => c j * μ⁻¹) _ (mem_eigenspace_iff σ c μ hμ),
    finrank_eq_card σ (fun j => θ (c j) * (θ μ)⁻¹) _
      (mem_eigenspace_iff σ (fun j => θ (c j)) (θ μ) hθμ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  refine and_congr_right fun _ => forall_congr' fun m => imp_congr_right fun _ => ?_
  have h1 : orbProd σ (fun j => θ (c j) * (θ μ)⁻¹) m j
      = θ (orbProd σ (fun j => c j * μ⁻¹) m j) := by
    simp only [orbProd, map_prod, map_mul, hinv]
  have h2 : orbProd σ (fun j => c j * μ⁻¹) m j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc _) (inv_ne_zero hμ)
  rw [h1]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    exact hθ _ _ h2 one_ne_zero (by rw [h, map_one])

end GlobalTheory.MonoEigen
