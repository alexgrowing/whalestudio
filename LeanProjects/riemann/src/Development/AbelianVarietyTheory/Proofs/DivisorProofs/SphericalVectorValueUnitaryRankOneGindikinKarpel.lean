import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

def transv {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) : GL (Fin n) L :=
  ⟨1 + Matrix.single i j c, 1 - Matrix.single i j c,
    by rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp,
    by rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]; simp⟩

theorem transv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    ((transv i j hij c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 + Matrix.single i j c := rfl

theorem transv_inv_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : L) :
    (((transv i j hij c)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 - Matrix.single i j c := rfl

theorem transv_mem_GU (σ : L →+* L) {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hr : i.rev = j) (c : L)
    (hc : σ c = -c) : transv i j hij c ∈ GU σ n := by
  rw [GlobalTheory.LGrp.mem_GU_iff]
  intro p r
  have e1 : ∀ x : Fin n, i = x.rev ↔ x = j := fun x => by rw [← hr]; exact ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  have e2 : ∀ x : Fin n, j = x.rev ↔ x = i := fun x => by
    rw [← hr]; exact ⟨fun h => Fin.rev_injective (by rw [← h]), fun h => by rw [h]⟩
  rw [transv_inv_val, transv_val]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.rev_inj, e1, e2]
  by_cases h : i = p ∧ j = r
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, hij.symm, hc, sub_eq_add_neg]
  · have h' : ¬ (r = j ∧ p = i) := fun h' => h ⟨h'.2.symm, h'.1.symm⟩
    rw [if_neg h, if_neg h']
    by_cases hpr : p = r
    · subst hpr; simp
    · simp [hpr, Ne.symm hpr]
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_mul_apply {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((Y : Matrix (Fin n) (Fin n) L) * M) i j = (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) * M (t⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (t⁻¹ i)]
  · intro l _ hl
    rw [hY i l (fun h => hl (by rw [h]; simp)), zero_mul]
  · simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL {x : L} (hx : Valued.v x ≤ 1) : x ∈ intL L := hx

theorem transv_mem_GLint {n : ℕ} (i j : Fin n) (hij : i ≠ j) {c : L} (hc : Valued.v c ≤ 1) :
    transv i j hij c ∈ GLint (Fin n) (intL L) := by
  have hc' : c ∈ intL L := mem_intL hc
  refine P.cartan_mem_of_entries (intL L) _ (fun p r => ?_) (fun p r => ?_)
  · rw [transv_val, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'
  · rw [transv_inv_val, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply]
    refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hc'

theorem ordL_neg (x : L) : ordL (-x) = ordL x := by
  simp only [ordL, Valuation.map_neg]

theorem ordL_one' : ordL (1 : L) = 0 :=
  P.fIwasawa_ordL_unit 1 1 (by rw [map_one]) (by rw [map_one]) (mul_one 1)

theorem ordL_inv {x : L} (hx : x ≠ 0) : ordL x⁻¹ = -ordL x := by
  have h := P.fIwasawa_ordL_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordL_one'] at h
  omega

theorem ordL_monomial_entry {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (hYK : Y ∈ GLint (Fin n) (intL L)) (i : Fin n) :
    ordL ((Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i)) = 0 := by
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq] at h
  exact P.fIwasawa_ordL_unit _ _ (P.cartan_entries_of_mem _ Y hYK _ _)
    (P.cartan_entries_of_mem _ _ (inv_mem hYK) _ _) (by rw [mul_comm]; exact h)

theorem isBorelU_one (σ : L →+* L) (n : ℕ) : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply, ne_of_gt h]

theorem chiDeltaU_one (σ : L →+* L) (n m q : ℕ) (α : Fin m → ℂ) : chiDeltaU q α (1 : GU σ n) = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one']
  · rfl

end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne
variable {L : Type} [Field L]

theorem monomial_entry_ne_zero {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (i : Fin n) : (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq, h0, zero_mul] at h
  exact zero_ne_one h
end GlobalTheory.GKUnitaryRankOne

namespace GlobalTheory.GKUnitaryRankOne

theorem value_rankOne : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (u : GU σ n), (∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j) →
    φ (y⁻¹ * u) = if Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 then 1
      else α k ^ (-ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) *
        (q : ℂ) ^ (ordL (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)) := by
  intro L _ _ ϖ σ q _ n k hk hn α φ hφ hφ1 y hy hyw u hu
  have hn2 : n = 2 * k.val + 2 := by obtain ⟨r, hr⟩ := hn; omega
  set a : Fin n := lo k with ha
  set a' : Fin n := (lo k).rev with ha'
  have hav : a.val = k.val := rfl
  have ha'v : a'.val = k.val + 1 := by rw [ha', Fin.val_rev]; simp; omega
  have haa' : a ≠ a' := fun h => by have := congrArg Fin.val h; omega
  have hra : a'.rev = a := by rw [ha', Fin.rev_rev]
  set b := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hb
  have hU : (u : GL (Fin n) L) = transv a a' haa' b := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [transv_val]
    by_cases h : i = a ∧ j = a'
    · obtain ⟨rfl, rfl⟩ := h
      simp [Matrix.single_apply, haa', hb]
    · rw [hu i j h, Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  have hσb : σ b = -b := by
    have h := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2 a a'
    rw [hra, ← ha', ← hb, hU, transv_inv_val] at h
    simpa [Matrix.single_apply, haa'] using h.symm
  by_cases hv : Valued.v b ≤ 1
  · rw [if_pos hv]
    have huK : u ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      show (u : GL (Fin n) L) ∈ GLint (Fin n) (intL L)
      rw [hU]; exact transv_mem_GLint a a' haa' hv
    have h := hφ 1 1 (y⁻¹ * u) (isBorelU_one σ n) (mul_mem (inv_mem hy) huK)
    rw [one_mul, one_mul] at h
    rw [h, chiDeltaU_one, hφ1, one_mul]
  · rw [if_neg hv]
    push_neg at hv
    have hb0 : b ≠ 0 := fun h => by rw [h, map_zero] at hv; exact not_lt_of_ge zero_le' hv
    set c := b⁻¹ with hc
    have hvc : Valued.v c ≤ 1 := ((Valuation.one_lt_val_iff _ hb0).1 hv).le
    have hσc : σ c = -c := by rw [hc, map_inv₀, hσb, inv_neg]
    have hbc : b * c = 1 := mul_inv_cancel₀ hb0
    let κ : GU σ n := ⟨transv a' a haa'.symm c, transv_mem_GU σ a' a haa'.symm hra c hσc⟩
    have hκ : κ ∈ KU σ n := by
      rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
      exact transv_mem_GLint a' a haa'.symm hvc
    set Pb : GU σ n := y⁻¹ * u * κ⁻¹ with hPb
    have e : Pb * 1 * κ = y⁻¹ * u := by rw [hPb]; group
    have hyK : (y : GL (Fin n) L) ∈ GLint (Fin n) (intL L) := hy.2
    have hyiw := IsWeylRep.inv hyw
    have hs : simpleU k = Equiv.swap a a' := by unfold simpleU; rw [if_neg hk]
    set M : Matrix (Fin n) (Fin n) L := (1 + Matrix.single a a' b) * (1 - Matrix.single a' a c) with hMdef
    have hM : ∀ l j, M l j = (1 : Matrix (Fin n) (Fin n) L) l j + (if a = l ∧ a' = j then b else 0)
        - (if a' = l ∧ a = j then c else 0) - (if a = l ∧ a = j then 1 else 0) := by
      intro l j
      rw [hMdef, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.single_mul_single_same, hbc]
      simp [Matrix.single_apply]; ring
    have hP : ∀ i j, (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
          M (Equiv.swap a a' i) j := by
      intro i j
      have : (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
          (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M := by
        rw [hPb, hMdef, ← transv_val a a' haa' b, ← transv_inv_val a' a haa'.symm, ← hU]
        simp [Matrix.mul_assoc, κ]
      rw [this, monomial_mul_apply hyiw, inv_inv, hs]
    have hunit : ∀ i, ordL ((((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i
        (Equiv.swap a a' i)) = 0 := fun i => by
      have := ordL_monomial_entry hyiw (inv_mem hyK) i
      rwa [inv_inv, hs] at this
    have hB : IsBorelU Pb := by
      intro i j hji
      have hj : j.val < i.val := hji
      rw [hP, hM]
      apply mul_eq_zero_of_right
      simp only [Matrix.one_apply, Equiv.swap_apply_def, Fin.ext_iff]
      split_ifs <;> first | omega | ring
    rw [← e, hφ Pb 1 κ hB hκ, hφ1, mul_one]
    have hdiag : ∀ i : Fin n, i ≠ a → i ≠ a' →
        ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 0 := by
      intro i h1 h2
      rw [hP, Equiv.swap_apply_of_ne_of_ne h1 h2, hM]
      simp only [Matrix.one_apply_eq, if_neg (fun h : a = i ∧ a' = i => h1 h.1.symm),
        if_neg (fun h : a' = i ∧ a = i => h2 h.1.symm), if_neg (fun h : a = i ∧ a = i => h1 h.1.symm)]
      have := hunit i
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at this
      simpa using this
    have hdiag_a : ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = -ordL b := by
      rw [hP, Equiv.swap_apply_left, hM]
      simp only [Matrix.one_apply, if_neg haa'.symm, if_neg (fun h : a = a' ∧ a' = a => haa' h.1),
        if_pos (⟨rfl, rfl⟩ : a' = a' ∧ a = a), if_neg (fun h : a = a' ∧ a = a => haa' h.1)]
      have hy0 : (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' ≠ 0 := by
        have := monomial_entry_ne_zero hyiw a
        rwa [inv_inv, hs, Equiv.swap_apply_left] at this
      have hc0 : c ≠ 0 := inv_ne_zero hb0
      have e2 : ((0 : L) + 0 - if True ∧ True then c else 0) - (if a = a' ∧ True then 1 else 0) = -c := by
        rw [if_pos ⟨trivial, trivial⟩, if_neg (fun h => haa' h.1)]; ring
      rw [e2, P.fIwasawa_ordL_mul _ _ hy0 (neg_ne_zero.2 hc0), ordL_neg, hc, ordL_inv hb0]
      have := hunit a
      rw [Equiv.swap_apply_left] at this
      rw [this, zero_add]
    unfold chiDeltaU
    rw [Finset.prod_eq_single k]
    · rw [dif_pos (by omega)]
      show α k ^ ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) *
          (q : ℂ) ^ (-(ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) *
            ((n : ℤ) - 1 - 2 * (k.val : ℤ))) = _
      have e3 : (n : ℤ) - 1 - 2 * (k.val : ℤ) = 1 := by omega
      rw [hdiag_a, e3, neg_neg, mul_one]
    · intro i _ hik
      have hi : i.val < k.val := by
        have : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
      rw [dif_pos (by omega), hdiag _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
        (fun h => by have := congrArg Fin.val h; simp at this; omega)]
      simp
    · simp

end GlobalTheory.GKUnitaryRankOne
