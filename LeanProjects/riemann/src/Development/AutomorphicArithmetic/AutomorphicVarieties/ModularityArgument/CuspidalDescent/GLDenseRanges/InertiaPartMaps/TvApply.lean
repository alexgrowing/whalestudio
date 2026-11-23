import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

noncomputable section

open ValuativeRel GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V.Hi Matrix

namespace UpperTheory.V.Z.Desc.V0

section Rank

variable {R : Type} [CommRing R] {n : ℕ}

private theorem vv_sq (y w : Fin n → R) : vecMulVec y w * vecMulVec y w = (w ⬝ᵥ y) • vecMulVec y w := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => by ring)

private theorem tv_mul (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 + vecMulVec y w) * (1 - c • vecMulVec y w) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, mul_smul_comm, vv_sq, smul_smul, ← add_smul,
    show c + c * (w ⬝ᵥ y) = c * (1 + w ⬝ᵥ y) by ring, h, one_smul]
  abel

private theorem tv_mul' (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) :
    (1 - c • vecMulVec y w) * (1 + vecMulVec y w) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, vv_sq, smul_smul]
  rw [show (c * (w ⬝ᵥ y)) = c * (1 + w ⬝ᵥ y) - c by ring, h, sub_smul, one_smul]
  abel

private def tv (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) : GL (Fin n) R where
  val := 1 + vecMulVec y w
  inv := 1 - c • vecMulVec y w
  val_inv := tv_mul y w c h
  inv_val := tv_mul' y w c h

private theorem tv_apply (y w : Fin n → R) (c : R) (h : c * (1 + w ⬝ᵥ y) = 1) (a b : Fin n) :
    (tv y w c h : Matrix (Fin n) (Fin n) R) a b = (1 : Matrix (Fin n) (Fin n) R) a b + y a * w b := by
  simp [tv, vecMulVec_apply]

end Rank

section Loc

variable {k : Type} [Field k] {n : ℕ}

private theorem chr_of (ψ : AddChar k Circle) (t : Fin n → k) (g : GL (Fin n) k) (y w : Fin n → k) (i c : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) (hc : (c : ℕ) = i + 1) (hwc : w c = 1) :
    chr ψ t g = (ψ (t i * y i) : ℂ) := by
  simp only [chr]
  congr 2
  have hic : i ≠ c := by
    intro h
    have := congrArg Fin.val h
    omega
  rw [Finset.sum_eq_single_of_mem (i, c) (by simp [hc])]
  · rw [hg, Matrix.one_apply_ne hic, hwc]
    ring
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    have hab' : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [hg, Matrix.one_apply_ne hab']
    rcases lt_trichotomy a i with h | h | h
    · have h1 := Fin.lt_def.1 h
      rw [hw b (by rw [Fin.le_def]; omega)]
      ring
    · subst h
      exfalso
      apply hne
      have : b = c := by
        ext
        omega
      rw [this]
    · rw [hy a h]
      ring

private theorem unip_of (g : GL (Fin n) k) (y w : Fin n → k) (i : Fin n)
    (hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b + y a * w b)
    (hy : ∀ a, i < a → y a = 0) (hw : ∀ b, b ≤ i → w b = 0) : g ∈ unipB k (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [hg, Matrix.one_apply_ne hba.ne']
    by_cases ha : i < a
    · rw [hy a ha]
      ring
    · rw [hw b (le_trans hba.le (not_lt.1 ha))]
      ring
  · rw [hg]
    by_cases ha : i < a
    · simp [hy a ha]
    · simp [hw a (not_lt.1 ha)]

private theorem inv_rows (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1) :
    ∀ a, i < a → ∀ j, j ≤ a →
      ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = (1 : Matrix (Fin n) (Fin n) k) a j := by
  have hq : (p : Matrix (Fin n) (Fin n) k) * ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 :=
    Units.mul_inv p
  intro a
  induction h : n - (a : ℕ) using Nat.strong_induction_on generalizing a with
  | _ d ih =>
    intro ha j hj
    have e := congrFun (congrFun hq a) j
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at e
    · rw [(hp a ha).2, one_mul] at e
      exact e
    · intro m _ hma
      rcases lt_or_gt_of_ne hma with hlt | hgt
      · rw [(hp a ha).1 m hlt, zero_mul]
      · have hjm : j < m := lt_of_le_of_lt hj hgt
        have h1 := Fin.lt_def.1 hgt
        have h2 := m.isLt
        rw [ih (n - (m : ℕ)) (by omega) m rfl (lt_trans ha hgt) j hjm.le, Matrix.one_apply_ne (ne_of_gt hjm)]
        ring
    · simp

private theorem conj_eq (p : GL (Fin n) k) (x : Fin n → k) (c : Fin n) :
    (p : Matrix (Fin n) (Fin n) k) * (1 + vecMulVec x (Pi.single c 1)) =
      (1 + vecMulVec ((p : Matrix (Fin n) (Fin n) k) *ᵥ x) (((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c)) *
        (p : Matrix (Fin n) (Fin n) k) := by
  have hrow : ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c ᵥ* (p : Matrix (Fin n) (Fin n) k) = Pi.single c 1 := by
    funext b
    have e := congrFun (congrFun (Units.inv_mul p) c) b
    rw [Matrix.mul_apply] at e
    rw [Matrix.vecMul, dotProduct, e]
    rcases eq_or_ne b c with rfl | hb
    · simp
    · simp [hb, Matrix.one_apply_ne hb.symm]
  rw [Matrix.mul_add, mul_one, Matrix.mul_vecMulVec, Matrix.add_mul, one_mul, Matrix.vecMulVec_mul, hrow]

end Loc

section Val

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem lev_lt (ψ : AddChar k Circle) (hψ : Lev1 ψ) (y : k)
    (h : ∀ s : 𝒪[k], ψ (y * (s : k)) = 1) : valuation k y < 1 := by
  by_contra hy
  have hy1 : 1 ≤ valuation k y := not_lt.1 hy
  have hy0 : y ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hy1
    exact absurd hy1 (not_le.2 zero_lt_one)
  obtain ⟨x, hx, hne⟩ := hψ.2.2
  have hs : valuation k (x / y) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (hx.trans hy1) zero_le'
  apply hne
  have := h ⟨x / y, hs⟩
  have hyx : y * ((⟨x / y, hs⟩ : 𝒪[k]) : k) = x := by
    show y * (x / y) = x
    field_simp
  rwa [hyx] at this

private theorem rowStep {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v)
    (p : GL (Fin n) k) (i c : Fin n) (hc : (c : ℕ) = i + 1)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hW : l (τ p v) ≠ 0) (j : Fin n) (hj : j ≤ i) (s : 𝒪[k]) :
    ψ (t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k))) = ψ (t i * (Pi.single j (s : k) : Fin n → k) i) := by
  have hci : i < c := by rw [Fin.lt_def, hc]; omega
  have hjc : j ≠ c := fun h => absurd (lt_of_le_of_lt hj hci) (by rw [h]; exact lt_irrefl c)
  set x : Fin n → k := Pi.single j (s : k) with hx
  set e : Fin n → k := Pi.single c 1 with he
  have hdot : e ⬝ᵥ x = 0 := by
    simp only [dotProduct, he, hx, Pi.single_apply]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) hjc
    all_goals simp
  have h0 : (1 : k) * (1 + e ⬝ᵥ x) = 1 := by rw [hdot]; ring
  have hy : ∀ a, i < a → x a = 0 := fun a ha => by
    rw [hx, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hj ha) (by rw [h]; exact lt_irrefl j)
  have hw : ∀ b, b ≤ i → e b = 0 := fun b hb => by
    rw [he, Pi.single_eq_of_ne]
    exact fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl c)
  have hu := unip_of (tv x e 1 h0) x e i (tv_apply x e 1 h0) hy hw
  have hcu := chr_of ψ t (tv x e 1 h0) x e i c (tv_apply x e 1 h0) hy hw hc (by rw [he, Pi.single_eq_same])
  have hK : tv x e 1 h0 ∈ KO k (Fin n) := by
    have h00 : (1 : 𝒪[k]) * (1 + (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s)) = 1 := by
      have hz : (Pi.single c 1 : Fin n → 𝒪[k]) ⬝ᵥ (Pi.single j s) = 0 := by
        simp only [dotProduct, Pi.single_apply]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        split_ifs with h1 h2
        · exact absurd (h2.symm.trans h1) hjc
        all_goals simp
      rw [hz]; ring
    refine ⟨tv (Pi.single j s) (Pi.single c 1) 1 h00, ?_⟩
    apply Units.ext
    ext a b
    simp [tv, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.single_apply, he, hx]
    split_ifs <;> first | rfl | simp
  set y : Fin n → k := (p : Matrix (Fin n) (Fin n) k) *ᵥ x with hyd
  set w : Fin n → k := ((p⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c with hwd
  have hyv : ∀ a, y a = (p : Matrix (Fin n) (Fin n) k) a j * (s : k) := by
    intro a
    simp [hyd, hx, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have hinv := inv_rows p i hp
  have hy' : ∀ a, i < a → y a = 0 := fun a ha => by
    rw [hyv, (hp a ha).1 j (lt_of_le_of_lt hj ha), zero_mul]
  have hw' : ∀ b, b ≤ i → w b = 0 := fun b hb => by
    rw [hwd, hinv c hci b (le_of_lt (lt_of_le_of_lt hb hci))]
    exact Matrix.one_apply_ne (fun h => absurd (lt_of_le_of_lt hb hci) (by rw [h]; exact lt_irrefl b))
  have hwc : w c = 1 := by rw [hwd, hinv c hci c le_rfl, Matrix.one_apply_eq]
  have hdot' : w ⬝ᵥ y = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rcases le_or_gt b i with hb | hb
    · rw [hw' b hb, zero_mul]
    · rw [hy' b hb, mul_zero]
  have h1 : (1 : k) * (1 + w ⬝ᵥ y) = 1 := by rw [hdot']; ring
  have hu' := unip_of (tv y w 1 h1) y w i (tv_apply y w 1 h1) hy' hw'
  have hcu' := chr_of ψ t (tv y w 1 h1) y w i c (tv_apply y w 1 h1) hy' hw' hc hwc
  have hconj : p * tv x e 1 h0 = tv y w 1 h1 * p := by
    apply Units.ext
    exact conj_eq p x c
  have eq1 : l (τ (p * tv x e 1 h0) v) = chr ψ t (tv x e 1 h0) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hv _ hu hK, map_smul, map_smul, smul_eq_mul]
  have eq2 : l (τ (tv y w 1 h1 * p) v) = chr ψ t (tv y w 1 h1) * l (τ p v) := by
    rw [map_mul, Module.End.mul_apply, hl _ hu' (τ p v)]
  rw [hconj, eq2] at eq1
  have eq3 := mul_right_cancel₀ hW eq1
  rw [hcu, hcu'] at eq3
  have eq4 : ψ (t i * y i) = ψ (t i * x i) := Subtype.ext (by exact_mod_cast eq3)
  rw [hyv] at eq4
  exact eq4

set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_mem_Kc_rows_unitriangular (p : GL (Fin n) k) (i : Fin n)
    (hp : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧ (p : Matrix (Fin n) (Fin n) k) a a = 1)
    (hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1) :
    ∃ κ ∈ Kc k n 1, ∀ a, i ≤ a → (∀ j, j < a → ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = 0) ∧
      ((p * κ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a a = 1 := by
  classical
  set P := (p : Matrix (Fin n) (Fin n) k) with hP
  let d : Fin n → k := fun j => if j ≤ i then P i j - (1 : Matrix (Fin n) (Fin n) k) i j else 0
  have hdv : ∀ j, valuation k (d j) < 1 := by
    intro j
    by_cases hj : j ≤ i
    · simp only [d, if_pos hj]
      exact hd j hj
    · simp only [d, if_neg hj, map_zero]
      exact zero_lt_one
  have hint : ∀ j, d j ∈ 𝒪[k] := fun j => (Valuation.mem_integer_iff _ _).2 (hdv j).le
  have hI := Valuation.integer.integers (valuation k)
  have hmax : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ 𝓂[k] := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact hx.ne
  let d₀ : Fin n → 𝒪[k] := fun j => ⟨d j, hint j⟩
  let y₀ : Fin n → 𝒪[k] := Pi.single i 1
  have hdot : d₀ ⬝ᵥ y₀ = d₀ i := by simp [y₀]
  have hu : IsUnit (1 + d₀ ⬝ᵥ y₀) := by
    rw [hdot, hI.isUnit_iff_valuation_eq_one, map_add, map_one]
    exact Valuation.map_one_add_of_lt _ (hdv i)
  obtain ⟨u, hu'⟩ := hu
  have hc : ((u⁻¹ : (𝒪[k])ˣ) : 𝒪[k]) * (1 + d₀ ⬝ᵥ y₀) = 1 := by rw [← hu']; exact u.inv_mul
  let M₀ : GL (Fin n) 𝒪[k] := tv y₀ d₀ _ hc
  let M : GL (Fin n) k := GeneralLinearGroup.map (algebraMap 𝒪[k] k) M₀
  have hM : ∀ a b, (M : Matrix (Fin n) (Fin n) k) a b =
      (1 : Matrix (Fin n) (Fin n) k) a b + (Pi.single i (1 : k) : Fin n → k) a * d b := by
    intro a b
    simp only [M, GeneralLinearGroup.map_apply, M₀, tv_apply, map_add, map_mul]
    congr 1
    · simp [Matrix.one_apply]
    · congr 1
      simp [y₀, Pi.single_apply]
  refine ⟨M⁻¹, ?_, ?_⟩
  · apply Subgroup.inv_mem
    refine ⟨M₀, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply GeneralLinearGroup.ext
    intro a b
    rw [GeneralLinearGroup.map_apply, tv_apply, map_add]
    have hz : Ideal.Quotient.mk (𝓂[k] ^ 1) (y₀ a * d₀ b) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mul_mem_left _ _ (hmax _ (hdv b))
    rw [hz, add_zero]
    simp [Matrix.one_apply]
  · set Q := ((p * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hQ
    have hq : ∀ a j, Q a j + Q a i * d j = P a j := by
      intro a j
      have h1 : ((p * M⁻¹ * M : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a j = P a j := by
        rw [inv_mul_cancel_right]
      rw [Units.val_mul, Matrix.mul_apply] at h1
      simp_rw [hM] at h1
      rw [← h1]
      simp [mul_add, Finset.sum_add_distrib, Matrix.one_apply, Pi.single_apply, Q]
    have hdi : 1 + d i = P i i := by simp [d]
    have hPii : P i i ≠ 0 := by
      intro h0
      have := hd i le_rfl
      rw [h0, zero_sub, Valuation.map_neg, Matrix.one_apply_eq, map_one] at this
      exact lt_irrefl _ this
    have hQi : ∀ a, Q a i * P i i = P a i := by
      intro a
      rw [← hdi, ← hq a i]
      ring
    intro a ha
    rcases ha.eq_or_lt with rfl | hlt
    · have hii : Q i i = 1 := by
        have := hQi i
        exact (mul_eq_right₀ hPii).1 this
      refine ⟨fun j hj => ?_, hii⟩
      have h2 := hq i j
      rw [hii, one_mul] at h2
      have hdj : d j = P i j - (1 : Matrix (Fin n) (Fin n) k) i j := by simp [d, hj.le]
      rw [hdj, Matrix.one_apply_ne hj.ne'] at h2
      linear_combination h2
    · obtain ⟨hz, h1⟩ := hp a hlt
      have hai : Q a i = 0 := by
        have := hQi a
        rw [hz i hlt] at this
        exact (mul_eq_zero.1 this).resolve_right hPii
      have hrow : ∀ j, Q a j = P a j := by
        intro j
        have := hq a j
        rw [hai, zero_mul, add_zero] at this
        exact this
      exact ⟨fun j hj => by rw [hrow]; exact hz j hj, by rw [hrow]; exact h1⟩

private theorem descent {W : Type} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin n) k) W)
    (ψ : AddChar k Circle) (t : Fin n → k) (l : W →ₗ[ℂ] ℂ) (hψ : Lev1 ψ) (ht : ∀ i, valuation k (t i) = 1)
    (hl : ∀ u ∈ unipB k (Fin n), ∀ v, l (τ u v) = chr ψ t u * l v) (v : W) (hlv : l v = 0)
    (hfix : ∀ κ ∈ Kc k n 1, τ κ v = v)
    (hv : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v) (r : ℕ) :
    r ≤ n - 1 → ∀ p : GL (Fin n) k,
      (∀ a : Fin n, r ≤ (a : ℕ) → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1) → l (τ p v) = 0 := by
  induction r with
  | zero =>
    intro _ p hp
    have hu : p ∈ unipB k (Fin n) :=
      (mem_unipB k).2 ⟨fun a j h => (hp a (Nat.zero_le _)).1 j h, fun a => (hp a (Nat.zero_le _)).2⟩
    rw [hl p hu v, hlv, mul_zero]
  | succ r ih =>
    intro hr p hp
    by_contra hW
    have hrn : r < n := by omega
    have hcn : r + 1 < n := by omega
    let i : Fin n := ⟨r, hrn⟩
    let c : Fin n := ⟨r + 1, hcn⟩
    have hpi : ∀ a, i < a → (∀ j, j < a → (p : Matrix (Fin n) (Fin n) k) a j = 0) ∧
        (p : Matrix (Fin n) (Fin n) k) a a = 1 := fun a ha => hp a (Fin.lt_def.1 ha)
    have hd : ∀ j, j ≤ i → valuation k ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
      intro j hj
      have hs := rowStep τ ψ t l hl v hv p i c rfl hpi hW j hj
      have h2 : ∀ s : 𝒪[k], ψ ((t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)) * (s : k)) = 1 := by
        intro s
        have e : t i * ((p : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) * (s : k) =
            t i * ((p : Matrix (Fin n) (Fin n) k) i j * (s : k)) - t i * (Pi.single j (s : k) : Fin n → k) i := by
          rw [Pi.single_apply]
          rcases eq_or_ne i j with h | h
          · subst h
            simp only [Matrix.one_apply_eq, if_true]
            ring
          · simp only [h, Matrix.one_apply_ne h, if_false]
            ring
        rw [e, AddChar.map_sub_eq_div, hs s, div_self']
      have h3 := lev_lt ψ hψ _ h2
      rw [map_mul, ht i, one_mul] at h3
      exact h3
    obtain ⟨κ, hκ, hpk⟩ := exists_mem_Kc_rows_unitriangular p i hpi hd
    apply hW
    have e : τ (p * κ) v = τ p v := by
      rw [map_mul, Module.End.mul_apply, hfix κ hκ]
    rw [← e]
    exact ih (by omega) (p * κ) (fun a ha => hpk a (Fin.le_def.2 ha))

end Val

theorem isoLe : IsoLe := by
  intro k _ _ _ _ n W _ _ τ ψ t l hψ ht hK v hv hlv
  obtain ⟨hl, hsep⟩ := hK
  have hfix : ∀ κ ∈ Kc k n 1, τ κ v = v := (Submodule.mem_inf.1 hv).1
  have heig : ∀ u, u ∈ unipB k (Fin n) → u ∈ KO k (Fin n) → τ u v = chr ψ t u • v := by
    intro u h1 h2
    have h3 := (Submodule.mem_iInf _).1 (Submodule.mem_iInf _ |>.1 (Submodule.mem_inf.1 hv).2 u) ⟨h1, h2⟩
    exact Module.End.mem_eigenspace_iff.1 h3
  refine hsep v fun p hp => descent τ ψ t l hψ ht hl v hlv hfix heig (n - 1) le_rfl p fun a ha => ?_
  have hn : (a : ℕ) + 1 = n := by
    have := a.2
    omega
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hp a j hn, one_apply_ne (ne_of_gt hj)]
  · rw [hp a a hn, one_apply_eq]

end UpperTheory.V.Z.Desc.V0
