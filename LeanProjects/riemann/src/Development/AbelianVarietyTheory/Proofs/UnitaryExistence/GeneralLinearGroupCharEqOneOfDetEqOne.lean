import Mathlib

namespace GlobalTheory

open Matrix

section DetOneChar

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]

theorem ddChar_crt [Finite R] (f : MaximalSpectrum R → R) :
    ∃ t : R, ∀ m : MaximalSpectrum R, t - f m ∈ m.asIdeal := by
  have : Finite (MaximalSpectrum R) :=
    Finite.of_injective (fun m : MaximalSpectrum R => (m.asIdeal : Set R))
      (fun a b hab => MaximalSpectrum.ext (SetLike.coe_injective hab))
  refine Ideal.exists_forall_sub_mem_ideal (I := fun m : MaximalSpectrum R => m.asIdeal) ?_ f
  intro a b hab
  have ha := a.isMaximal
  have hb := b.isMaximal
  exact Ideal.isCoprime_of_isMaximal (fun h => hab (MaximalSpectrum.ext h))

theorem ddChar_isUnit {x : R} (h : ∀ m : MaximalSpectrum R, x ∉ m.asIdeal) : IsUnit x := by
  by_contra hx
  obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h ⟨M, hM⟩ hxM

theorem ddChar_exists_unit [Finite R]
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 4 ≤ Nat.card (R ⧸ 𝔪)) :
    ∃ u : Rˣ, IsUnit ((u : R) - 1) := by
  have key : ∀ m : MaximalSpectrum R, ∃ c : R, c ∉ m.asIdeal ∧ c - 1 ∉ m.asIdeal := by
    intro m
    have h4 := h m.asIdeal m.isMaximal
    by_contra hno
    push Not at hno
    have hsurj : Function.Surjective
        (fun b : Bool => if b then (1 : R ⧸ m.asIdeal) else 0) := by
      intro y
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      by_cases hc : c ∈ m.asIdeal
      · exact ⟨false, by simp [Ideal.Quotient.eq_zero_iff_mem.2 hc]⟩
      · refine ⟨true, ?_⟩
        have h1 := hno c hc
        simp only [if_true]
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk m.asIdeal), ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem]
        exact h1
    have := Nat.card_le_card_of_surjective _ hsurj
    simp at this
    omega
  choose f hf using key
  obtain ⟨t, ht⟩ := ddChar_crt f
  have hnot : ∀ (c : R) (m : MaximalSpectrum R), c - f m ∈ m.asIdeal → f m ∉ m.asIdeal → c ∉ m.asIdeal :=
    fun c m h1 h2 h3 => h2 (by simpa using m.asIdeal.sub_mem h3 h1)
  have htu : IsUnit t := ddChar_isUnit fun m => hnot t m (ht m) (hf m).1
  refine ⟨htu.unit, ddChar_isUnit fun m hm => (hf m).2 ?_⟩
  have : (t - 1) - (t - f m) = f m - 1 := by ring
  rw [← this]
  exact m.asIdeal.sub_mem (by simpa using hm) (ht m)

theorem ddChar_stable [Finite R] {v w b : R} (h : w * v + b = 1) :
    ∃ t : R, IsUnit (v + t * b) := by
  have key : ∀ m : MaximalSpectrum R, ∃ c : R, v + c * b ∉ m.asIdeal := by
    intro m
    by_cases hb : b ∈ m.asIdeal
    · refine ⟨0, fun hv => m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have : w * v + b ∈ m.asIdeal := m.asIdeal.add_mem (m.asIdeal.mul_mem_left _ (by simpa using hv)) hb
      rwa [h] at this
    · obtain ⟨y, i, hi, hyi⟩ := m.isMaximal.exists_inv hb
      refine ⟨(1 - v) * y, fun hmem => m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have e : (1 : R) = (v + (1 - v) * y * b) + (1 - v) * i := by linear_combination (v - 1) * hyi
      rw [e]
      exact m.asIdeal.add_mem hmem (m.asIdeal.mul_mem_left _ hi)
  choose f hf using key
  obtain ⟨t, ht⟩ := ddChar_crt f
  refine ⟨t, ddChar_isUnit fun m hm => hf m ?_⟩
  have : v + f m * b = (v + t * b) - (t - f m) * b := by ring
  rw [this]
  exact m.asIdeal.sub_mem hm (m.asIdeal.mul_mem_right _ (ht m))

def ddCharUnip (N : Matrix n n R) (hN : N * N = 0) : GL n R :=
  ⟨1 + N, 1 - N, by simp [add_mul, mul_sub, hN], by simp [sub_mul, mul_add, hN]⟩

theorem ddChar_unip_eq_one (ψ : GL n R →* A) (N : Matrix n n R) (hN : N * N = 0) (d : GL n R)
    (p q : R) (hp : (d : Matrix n n R) * N = p • N) (hq : N * (d : Matrix n n R) = q • N)
    (hpq : IsUnit (q - p)) : ψ (ddCharUnip N hN) = 1 := by
  obtain ⟨c, hc⟩ := hpq
  set M : Matrix n n R := ((c⁻¹ : Rˣ) : R) • N with hM
  have hM2 : M * M = 0 := by
    rw [hM, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, smul_zero]
  have hMM : ∀ a : R, (a • M) * (a • M) = 0 := fun a => by
    rw [Matrix.smul_mul, Matrix.mul_smul, hM2, smul_zero, smul_zero]
  have hdM : (d : Matrix n n R) * M = p • M := by rw [hM, Matrix.mul_smul, hp, smul_comm]
  have hMd : M * (d : Matrix n n R) = q • M := by rw [hM, Matrix.smul_mul, hq, smul_comm]
  clear_value M
  let U : R → GL n R := fun a => ddCharUnip (a • M) (hMM a)
  have hU_add : ∀ a b : R, U a * U b = U (a + b) := by
    intro a b
    apply Units.ext
    show (1 + a • M) * (1 + b • M) = 1 + (a + b) • M
    have h0 : (a • M) * (b • M) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hM2, smul_zero, smul_zero]
    simp only [add_mul, mul_add, one_mul, mul_one, h0, add_zero, add_smul]
    abel
  have hconj : d * U q = U p * d := by
    apply Units.ext
    show (d : Matrix n n R) * (1 + q • M) = (1 + p • M) * (d : Matrix n n R)
    rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, hdM, Matrix.smul_mul, hMd,
      smul_smul, smul_smul, mul_comm q p]
  have h1 : ψ (U q) = ψ (U p) := by
    have := congrArg ψ hconj
    rw [map_mul, map_mul, mul_comm (ψ (U p))] at this
    exact mul_left_cancel this
  have h2 : U q = U p * U (q - p) := by rw [hU_add, add_sub_cancel]
  have h3 : ψ (U (q - p)) = 1 := by
    have := congrArg ψ h2
    rw [map_mul, h1] at this
    exact mul_left_cancel (this.symm.trans (mul_one _).symm)
  have h4 : U (q - p) = ddCharUnip N hN := by
    apply Units.ext
    show 1 + (q - p) • M = 1 + N
    rw [hM, smul_smul, ← hc, Units.mul_inv, one_smul]
  rw [← h4]
  exact h3

def ddCharDiag : (n → Rˣ) →* GL n R :=
  (Units.map (diagonalRingHom n R).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem ddCharDiag_val (d : n → Rˣ) :
    ((ddCharDiag d : GL n R) : Matrix n n R) = diagonal fun i => (d i : R) := rfl

theorem ddChar_diag_single (ψ : GL n R →* A) (i j : n) (u : Rˣ) :
    ψ (ddCharDiag (Pi.mulSingle i u)) = ψ (ddCharDiag (Pi.mulSingle j u)) := by
  let σ := Equiv.swap i j
  let P : Matrix n n R := σ.toPEquiv.toMatrix
  have hPP : P * P = 1 := by
    ext a b
    rw [PEquiv.toMatrix_toPEquiv_mul]
    simp [P, σ, PEquiv.toMatrix_apply, Matrix.one_apply]
  let Pg : GL n R := ⟨P, P, hPP, hPP⟩
  have hconj : Pg * ddCharDiag (Pi.mulSingle i u) * Pg = ddCharDiag (Pi.mulSingle j u) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ddCharDiag_val, ddCharDiag_val]
    show P * _ * P = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp only [Matrix.submatrix_apply, id, diagonal_apply, σ, Equiv.symm_swap]
    by_cases hab : a = b
    · subst hab
      simp only [if_true]
      simp [Pi.mulSingle_apply, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have : Equiv.swap i j a ≠ Equiv.swap i j b := fun h => hab ((Equiv.swap i j).injective h)
      simp [hab, this]
  have h := congrArg ψ hconj
  rw [map_mul, map_mul, mul_comm (ψ Pg), mul_assoc, ← map_mul,
    show Pg * Pg = 1 from Units.ext hPP, map_one, mul_one] at h
  exact h

theorem ddChar_diag (ψ : GL n R →* A) (g : GL n R)
    (hg : ∀ i j, i ≠ j → (g : Matrix n n R) i j = 0) (hdet : (g : Matrix n n R).det = 1) :
    ψ g = 1 := by
  have hdiag : (g : Matrix n n R) = diagonal fun k => (g : Matrix n n R) k k := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, hg a b hab]
  have hdet' : ∏ k, (g : Matrix n n R) k k = 1 := by
    have e : (g : Matrix n n R).det = ∏ k, (g : Matrix n n R) k k := by
      conv_lhs => rw [hdiag]
      rw [det_diagonal]
    rw [← e, hdet]
  have hunit : ∀ k, IsUnit ((g : Matrix n n R) k k) := fun k =>
    isUnit_of_dvd_one (hdet' ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
  let dv : n → Rˣ := fun k => (hunit k).unit
  have hgD : g = ddCharDiag dv := by
    apply Units.ext
    rw [ddCharDiag_val, hdiag]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [dv]
    · simp [hab]
  have hprod : ∏ k, dv k = 1 := Units.ext (by rw [Units.coe_prod]; simpa [dv] using hdet')
  let φ : (n → Rˣ) →* A := ψ.comp ddCharDiag
  have hφ : ∀ w, φ w = ψ (ddCharDiag w) := fun w => rfl
  rw [hgD, ← hφ, ← Finset.univ_prod_mulSingle dv, map_prod]
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j0⟩⟩
  · simp [Finset.univ_eq_empty]
  · simp only [hφ]
    rw [Finset.prod_congr rfl fun k _ => ddChar_diag_single ψ k j0 (dv k)]
    rw [show (∏ k, ψ (ddCharDiag (Pi.mulSingle j0 (dv k) : n → Rˣ))) =
      φ (∏ k, (Pi.mulSingle j0 (dv k) : n → Rˣ)) from (map_prod φ _ _).symm]
    have e2 : ∏ k, (Pi.mulSingle j0 (dv k) : n → Rˣ) = (Pi.mulSingle j0 (∏ k, dv k) : n → Rˣ) := by
      funext i
      rw [Finset.prod_apply]
      by_cases hi : i = j0
      · subst hi
        simp
      · simp [hi]
    rw [e2, hprod, Pi.mulSingle_one, map_one]

theorem ddChar_vecMulVec_sq {x y : n → R} (h : y ⬝ᵥ x = 0) :
    vecMulVec x y * vecMulVec x y = 0 := by
  ext i j
  have h' : ∑ k, y k * x k = 0 := h
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, x i * y k * (x k * y j) = x i * y j * ∑ k, y k * x k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h', mul_zero]

theorem ddChar_det_unip {x y : n → R} (h : y ⬝ᵥ x = 0) :
    ((ddCharUnip _ (ddChar_vecMulVec_sq h) : GL n R) : Matrix n n R).det = 1 := by
  show (1 + vecMulVec x y).det = 1
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]

theorem ddChar_row (ψ : GL n R →* A) (u : Rˣ) (hu : IsUnit ((u : R) - 1)) (a : n) (y : n → R)
    (hy : y a = 0) (h : y ⬝ᵥ Pi.single a 1 = 0) :
    ψ (ddCharUnip _ (ddChar_vecMulVec_sq h)) = 1 := by
  refine ddChar_unip_eq_one ψ _ _ (ddCharDiag (Pi.mulSingle a u)) (u : R) 1 ?_ ?_ ?_
  · ext i j
    rw [ddCharDiag_val, Matrix.diagonal_mul, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    by_cases hi : i = a
    · subst hi
      simp
    · simp [hi]
  · ext i j
    rw [ddCharDiag_val, Matrix.mul_diagonal, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul]
    by_cases hj : j = a
    · subst hj
      simp [hy]
    · simp [hj]
  · rw [← neg_sub]
    exact hu.neg

theorem ddChar_col (ψ : GL n R →* A) (u : Rˣ) (hu : IsUnit ((u : R) - 1)) (a : n) (x : n → R)
    (hx : x a = 0) (h : Pi.single a 1 ⬝ᵥ x = 0) :
    ψ (ddCharUnip _ (ddChar_vecMulVec_sq h)) = 1 := by
  refine ddChar_unip_eq_one ψ _ _ (ddCharDiag (Pi.mulSingle a u)) 1 (u : R) ?_ ?_ hu
  · ext i j
    rw [ddCharDiag_val, Matrix.diagonal_mul, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul]
    by_cases hi : i = a
    · subst hi
      simp [hx]
    · simp [hi]
  · ext i j
    rw [ddCharDiag_val, Matrix.mul_diagonal, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    by_cases hj : j = a
    · subst hj
      simp [mul_comm]
    · simp [hj]

theorem ddChar_unip_mul_apply {x y : n → R} (h : y ⬝ᵥ x = 0) (g : GL n R) (i j : n) :
    ((ddCharUnip _ (ddChar_vecMulVec_sq h) * g : GL n R) : Matrix n n R) i j
      = (g : Matrix n n R) i j + x i * ∑ k, y k * (g : Matrix n n R) k j := by
  show ((1 + vecMulVec x y) * (g : Matrix n n R)) i j = _
  rw [add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [vecMulVec_apply]; ring

theorem ddChar_mul_unip_apply {x y : n → R} (h : y ⬝ᵥ x = 0) (g : GL n R) (i j : n) :
    ((g * ddCharUnip _ (ddChar_vecMulVec_sq h) : GL n R) : Matrix n n R) i j
      = (g : Matrix n n R) i j + (∑ k, (g : Matrix n n R) i k * x k) * y j := by
  show ((g : Matrix n n R) * (1 + vecMulVec x y)) i j = _
  rw [mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [vecMulVec_apply]; ring

theorem ddChar_induction [Finite R] (ψ : GL n R →* A) (u : Rˣ) (hu : IsUnit ((u : R) - 1))
    (s : Finset n) : ∀ g : GL n R,
      (∀ i j, i ≠ j → (i ∉ s ∨ j ∉ s) → (g : Matrix n n R) i j = 0) →
      (g : Matrix n n R).det = 1 → ψ g = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg hdet
    exact ddChar_diag ψ g (fun i j hij => hg i j hij (Or.inl (Finset.notMem_empty i))) hdet
  | insert a s ha ih =>
    intro g hg hdet
    have hinv : ∑ k, ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 1 := by
      have := congrArg (fun M : GL n R => (M : Matrix n n R) a a) (inv_mul_cancel g)
      simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this
    have hz : ∀ k ∈ (Finset.univ : Finset n), k ∉ insert a s →
        ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 0 := by
      intro k _ hk
      have hka : k ≠ a := fun e => hk (e ▸ Finset.mem_insert_self a s)
      rw [hg k a hka (Or.inl hk), mul_zero]
    have hwvb : ((g⁻¹ : GL n R) : Matrix n n R) a a * (g : Matrix n n R) a a +
        ∑ k ∈ s, ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 1 := by
      rw [← Finset.sum_insert ha (f := fun k => ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a),
        Finset.sum_subset (Finset.subset_univ _) hz]
      exact hinv
    obtain ⟨t, ht⟩ := ddChar_stable hwvb
    let y1 : n → R := fun k => if k ∈ s then t * ((g⁻¹ : GL n R) : Matrix n n R) a k else 0
    have hy1a : y1 a = 0 := by simp [y1, ha]
    have h1 : y1 ⬝ᵥ Pi.single a 1 = 0 := by rw [dotProduct_single, hy1a, zero_mul]
    let g1 : GL n R := ddCharUnip _ (ddChar_vecMulVec_sq h1) * g
    have e1 : ∀ i j, (g1 : Matrix n n R) i j =
        (g : Matrix n n R) i j + (Pi.single a (1 : R) : n → R) i * ∑ k, y1 k * (g : Matrix n n R) k j :=
      fun i j => ddChar_unip_mul_apply h1 g i j
    have hsum1 : ∀ j, ∑ k, y1 k * (g : Matrix n n R) k j =
        ∑ k ∈ s, t * ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k j := by
      intro j
      simp only [y1, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hg1aa : IsUnit ((g1 : Matrix n n R) a a) := by
      rw [e1, hsum1, Pi.single_eq_same, one_mul]
      convert ht using 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs1 : ∀ i j, i ≠ j → (i ∉ insert a s ∨ j ∉ insert a s) → (g1 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      rw [e1]
      by_cases hia : i = a
      · subst hia
        have hj : j ∉ insert i s := by
          rcases hout with h | h
          · exact absurd (Finset.mem_insert_self i s) h
          · exact h
        rw [hg i j hij (Or.inr hj), zero_add, hsum1]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => ?_)
        have hkj : k ≠ j := fun e => hj (e ▸ Finset.mem_insert_of_mem hk)
        rw [hg k j hkj (Or.inr hj), mul_zero]
      · rw [Pi.single_eq_of_ne hia, zero_mul, add_zero]
        exact hg i j hij hout
    have hdet1 : (g1 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h1, hdet, one_mul]
    have hψ1 : ψ g1 = ψ g := by rw [map_mul, ddChar_row ψ u hu a y1 hy1a h1, one_mul]
    let C : R := (g1 : Matrix n n R) a a
    let ci : R := ((hg1aa.unit⁻¹ : Rˣ) : R)
    have hCci : C * ci = 1 := hg1aa.mul_val_inv
    have hciC : ci * C = 1 := by rw [mul_comm]; exact hCci
    let x2 : n → R := fun i => if i = a then 0 else -((g1 : Matrix n n R) i a * ci)
    have hx2a : x2 a = 0 := by simp [x2]
    have h2 : Pi.single a 1 ⬝ᵥ x2 = 0 := by rw [single_dotProduct, hx2a, mul_zero]
    let g2 : GL n R := ddCharUnip _ (ddChar_vecMulVec_sq h2) * g1
    have e2 : ∀ i j, (g2 : Matrix n n R) i j = (g1 : Matrix n n R) i j + x2 i * (g1 : Matrix n n R) a j := by
      intro i j
      rw [ddChar_unip_mul_apply h2 g1 i j]
      congr 2
      simp [Pi.single_apply, ite_mul]
    have hg2a : ∀ i, i ≠ a → (g2 : Matrix n n R) i a = 0 := by
      intro i hia
      rw [e2]
      simp only [x2, if_neg hia]
      change (g1 : Matrix n n R) i a + -((g1 : Matrix n n R) i a * ci) * C = 0
      rw [neg_mul, mul_assoc, hciC, mul_one, add_neg_cancel]
    have hg2aj : ∀ j, (g2 : Matrix n n R) a j = (g1 : Matrix n n R) a j := by
      intro j
      rw [e2, hx2a, zero_mul, add_zero]
    have hs2 : ∀ i j, i ≠ j → (i ∉ insert a s ∨ j ∉ insert a s) → (g2 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      by_cases hia : i = a
      · subst hia
        rw [hg2aj]
        exact hs1 i j hij hout
      · rw [e2, hs1 i j hij hout, zero_add]
        simp only [x2, if_neg hia]
        rcases hout with h | h
        · rw [hs1 i a hia (Or.inl h), zero_mul, neg_zero, zero_mul]
        · have haj : a ≠ j := fun e => h (e ▸ Finset.mem_insert_self a s)
          rw [hs1 a j haj (Or.inr h), mul_zero]
    have hdet2 : (g2 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h2, hdet1, one_mul]
    have hψ2 : ψ g2 = ψ g1 := by rw [map_mul, ddChar_col ψ u hu a x2 hx2a h2, one_mul]
    let y3 : n → R := fun j => if j = a then 0 else -(ci * (g2 : Matrix n n R) a j)
    have hy3a : y3 a = 0 := by simp [y3]
    have h3 : y3 ⬝ᵥ Pi.single a 1 = 0 := by rw [dotProduct_single, hy3a, zero_mul]
    let g3 : GL n R := g2 * ddCharUnip _ (ddChar_vecMulVec_sq h3)
    have e3 : ∀ i j, (g3 : Matrix n n R) i j = (g2 : Matrix n n R) i j + (g2 : Matrix n n R) i a * y3 j := by
      intro i j
      rw [ddChar_mul_unip_apply h3 g2 i j]
      congr 2
      simp [Pi.single_apply]
    have hg2aa : (g2 : Matrix n n R) a a = C := by rw [hg2aj]
    have hs3 : ∀ i j, i ≠ j → (i ∉ s ∨ j ∉ s) → (g3 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      rw [e3]
      by_cases hia : i = a
      · subst hia
        have hja : j ≠ i := fun e => hij e.symm
        simp only [y3, if_neg hja]
        rw [hg2aa, mul_neg, ← mul_assoc, hCci, one_mul, add_neg_cancel]
      · rw [hg2a i hia, zero_mul, add_zero]
        by_cases hja : j = a
        · subst hja
          exact hg2a i hia
        · have hout' : i ∉ insert a s ∨ j ∉ insert a s := by
            rcases hout with h | h
            · exact Or.inl (by simp [hia, h])
            · exact Or.inr (by simp [hja, h])
          exact hs2 i j hij hout'
    have hdet3 : (g3 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h3, hdet2, mul_one]
    have hψ3 : ψ g3 = ψ g2 := by rw [map_mul, ddChar_row ψ u hu a y3 hy3a h3, mul_one]
    rw [← hψ1, ← hψ2, ← hψ3]
    exact ih g3 hs3 hdet3

end DetOneChar

theorem generalLinearGroup_char_eq_one_of_det_eq_one :
    ∀ (R : Type) [CommRing R] [Finite R] (r : ℕ) (A : Type) [CommGroup A]
      (ψ : GL (Fin r) R →* A), (∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 4 ≤ Nat.card (R ⧸ 𝔪)) →
      ∀ g : GL (Fin r) R, (g : Matrix (Fin r) (Fin r) R).det = 1 → ψ g = 1 := by
  intro R _ _ r A _ ψ h4 g hdet
  obtain ⟨u, hu⟩ := ddChar_exists_unit h4
  exact ddChar_induction ψ u hu Finset.univ g (fun i j _ hout => by simp at hout) hdet

end GlobalTheory
