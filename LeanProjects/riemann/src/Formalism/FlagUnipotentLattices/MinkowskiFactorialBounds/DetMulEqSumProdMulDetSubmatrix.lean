import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

lemma submatrix_mul_castLE_of_lower {R : Type*} [CommRing R] {N l : ℕ} {α : Type*} (hl : l ≤ N)
    (Lo : Matrix (Fin N) (Fin N) R) (X : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hLo : ∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → Lo i j = 0) :
    (Lo * X).submatrix (Fin.castLE hl) g =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * X.submatrix (Fin.castLE hl) g := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
  · intro k hk
    have : l ≤ (k : ℕ) := by
      by_contra hlt
      exact hk ⟨⟨k, by omega⟩, by ext; simp⟩
    rw [hLo _ _ (by simp) this, zero_mul]
  · intro k; rfl

lemma submatrix_mul_castLE_of_upper {R : Type*} [CommRing R] {N l : ℕ} {α : Type*} (hl : l ≤ N)
    (X : Matrix (Fin N) (Fin N) R) (Up : Matrix (Fin N) (Fin N) R) (g : α → Fin N)
    (hUp : ∀ i j : Fin N, l ≤ (i : ℕ) → (j : ℕ) < l → Up i j = 0) :
    (X * Up).submatrix g (Fin.castLE hl) =
      X.submatrix g (Fin.castLE hl) * Up.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
  · intro k hk
    have : l ≤ (k : ℕ) := by
      by_contra hlt
      exact hk ⟨⟨k, by omega⟩, by ext; simp⟩
    rw [hUp _ _ this (by simp), mul_zero]
  · intro k; rfl

lemma det_submatrix_castLE_of_unitLower {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (Lo : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Lo i i = 1) (h0 : ∀ i j, i < j → Lo i j = 0) :
    (Lo.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [h1]
  · intro i j hij
    exact h0 _ _ (by simpa using hij)

lemma det_submatrix_castLE_of_unitUpper {R : Type*} [CommRing R] {N l : ℕ} (hl : l ≤ N)
    (Up : Matrix (Fin N) (Fin N) R) (h1 : ∀ i, Up i i = 1) (h0 : ∀ i j, j < i → Up i j = 0) :
    (Up.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h1]
  · intro i j hij
    exact h0 _ _ (by simpa using hij)

theorem leadingMinorTriangularInvariant : LeadingMinorInvariant := by
  intro R _ N l hl Lo W Up hL1 hL0 hU1 hU0
  rw [Matrix.mul_assoc, submatrix_mul_castLE_of_lower hl Lo (W * Up) _ (fun i j hi hj => hL0 i j (by
      rw [Fin.lt_def]; omega)),
    submatrix_mul_castLE_of_upper hl W Up _ (fun i j hi hj => hU0 i j (by rw [Fin.lt_def]; omega)),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_unitLower hl Lo hL1 hL0, det_submatrix_castLE_of_unitUpper hl Up hU1 hU0]
  ring

theorem leadingMinorColumnReplace : CramerUpper := by
  intro R _ N l hl Lo W Up hL1 hL0 hU1 hU0 hW c b hc
  have hLo' : ∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → Lo i j = 0 := fun i j hi hj =>
    hL0 i j (by rw [Fin.lt_def]; omega)
  have key : ∀ {α : Type} (g : α → Fin N), (Lo * W * Up).submatrix (Fin.castLE hl) g =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * (W.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Up.submatrix (Fin.castLE hl) g) := by
    intro α g
    rw [Matrix.mul_assoc, submatrix_mul_castLE_of_lower hl Lo (W * Up) g hLo', submatrix_mul_castLE_of_lower hl W Up g hW]
  rw [key, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_submatrix_castLE_of_unitUpper hl Up hU1 hU0]
  set A := Up.submatrix (Fin.castLE hl) (Fin.castLE hl) with hA
  have hAdet : A.det = 1 := det_submatrix_castLE_of_unitUpper hl Up hU1 hU0
  set u : Fin l → R := fun k => Up (Fin.castLE hl k) b with hu
  have e1 : Up.submatrix (Fin.castLE hl) (fun j => if j = c then b else Fin.castLE hl j) =
      A.updateCol c u := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.updateCol_apply, hA, hu]
    split_ifs <;> rfl
  have hrow : ∀ j, A c j = if j = c then 1 else 0 := by
    intro j
    rcases lt_trichotomy j c with h | h | h
    · rw [if_neg h.ne]; exact hU0 _ _ (by simpa using h)
    · subst h; simp [hA, hU1]
    · rw [if_neg h.ne']; exact hc j h
  have hadj : ∀ k, A.adjugate c k = if k = c then 1 else 0 := by
    intro k
    have h1 : (A * A.adjugate) c k = (1 : Matrix (Fin l) (Fin l) R) c k := by
      rw [Matrix.mul_adjugate, hAdet, one_smul]
    rw [Matrix.mul_apply] at h1
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [h1, Matrix.one_apply]
    simp only [eq_comm]
  have e2 : (A.updateCol c u).det = u c := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
    simp [hadj]
  rw [e1, e2]; ring

theorem complementNormIdentity : OmegaNorm := by
  intro K V _ _ _ _ h hh r f f' T T' x w ζ hG hG' hT hxmem hw hom
  set Z := crossGram h f f' with hZ
  set z := f (Fin.last r) with hz
  have hx : ∀ y, (∀ a : Fin r, h (f a.castSucc) y = 0) → h x y = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun v _ => h v y = 0) ?_ ?_ ?_ ?_ hxmem
    · rintro v ⟨a, rfl⟩; exact hy a
    · simp
    · intro u v _ _ hu hv; simp [hu, hv]
    · intro c u _ hu; simp [hu]
  have hne : ∀ a : Fin r, a.castSucc ≠ Fin.last r := fun a => (Fin.castSucc_lt_last a).ne
  have hez : ∀ a : Fin r, ∀ b, h (f a.castSucc) (f b) = 0 := fun a b => by
    rw [hG]; simp [hne a]
  have hxf : ∀ b, h x (f b) = 0 := fun b => hx _ fun a => hez a b
  have hxw : h x w = 0 := hx _ fun a => by rw [hh w, hw, star_zero]
  have hwx : h w x = 0 := by rw [hh x, hxw, star_zero]
  have hxx : h x x = 0 := hx _ fun a => by rw [hh x, hxf, star_zero]
  have hzx : h z x = 0 := by rw [hh x, hxf, star_zero]
  have hzw : h z w = 0 := by rw [hh w, hw, star_zero]
  have hzz : h z z = -T := by rw [hz, hG]; simp
  have hxz : h x z = 0 := hxf _
  have hwz : h w z = 0 := hw _
  have hTs : star T = T := by
    have := hh z z
    rw [hzz] at this
    have h2 : star (-T) = -star T := star_neg T
    rw [h2] at this
    exact (neg_injective this).symm
  set om := ∑ b, Z.adjugate b (Fin.last r) • f' b with hom'

  have h1 : h om z = Z.det := by
    rw [hom']
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have : (Z * Z.adjugate) (Fin.last r) (Fin.last r) = Z.det := by
      rw [Matrix.mul_adjugate]; simp
    rw [← this, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  have h2 : h om z = -(ζ * T) := by
    rw [hom]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hxz, hwz,
      hzz, ← hz]
    ring
  have hdet : Z.det = -(ζ * T) := h1.symm.trans h2

  have h3 : h om om = -(T' * (Z.adjugate (Fin.last r) (Fin.last r) *
      star (Z.adjugate (Fin.last r) (Fin.last r)))) := by
    rw [hom']
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.map_smulₛₗ, starRingEnd_apply, hG']
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp; ring
      · intro b _ hb; simp [hb]
      · simp
    · intro b _ hb
      simp [hb]
    · simp
  have h4 : h om om = h w w - ζ * star ζ * T := by
    rw [hom]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.map_smulₛₗ, starRingEnd_apply, hxx, hxw, hwx, hxz, hwz, hzx, hzw, hzz, ← hz]
    ring
  have hadj : Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    simp [← two_mul]
  rw [← hadj, hdet, star_neg, star_mul, hTs]
  have h5 : h w w = ζ * star ζ * T - T' * (Z.adjugate (Fin.last r) (Fin.last r) *
      star (Z.adjugate (Fin.last r) (Fin.last r))) := by
    have := h3.symm.trans h4
    linear_combination -this
  rw [h5]; ring

def consRowMatrix {R : Type*} {r : ℕ} (u : Fin (r + 1) → R) (Y : Matrix (Fin r) (Fin (r + 1)) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun i => Fin.cases u (fun a => Y a) i

lemma s5bCons_zero {R : Type*} {r : ℕ} (u : Fin (r + 1) → R) (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (j : Fin (r + 1)) : consRowMatrix u Y 0 j = u j := rfl

lemma s5bCons_succ {R : Type*} {r : ℕ} (u : Fin (r + 1) → R) (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (a : Fin r) (j : Fin (r + 1)) : consRowMatrix u Y a.succ j = Y a j := rfl

lemma det_consRow {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) :
    (consRowMatrix u Y).det = ∑ b, u b * cofVec Y b := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (consRowMatrix u Y).submatrix Fin.succ b.succAbove =
      Y.submatrix id b.succAbove := by
    ext i j; rfl
  rw [this, s5bCons_zero]; simp only [cofVec]; ring

lemma neg_one_pow_mul_neg_one_pow {R : Type*} [CommRing R] (n : ℕ) : ((-1 : R) ^ n) * ((-1) ^ n) = 1 := by
  rw [← mul_pow]; simp

lemma det_submatrix_consRow_succAbove {R : Type*} [CommRing R] {n : ℕ} (Y : Matrix (Fin (n + 1)) (Fin (n + 2)) R)
    (u : Fin (n + 2) → R) (b₀ : Fin (n + 2)) (a : Fin (n + 1)) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by
  have e : (consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove =
      consRowMatrix (fun c => u (b₀.succAbove c))
        ((Y.submatrix id b₀.succAbove).submatrix a.succAbove id) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.submatrix_apply, Fin.succ_succAbove_zero, s5bCons_zero]
    · simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, s5bCons_succ, id]
  rw [e, det_consRow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [cofVec, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  have hs := neg_one_pow_mul_neg_one_pow (R := R) (a : ℕ)
  rw [pow_add]
  generalize (Y.submatrix a.succAbove (b₀.succAbove ∘ c.succAbove)).det = M
  linear_combination (-(u (b₀.succAbove c) * (-1) ^ (c : ℕ) * M)) * hs

lemma det_submatrix_consRow_succAbove' {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) (b₀ : Fin (r + 1)) (a : Fin r) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by
  cases r with
  | zero => exact a.elim0
  | succ n => exact det_submatrix_consRow_succAbove Y u b₀ a

theorem cofactorVectorKernel : KernelRowSpace := by
  intro R _ r Y
  constructor
  · ext a
    have h := det_consRow Y (Y a)
    have h0 : (consRowMatrix (Y a) Y).det = 0 :=
      Matrix.det_zero_of_row_eq (i := 0) (j := a.succ) (Fin.succ_ne_zero a).symm (by ext j; rfl)
    rw [h0] at h
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    exact h.symm
  · intro u hu b₀
    have hA := det_consRow Y u
    rw [hu] at hA
    ext b
    simp only [Pi.smul_apply, smul_eq_mul]
    rcases Fin.eq_self_or_eq_succAbove b₀ b with hb | ⟨c, hb⟩
    · rw [hb]
      rw [Matrix.det_succ_column _ b₀, Fin.sum_univ_succ] at hA
      have t0 : (consRowMatrix u Y).submatrix (Fin.succAbove 0) b₀.succAbove =
          Y.submatrix id b₀.succAbove := by
        ext i j; simp only [Matrix.submatrix_apply, Fin.succAbove_zero, s5bCons_succ, id]
      rw [t0] at hA
      simp only [det_submatrix_consRow_succAbove', s5bCons_zero, s5bCons_succ,
        Fin.val_zero, Fin.val_succ, zero_add] at hA
      have hterm : ∀ a : Fin r, (-1 : R) ^ ((a : ℕ) + 1 + (b₀ : ℕ)) * Y a b₀ *
          ((-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a) =
          -((-1) ^ (b₀ : ℕ) * ((∑ c, u (b₀.succAbove c) *
            (Y.submatrix id b₀.succAbove).adjugate c a) * Y a b₀)) := by
        intro a
        have hs := neg_one_pow_mul_neg_one_pow (R := R) (a : ℕ)
        rw [pow_add, pow_add, pow_one]
        linear_combination (-((-1) ^ (b₀ : ℕ) * Y a b₀ * ∑ c, u (b₀.succAbove c) *
            (Y.submatrix id b₀.succAbove).adjugate c a)) * hs
      simp only [hterm, Finset.sum_neg_distrib, ← Finset.mul_sum] at hA
      have hs := neg_one_pow_mul_neg_one_pow (R := R) (b₀ : ℕ)
      simp only [Matrix.vecMul, dotProduct]
      linear_combination ((-1) ^ (b₀ : ℕ)) * hA - ((Y.submatrix id b₀.succAbove).det * u b₀ -
        ∑ a, (∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a) * Y a b₀) * hs
    · rw [hb]
      have : (((fun c => u (b₀.succAbove c)) ᵥ* (Y.submatrix id b₀.succAbove).adjugate) ᵥ* Y)
          (b₀.succAbove c) = (((fun c => u (b₀.succAbove c)) ᵥ*
            (Y.submatrix id b₀.succAbove).adjugate) ᵥ* (Y.submatrix id b₀.succAbove)) c := by
        simp [Matrix.vecMul, dotProduct]
      rw [this, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
      simp

theorem unitriangularReduction : UnipotentReduce := by
  intro E _ O FF N u hFF hu1 hu0
  classical
  have key : ∀ t : ℕ, ∃ n : Matrix (Fin N) (Fin N) E, (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, n i j ∈ O) ∧
      ∀ i j : Fin N, i < j → N ≤ (i:ℕ) + t → (u * n) i j ∈ FF := by
    intro t
    induction t with
    | zero =>
      refine ⟨1, by simp, fun i j h => Matrix.one_apply_ne h.ne', fun i j => ?_,
        fun i j _ h => absurd i.2 (by omega)⟩
      rw [Matrix.one_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    | succ t ih =>
      obtain ⟨n, h1, h0, hO, hF⟩ := ih
      by_cases ht : t < N
      · let s : Fin N := ⟨N - t - 1, by omega⟩
        choose a ha using fun j : Fin N =>
          hFF (∑ k ∈ Finset.univ.filter (fun k => s < k), u s k * n k j)
        let n' : Matrix (Fin N) (Fin N) E := n.updateRow s (fun j => if s < j then a j else n s j)
        have hn's : ∀ j, n' s j = if s < j then a j else n s j := fun j => by
          simp [n', Matrix.updateRow_self]
        have hn'ne : ∀ i j, i ≠ s → n' i j = n i j := fun i j hi => by
          simp [n', Matrix.updateRow_ne hi]
        have hmul : ∀ i j, (u * n') i j = (u * n) i j + u i s * (n' s j - n s j) := by
          intro i j
          simp only [Matrix.mul_apply]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
            ← Finset.add_sum_erase Finset.univ (fun k => u i k * n k j) (Finset.mem_univ s)]
          have : ∑ k ∈ Finset.univ.erase s, u i k * n' k j =
              ∑ k ∈ Finset.univ.erase s, u i k * n k j :=
            Finset.sum_congr rfl fun k hk => by rw [hn'ne k j (Finset.ne_of_mem_erase hk)]
          rw [this]; ring
        refine ⟨n', ?_, ?_, ?_, ?_⟩
        · intro i
          by_cases hi : i = s
          · subst hi; rw [hn's, if_neg (lt_irrefl _), h1]
          · rw [hn'ne i i hi, h1]
        · intro i j hji
          by_cases hi : i = s
          · subst hi; rw [hn's, if_neg (not_lt.2 hji.le), h0 _ _ hji]
          · rw [hn'ne i j hi, h0 _ _ hji]
        · intro i j
          by_cases hi : i = s
          · subst hi; rw [hn's]; split_ifs
            · exact (ha j).1
            · exact hO _ _
          · rw [hn'ne i j hi]; exact hO _ _
        · intro i j hij hi
          rw [hmul]
          by_cases his : i = s
          · subst his
            rw [hu1, hn's, if_pos hij]
            have hsplit : (u * n) s j = n s j +
                ∑ k ∈ Finset.univ.filter (fun k => s < k), u s k * n k j := by
              rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => s < k)]
              rw [add_comm]; congr 1
              rw [Finset.sum_eq_single s]
              · rw [hu1, one_mul]
              · intro k hk hki
                have : k < s := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hk).2) hki
                rw [hu0 _ _ this, zero_mul]
              · intro h; exact (h (by simp)).elim
            rw [hsplit]
            have := (ha j).2
            convert this using 1; ring
          · have hsi : s < i := by
              rw [Fin.lt_def]
              have : (i : ℕ) ≠ (s : ℕ) := fun h => his (Fin.ext h)
              have hs : (s : ℕ) = N - t - 1 := rfl
              omega
            rw [hu0 _ _ hsi, zero_mul, add_zero]
            apply hF i j hij
            have hs : (s : ℕ) = N - t - 1 := rfl
            rw [Fin.lt_def] at hsi
            omega
      · exact ⟨n, h1, h0, hO, fun i j hij _ => hF i j hij (by omega)⟩
  obtain ⟨n, h1, h0, hO, hF⟩ := key N
  exact ⟨n, h1, h0, hO, fun i j hij => hF i j hij (by omega)⟩

theorem normMinorMonomialLe : MonomialMinor := by
  intro N σ c t I J
  classical
  set W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => if j = σ i then c i else 0 with hW
  set P := ∏ i, max 1 ‖c i‖ with hP
  have hP1 : 1 ≤ P := one_le_finset_prod_real_of_forall_one_le _ _ fun i _ => le_max_left _ _
  by_cases hI : Function.Injective I
  · set g : Equiv.Perm (Fin t) → ℝ := fun π => ∏ i, ‖(W.submatrix I J) (π i) i‖ with hg
    have hdet : ‖(W.submatrix I J).det‖ ≤ ∑ π, g π := by
      rw [Matrix.det_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π _ => ?_)
      rw [hg]
      simp only [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
      have h2 : ‖(((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
      rw [h2, one_mul]
    have hgle : ∀ π, g π ≤ P := by
      intro π
      calc g π ≤ ∏ i, max 1 ‖c (I (π i))‖ := by
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
            simp only [hW, Matrix.submatrix_apply, Matrix.of_apply]
            split_ifs
            · exact le_max_right _ _
            · simp
        _ = ∏ i, max 1 ‖c (I i)‖ := Equiv.prod_comp π (fun i => max 1 ‖c (I i)‖)
        _ = ∏ k ∈ Finset.univ.image I, max 1 ‖c k‖ := by
            rw [Finset.prod_image (fun a _ b _ h => hI h)]
        _ ≤ P := finset_prod_le_prod_of_subset_of_one_le _ _ (Finset.subset_univ _) _ fun k _ => le_max_left _ _
    have huniq : ∀ π π', g π ≠ 0 → g π' ≠ 0 → π = π' := by
      intro π π' h h'
      have key : ∀ ρ : Equiv.Perm (Fin t), g ρ ≠ 0 → ∀ i, J i = σ (I (ρ i)) := by
        intro ρ hρ i
        by_contra hne
        apply hρ
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hW, hne]
      ext i
      have := (key π h i).symm.trans (key π' h' i)
      exact congrArg _ (hI (σ.injective this))
    refine hdet.trans ?_
    by_cases hex : ∃ π₀, g π₀ ≠ 0
    · obtain ⟨π₀, h₀⟩ := hex
      rw [Finset.sum_eq_single π₀]
      · exact hgle π₀
      · intro π _ hne
        by_contra hπ
        exact hne (huniq π π₀ hπ h₀)
      · simp
    · push_neg at hex
      rw [Finset.sum_eq_zero fun π _ => hex π]; linarith
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by
      simpa [Function.Injective] using hI
    rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])]
    simp; linarith

lemma det_mul_eq_sum_prod_mul_det_submatrix {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ) :
    (X * Y).det = ∑ f : Fin t → Fin N, (∏ i, X i (f i)) * (Y.submatrix f id).det := by
  have h1 : (X * Y) = Matrix.of (fun i => ∑ k, X i k • Y k) := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h1]
  have h2 := (Matrix.detRowAlternating (n := Fin t) (R := ℂ)).toMultilinearMap.map_sum
    (fun i k => X i k • Y k)
  have h3 : (Matrix.of (fun i => ∑ k, X i k • Y k)).det =
      ∑ f : Fin t → Fin N, Matrix.detRowAlternating (fun i => X i (f i) • Y (f i)) := h2
  rw [h3]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h4 := (Matrix.detRowAlternating (n := Fin t) (R := ℂ)).toMultilinearMap.map_smul_univ
    (fun i => X i (f i)) (fun i => Y (f i))
  exact h4

lemma card_injective_fin_le_factorial (t N : ℕ) :
    (Finset.univ.filter (fun f : Fin t → Fin N => Function.Injective f)).card ≤ N.factorial := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  by_cases h : t ≤ N
  · rw [← Nat.factorial_mul_descFactorial h]
    exact Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]; exact Nat.zero_le _

lemma norm_det_mul_le {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ)
    (ρ Q : ℝ) (hρ : 1 ≤ ρ) (hQ : 0 ≤ Q) (hX : ∀ i k, ‖X i k‖ ≤ ρ)
    (hY : ∀ f : Fin t → Fin N, ‖(Y.submatrix f id).det‖ ≤ Q) :
    ‖(X * Y).det‖ ≤ (N.factorial : ℝ) * ρ ^ N * Q := by
  classical
  rw [det_mul_eq_sum_prod_mul_det_submatrix]
  have hterm : ∀ f : Fin t → Fin N, ‖(∏ i, X i (f i)) * (Y.submatrix f id).det‖ ≤
      if Function.Injective f then ρ ^ N * Q else 0 := by
    intro f
    split_ifs with hf
    · have htN : t ≤ N := by simpa using Fintype.card_le_of_injective f hf
      rw [norm_mul, norm_prod]
      apply mul_le_mul _ (hY f) (norm_nonneg _) (by positivity)
      calc ∏ i, ‖X i (f i)‖ ≤ ∏ _i : Fin t, ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hX _ _)
        _ = ρ ^ t := by simp
        _ ≤ ρ ^ N := pow_le_pow_right₀ hρ htN
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
        simpa [Function.Injective] using hf
      rw [Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])]; simp
  calc _ ≤ ∑ f : Fin t → Fin N, ‖(∏ i, X i (f i)) * (Y.submatrix f id).det‖ := norm_sum_le _ _
    _ ≤ ∑ f : Fin t → Fin N, if Function.Injective f then ρ ^ N * Q else 0 :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = ((Finset.univ.filter (fun f : Fin t → Fin N => Function.Injective f)).card : ℝ) *
        (ρ ^ N * Q) := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N.factorial : ℝ) * (ρ ^ N * Q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_injective_fin_le_factorial t N
    _ = _ := by ring

theorem normMinorMulLe : MinorBound := by
  intro N A w B ρ P hρ hA hB hw t I J
  have hP : 0 ≤ P := (norm_nonneg _).trans (hw 0 Fin.elim0 Fin.elim0)
  have e : (A * w * B).submatrix I J = (A.submatrix I id) * ((w * B).submatrix id J) := by
    rw [Matrix.mul_assoc]; ext i j; simp [Matrix.mul_apply]
  rw [e]
  have h2 : ∀ f : Fin t → Fin N, ‖(((w * B).submatrix id J).submatrix f id).det‖ ≤
      (N.factorial : ℝ) * ρ ^ N * P := by
    intro f
    have e2 : ((w * B).submatrix id J).submatrix f id =
        ((B.submatrix id J)ᵀ * (w.submatrix f id)ᵀ)ᵀ := by
      rw [← Matrix.transpose_mul]; ext i j; simp [Matrix.mul_apply, mul_comm]
    rw [e2, Matrix.det_transpose]
    apply norm_det_mul_le _ _ ρ P hρ hP (fun i k => hB _ _)
    intro g
    have : ((w.submatrix f id)ᵀ).submatrix g id = (w.submatrix f g)ᵀ := by ext i j; simp
    rw [this, Matrix.det_transpose]; exact hw t f g
  have h1 := norm_det_mul_le (A.submatrix I id) ((w * B).submatrix id J) ρ _ hρ (by positivity)
    (fun i k => hA _ _) h2
  refine h1.trans ?_
  have h4 : (1:ℝ) ≤ 4 ^ N := one_le_pow₀ (by norm_num)
  calc (N.factorial : ℝ) * ρ ^ N * ((N.factorial : ℝ) * ρ ^ N * P)
      = 1 * ((N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P) := by ring
    _ ≤ 4 ^ N * ((N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P) := by gcongr
    _ = _ := by ring

end Formalism.HermitianLatticeCounting.P
