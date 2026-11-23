import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm

namespace GlobalTheory.PtEx

theorem exists_blocks {K : Type} [Zero K] (n : ℕ) : ∀ (w : ℕ → ℕ) (d : ℕ → K), (∀ a < n, d a ≠ 0) →
    (∀ a < n, w a < n) → (∀ a < n, ∀ b < n, w a = w b → a = b) → (∀ v < n, ∃ a < n, w a = v) →
    (∀ a b, a < b → b < n → w a = w b + 1 → b = a + 1 ∧ d a = d b) →
    ∃ bs : List (K × ℕ), ((∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ (bs.map Prod.snd).sum = n) ∧
      ∀ a < n, ∀ b < n, Formalism.MainNotions.S.ptEntry bs a b = if a = w b then d b else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w d hd hlt hinj hsur hC
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨[], by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
  obtain ⟨s, hs⟩ : ∃ s, s = w 0 + 1 := ⟨_, rfl⟩
  have hsn : s ≤ n := by have := hlt 0 hn; omega
  have run (a : ℕ) : a < s → ∀ c ≤ a, w c + c + 1 = s ∧ d c = d 0 := by
    induction a with
    | zero => intro _ c hc; obtain rfl : c = 0 := by omega
              exact ⟨by omega, rfl⟩
    | succ a iha =>
      intro ha c hc
      have k := iha (by omega)
      rcases Nat.lt_or_ge c (a + 1) with h | h
      · exact k c (by omega)
      obtain rfl : c = a + 1 := by omega
      have ka := k a le_rfl
      obtain ⟨b, hb, e⟩ := hsur (w a - 1) (by omega)
      have hab : a < b := by
        by_contra h
        have := (k b (by omega)).1
        omega
      obtain ⟨rfl, e2⟩ := hC a b hab hb (by omega)
      exact ⟨by omega, e2.symm.trans ka.2⟩
  have lo (c : ℕ) (hc : c < s) : w c + c + 1 = s ∧ d c = d 0 := run c hc c le_rfl
  have hi (c : ℕ) (hc : s ≤ c) (hcn : c < n) : s ≤ w c := by
    by_contra h
    have h1 := (lo (s - 1 - w c) (by omega)).1
    have := hinj c hcn (s - 1 - w c) (by omega) (by omega)
    omega
  obtain ⟨bs, ⟨h1, h2⟩, h3⟩ := ih (n - s) (by omega) (fun a => w (a + s) - s) (fun a => d (a + s))
    (fun a ha => hd _ (by omega))
    (fun a ha => by have := hlt (a + s) (by omega); have := hi (a + s) (by omega) (by omega); omega)
    (fun a ha b hb e => by
      have := hi (a + s) (by omega) (by omega)
      have := hi (b + s) (by omega) (by omega)
      have := hinj (a + s) (by omega) (b + s) (by omega) (by omega)
      omega)
    (fun v hv => by
      obtain ⟨b, hb, e⟩ := hsur (v + s) (by omega)
      have : s ≤ b := by
        by_contra h
        have := (lo b (by omega)).1
        omega
      exact ⟨b - s, by omega, by simp only [Nat.sub_add_cancel this]; omega⟩)
    (fun a b hab hb e => by
      have := hi (a + s) (by omega) (by omega)
      have := hi (b + s) (by omega) (by omega)
      have := hC (a + s) (b + s) (by omega) (by omega) (by omega)
      exact ⟨by omega, this.2⟩)
  refine ⟨(d 0, s) :: bs, ⟨?_, by simp [h2]; omega⟩, fun a ha b hb => ?_⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨hd 0 hn, by omega⟩, h1⟩
  · rw [Formalism.MainNotions.S.ptEntry]
    rcases Nat.lt_or_ge b s with hbs | hbs
    · obtain ⟨e1, e2⟩ := lo b hbs
      rw [e2]
      split_ifs <;> first | rfl | omega
    · have := hi b hbs hb
      rw [if_neg (by omega)]
      rcases Nat.lt_or_ge a s with has | has
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_pos ⟨has, hbs⟩, h3 _ (by omega) _ (by omega)]
        simp only [Nat.sub_add_cancel hbs]
        split_ifs <;> first | rfl | omega

theorem exists_point {K : Type} [Zero K] {n : ℕ} (w : Equiv.Perm (Fin n)) (d : Fin n → K) (hd : ∀ a, d a ≠ 0)
    (hC : ∀ a b, a < b → (w a : ℕ) = w b + 1 → (b : ℕ) = a + 1 ∧ d a = d b) :
    ∃ p : Formalism.MainNotions.S.Point K n, Formalism.MainNotions.S.ptMat p = Matrix.of fun a b => if a = w b then d b else 0 := by
  obtain ⟨bs, h1, h2⟩ := exists_blocks n (fun a => if h : a < n then (w ⟨a, h⟩ : ℕ) else 0)
    (fun a => if h : a < n then d ⟨a, h⟩ else 0) (fun a ha => by simpa [ha] using hd _)
    (fun a ha => by simp [ha])
    (fun a ha b hb e => by
      simp only [ha, hb, dif_pos] at e
      simpa using w.injective (Fin.ext e))
    (fun v hv => ⟨w.symm ⟨v, hv⟩, (w.symm _).2, by simp⟩)
    (fun a b hab hb e => by
      have ha : a < n := hab.trans hb
      simp only [ha, hb, dif_pos] at e ⊢
      exact hC ⟨a, ha⟩ ⟨b, hb⟩ hab e)
  refine ⟨⟨bs, h1⟩, Matrix.ext fun a b => (h2 a a.2 b b.2).trans ?_⟩
  simp [Fin.ext_iff]

variable {E : Type} [Field E]

theorem exists_lo_mono_up {n : ℕ} {Z : Matrix (Fin n) (Fin n) E} (hZ : Z.det ≠ 0) :
    ∃ (l u : Matrix (Fin n) (Fin n) E) (w : Equiv.Perm (Fin n)) (d : Fin n → E), IsLo l ∧ IsUp u ∧
      (∀ a, d a ≠ 0) ∧ Z = l * (Matrix.of fun a b => if a = w b then d b else 0) * u := by
  have h : (Z.submatrix Fin.revPerm id).det ≠ 0 := by
    rw [Matrix.det_permute]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with e | e <;> simpa [e] using hZ
  obtain ⟨m, v, hv, u, hu, e⟩ := GlobalTheory.FinGL.Bruhat.exists_decomp (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)
  refine ⟨(v : Matrix (Fin n) (Fin n) E).submatrix Fin.rev Fin.rev, u, m.1.trans Fin.revPerm,
    fun b => m.2 b, fun i j => ⟨fun h => Formalism.L2.DIV.unip_lower hv (by simpa using h),
      fun h => h ▸ Formalism.L2.DIV.unip_diag hv _⟩, fun i j => ⟨fun h => Formalism.L2.DIV.unip_lower hu h,
      fun h => h ▸ Formalism.L2.DIV.unip_diag hu _⟩, fun b => (m.2 b).ne_zero, ?_⟩
  ext a b
  have := congrFun (congrFun e a.rev) b
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply] at this
  simpa [Matrix.mul_apply, GlobalTheory.FinGL.Bruhat.mono] using this

section Lie

variable {σ : E →+* E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {T T' : E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {Z A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b E) : cT σ (cT σ M) = M := by
  ext i j
  simp [cT, hσ]

theorem cT_add {a b : Type} (M N : Matrix a b E) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  simp [cT]

theorem det_cT (Z : Matrix (Fin n) (Fin n) E) : (cT σ Z).det = σ Z.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

theorem TF_mul_strict (hA : IsStrict A) : TF r T * A = 0 ∧ cT σ A * TF r T = 0 := by
  constructor
  · ext i j
    by_cases h : i = Fin.last r <;> simp [TF, h, hA _ _ (Fin.le_last _)]
  · ext i j
    by_cases h : j = Fin.last r <;> simp [TF, cT, h, hA _ _ (Fin.le_last _)]

theorem det_gram_ne_zero (hZ : Z.det ≠ 0) (hG : Gq σ T T' Z ≠ 0) :
    (Matrix.fromBlocks (TF r T) Z (cT σ Z) (TF r T')).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  rw [← Sum.elim_comp_inl_inr v, Matrix.fromBlocks_mulVec] at e
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at e
  have e1 : TF r T *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 := funext fun i => congrFun e (Sum.inl i)
  have e2 : TF r T' *ᵥ (v ∘ Sum.inr) + cT σ Z *ᵥ (v ∘ Sum.inl) = 0 :=
    (add_comm _ _).trans (funext fun i => congrFun e (Sum.inr i))
  apply hv
  rw [← Sum.elim_comp_inl_inr v]
  generalize v ∘ Sum.inl = a at *
  generalize v ∘ Sum.inr = a' at *
  have d1 := Iota.det_mul_last e1
  have d2 := Iota.det_mul_last e2
  have c2 : SgAlg.lead (cT σ Z) r (Nat.le_succ r) = σ (SgAlg.lead Z r (Nat.le_succ r)) := by
    rw [SgAlg.lead, SgAlg.lead, ← det_cT]
    rfl
  rw [det_cT, c2] at d2
  have l1 : a (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination Z.det * d2 + T' * σ (SgAlg.lead Z r (Nat.le_succ r)) * d1)).resolve_left hG
  have l2 : a' (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination σ Z.det * d1 + T * SgAlg.lead Z r (Nat.le_succ r) * d2)).resolve_left hG
  have k (T : E) {x : Fin (r + 1) → E} (hx : x (Fin.last r) = 0) : TF r T *ᵥ x = 0 := by
    ext i
    by_cases hi : i = Fin.last r <;> simp [TF, Matrix.mulVec_diagonal, hi, hx]
  rw [k T l1, zero_add] at e1
  rw [k T' l2, zero_add] at e2
  rw [Matrix.eq_zero_of_mulVec_eq_zero hZ e1,
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_cT]; simpa using hZ) e2]
  simp

theorem mem_spanX_of_perp (hZ : Z.det ≠ 0) (hA : IsStrict A) (h : cT σ A * Z + Z * A' = 0)
    {x : Fin n → E} (hx : x ∈ perpX σ J P) {c c' : Fin (r + 1) → E}
    (e : TF r T *ᵥ c + Z *ᵥ c' = (cT σ P * J) *ᵥ x) :
    P *ᵥ (A *ᵥ c) + P' *ᵥ (A' *ᵥ c') ∈ spanX P := by
  have h1 : cT σ A *ᵥ ((cT σ P * J) *ᵥ x) = 0 := by
    ext i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    have k (a : Fin r) : ((cT σ P * J) *ᵥ x) a.castSucc = 0 := congrFun ((mem_perpX P x).1 hx) a
    simp only [k, mul_zero, Finset.sum_const_zero, zero_add]
    simp [cT, hA _ _ (Fin.le_last _)]
  have h2 : A' *ᵥ c' = 0 := by
    refine Matrix.eq_zero_of_mulVec_eq_zero hZ ?_
    rw [← e, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (TF_mul_strict hA).2,
      Matrix.zero_mulVec, zero_add, eq_neg_of_add_eq_zero_left h, Matrix.neg_mulVec, neg_eq_zero] at h1
    rwa [Matrix.mulVec_mulVec]
  rw [h2, Matrix.mulVec_zero, add_zero]
  refine ⟨fun a => (A *ᵥ c) a.castSucc, (Iota.eOf_mulVec P _).trans (congrArg _ ?_)⟩
  ext i
  induction i using Fin.lastCases
  · simp [Matrix.mulVec, dotProduct, hA _ _ (Fin.le_last _)]
  · simp

theorem exists_lieN (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hP : IsFrame σ J T P) (hP' : IsFrame σ J T' P')
    (eZ : Z = pairM σ J P' P) (hZ : Z.det ≠ 0) (hG : Gq σ T T' Z ≠ 0)
    (hA : IsStrict A) (hA' : IsStrict A') (h : cT σ A * Z + Z * A' = 0) :
    ∃ Y, LieN σ J P Y A ∧ LieN σ J P' Y A' := by
  have h' : cT σ A' * cT σ Z + cT σ Z * A = 0 := by
    have := congrArg (cT σ) h
    rw [cT_add, cT_mul, cT_mul, cT_cT hσ] at this
    exact (add_comm _ _).trans <| this.trans (by ext; simp [cT])
  have eZ' : cT σ Z = pairM σ J P P' := by
    rw [eZ, pairM, pairM, cT_mul, cT_mul, cT_cT hσ, hJ, Matrix.mul_assoc]
  set Q := Matrix.fromCols P P' with hQ
  set B := Matrix.fromBlocks A 0 0 A' with hB
  set Γ := Matrix.fromBlocks (TF r T) Z (cT σ Z) (TF r T') with hΓ
  have hu : IsUnit Γ.det := (det_gram_ne_zero hZ hG).isUnit
  have cQ : cT σ Q = Matrix.fromRows (cT σ P) (cT σ P') := by
    ext (i | i) j <;> rfl
  have cB : cT σ B = Matrix.fromBlocks (cT σ A) 0 0 (cT σ A') := by
    ext (i | i) (j | j) <;> simp [hB, cT]
  have g : cT σ Q * J * Q = Γ := by
    rw [cQ, Matrix.fromRows_mul, hQ, Matrix.fromRows_mul_fromCols, hΓ, eZ', eZ, ← hP.2, ← hP'.2]
    rfl
  have cΓ : cT σ Γ = Γ := by rw [← g, cT_mul, cT_mul, cT_cT hσ, hJ, Matrix.mul_assoc]
  have cΓi : cT σ Γ⁻¹ = Γ⁻¹ := by
    refine (Matrix.inv_eq_left_inv ?_).symm
    conv_lhs => enter [2]; rw [← cΓ]
    rw [← cT_mul, Matrix.mul_nonsing_inv _ hu]
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have sk : cT σ B * Γ + Γ * B = 0 := by
    rw [cB, hΓ, hB, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
    simp [TF_mul_strict hA (σ := σ), TF_mul_strict hA' (σ := σ), h, h']
  have sk' : Γ⁻¹ * cT σ B + B * Γ⁻¹ = 0 := by
    have := congrArg (fun M => Γ⁻¹ * M * Γ⁻¹) sk
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul] using this
  set Y := Q * B * Γ⁻¹ * (cT σ Q * J) with hY
  have y1 : cT σ Y * J + J * Y = 0 := by
    have := congrArg (fun M => J * Q * M * (cT σ Q * J)) sk'
    simp only [hY, cT_mul, cT_cT hσ, hJ, cΓi]
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul] using this
  have y2 : Matrix.fromCols (Y * P) (Y * P') = Matrix.fromCols (P * A) (P' * A') := by
    rw [← Matrix.mul_fromCols, ← hQ, hY, Matrix.mul_assoc, g, Matrix.nonsing_inv_mul_cancel_right _ _ hu, hQ, hB,
      Matrix.fromCols_mul_fromBlocks]
    simp
  have y3 (x : Fin n → E) : ∃ c c', Y *ᵥ x = P *ᵥ (A *ᵥ c) + P' *ᵥ (A' *ᵥ c') ∧
      TF r T *ᵥ c + Z *ᵥ c' = (cT σ P * J) *ᵥ x ∧ TF r T' *ᵥ c' + cT σ Z *ᵥ c = (cT σ P' * J) *ᵥ x := by
    obtain ⟨v, hv⟩ : ∃ v, v = Γ⁻¹ *ᵥ ((cT σ Q * J) *ᵥ x) := ⟨_, rfl⟩
    have e : Γ *ᵥ v = (cT σ Q * J) *ᵥ x := by
      rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    rw [hΓ, Matrix.fromBlocks_mulVec, cQ, Matrix.fromRows_mul, Matrix.fromRows_mulVec] at e
    refine ⟨v ∘ Sum.inl, v ∘ Sum.inr, ?_, funext fun i => congrFun e (Sum.inl i),
      (add_comm _ _).trans (funext fun i => congrFun e (Sum.inr i))⟩
    rw [hY, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hv, ← Matrix.mulVec_mulVec, hB,
      Matrix.fromBlocks_mulVec, hQ, Matrix.fromCols_mulVec_sumElim]
    simp
  obtain ⟨y4, y5⟩ := Matrix.fromCols_ext_iff .. |>.1 y2
  refine ⟨Y, ⟨y1, hA, y4, fun x hx => ?_⟩, y1, hA', y5, fun x hx => ?_⟩
  · obtain ⟨c, c', e1, e2, -⟩ := y3 x
    rw [e1]
    exact mem_spanX_of_perp hZ hA h hx e2
  · obtain ⟨c, c', e1, -, e2⟩ := y3 x
    rw [e1, add_comm]
    refine mem_spanX_of_perp (by rw [det_cT]; simpa using hZ) hA' ?_ hx e2
    exact h'

end Lie

section Generic

variable {σ : E →+* E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {T T' : E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {Z A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem simpleSum_single (a b : Fin (r + 1)) (x : E) :
    simpleSum (Matrix.single a b x) = if (b : ℕ) = a + 1 then x else 0 := by
  rw [simpleSum]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a, by have := b.2; omega⟩ : Fin r) _ (by simp)]
    · rw [Matrix.single_apply, if_pos ⟨rfl, Fin.ext h⟩]
    · intro k _ hk
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, -⟩
      exact hk rfl
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h rfl

theorem isStrict_single {m : ℕ} {a b : Fin m} (h : a < b) (x : E) : IsStrict (Matrix.single a b x) := by
  intro i j hij
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h.not_ge hij

variable [CharZero E]

theorem inversion_of_relevant (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hP : IsFrame σ J T P)
    (hP' : IsFrame σ J T' P') {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → E} (hd : ∀ a, d a ≠ 0)
    (eZ : Z = pairM σ J P' P) (hM : Z = Matrix.of fun a b => if a = w b then d b else 0) (hZ : Z.det ≠ 0)
    (hG : Gq σ T T' Z ≠ 0) (hR : Relevant σ J P P') {a b : Fin (r + 1)} (hab : a < b)
    (hw : (w a : ℕ) = w b + 1) : (b : ℕ) = a + 1 ∧ d a = -d b := by
  have key (c : E) : c * (d a + if (b : ℕ) = a + 1 then d b else 0) +
      σ (c * (d a + if (b : ℕ) = a + 1 then d b else 0)) = 0 := by
    obtain ⟨Y, h1, h2⟩ := exists_lieN hσ hJ hP hP' eZ hZ hG
      (isStrict_single (a := w b) (b := w a) (by rw [Fin.lt_def]; omega) (σ (-(c * d a))))
      (isStrict_single hab (c * d b)) (by
        have e : cT σ (Matrix.single (w b) (w a) (σ (-(c * d a)))) = Matrix.single (w a) (w b) (-(c * d a)) := by
          ext i j
          simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply, apply_ite σ, hσ, map_zero,
            and_comm]
        rw [e, hM]
        ext i j
        simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.of_apply, Matrix.zero_apply]
        rw [Finset.sum_eq_single (w b) (fun k _ hk => by simp [hk.symm]) (by simp),
          Finset.sum_eq_single a (fun k _ hk => by simp [hk.symm]) (by simp)]
        by_cases h1 : w a = i <;> by_cases h2 : b = j
        · subst h1 h2; simp; ring
        · simp [h2]
        · simp [h1, Ne.symm h1]
        · simp [h2])
    have := hR _ _ _ h1 h2
    rw [simpleSum_single, simpleSum_single, if_pos hw] at this
    split_ifs at this ⊢ <;> simp only [map_sub, map_neg, map_mul, map_add, map_zero, hσ] at this ⊢ <;>
      linear_combination -this
  have h0 : (d a + if (b : ℕ) = a + 1 then d b else 0) = 0 := by
    by_contra h
    have := key (d a + if (b : ℕ) = a + 1 then d b else 0)⁻¹
    rw [inv_mul_cancel₀ h, map_one] at this
    norm_num at this
  by_cases h : (b : ℕ) = a + 1
  · rw [if_pos h] at h0
    exact ⟨h, eq_neg_of_add_eq_zero_left h0⟩
  · rw [if_neg h, add_zero] at h0
    exact absurd h0 (hd a)

theorem exists_liesAt (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermU σ J) (hP : IsFrame σ J T P)
    (hP' : IsFrame σ J T' P') (eZ : Z = pairM σ J P' P) (hZ : Z.det ≠ 0) (hG : Gq σ T T' Z ≠ 0)
    (hR : Relevant σ J P P') : ∃ w, LiesAt w Z := by
  obtain ⟨l, u, w, d, hl, hu, hd, e⟩ := exists_lo_mono_up hZ
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun a b => if a = w b then d b else 0 with hM
  have hv : IsUp (cT σ l) := fun i j =>
    ⟨fun h => by simp [cT, (hl j i).1 h], fun h => by simp [cT, (hl j i).2 h.symm]⟩
  have e1 : cT σ (cT σ l)⁻¹ * l = 1 := by
    conv_lhs => enter [2]; rw [← cT_cT hσ l]
    rw [← cT_mul, up_mul_inv hv]
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have e2 : M = pairM σ J (P' * u⁻¹) (P * (cT σ l)⁻¹) := by
    rw [pairM_mul, ← eZ, e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc,
      up_mul_inv hu, Matrix.mul_one]
  have h1 : M.det ≠ 0 := fun h => hZ (by rw [e, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul])
  have h2 : Gq σ T T' M ≠ 0 := by rwa [e, Gq_mul T T' hl hu] at hG
  obtain ⟨p, hp⟩ := exists_point w (fun b => d b * (-1) ^ (r - (b : ℕ)))
    (fun a => mul_ne_zero (hd a) (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))) fun a b hab hw => by
      obtain ⟨k1, k2⟩ := inversion_of_relevant hσ hJ.1 (isFrame_mul hP (up_inv hv)) (isFrame_mul hP' (up_inv hu))
        hd e2 hM h1 h2 (hR.mul (up_inv hv) (up_inv hu)) hab hw
      refine ⟨k1, ?_⟩
      rw [k2, show r - (a : ℕ) = r - (b : ℕ) + 1 by have := b.2; omega, pow_succ]
      ring
  refine ⟨p, e ▸ LiesAt.mul ⟨1, 1, fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne,
    fun h => h ▸ Matrix.one_apply_eq _⟩, up_one, ?_⟩ hl hu⟩
  rw [hp, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp [eps, hM]

end Generic

section Signature

open scoped ComplexOrder

variable {n r p : ℕ}

theorem det_ne_zero_complex {J : Matrix (Fin n) (Fin n) ℂ} (hJ : cT (starRingEnd ℂ) J = J)
    (hs : Formalism.UG.HasSignature J p (r + 1)) {T T' : ℂ} (hT : 0 ≤ T) (hT' : 0 ≤ T')
    {P P' : Matrix (Fin n) (Fin (r + 1)) ℂ} (hP : IsFrame (starRingEnd ℂ) J T P)
    (hP' : IsFrame (starRingEnd ℂ) J T' P')
    (hG : Gq (starRingEnd ℂ) T T' (pairM (starRingEnd ℂ) J P' P) ≠ 0) :
    (pairM (starRingEnd ℂ) J P' P).det ≠ 0 := by
  intro h
  obtain ⟨a, ha, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  obtain ⟨ε, Q, hQ⟩ := hs
  let co : (Fin n → ℂ) →ₗ[ℂ] (Fin p ⊕ Fin (r + 1) → ℂ) :=
    (Q⁻¹ : GL _ ℂ).1.mulVecLin ∘ₗ LinearMap.funLeft ℂ ℂ ε.symm
  have hco (x : Fin n → ℂ) : x ∘ ε.symm = Q.1 *ᵥ co x := by
    change _ = Q.1 *ᵥ ((Q⁻¹ : GL _ ℂ).1 *ᵥ (x ∘ ε.symm))
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hq (x : Fin n → ℂ) : star x ⬝ᵥ J *ᵥ x = star (co x) ⬝ᵥ Formalism.UG.Jpq p (r + 1) *ᵥ co x := by
    rw [← hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hco, Matrix.dotProduct_mulVec (star (co x)),
      show Formalism.UG.cT (starRingEnd ℂ) Q.1 = Q.1ᴴ from rfl, ← Matrix.star_mulVec, ← hco, Matrix.reindex_apply,
      Matrix.submatrix_mulVec_equiv]
    rw [← comp_equiv_symm_dotProduct]
    congr 1
    · ext i; simp
    · congr 1; ext i; simp
  let f : ((Fin (r + 1) → ℂ) × ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    LinearMap.funLeft ℂ ℂ Sum.inr ∘ₗ co ∘ₗ (P.mulVecLin.coprod (LinearMap.toSpanSingleton ℂ _ (P' *ᵥ a)))
  obtain ⟨⟨c, t⟩, h0, hne⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) (by simp))
  obtain ⟨x, hx⟩ : ∃ x, x = P *ᵥ c + P' *ᵥ (t • a) := ⟨_, rfl⟩
  have h1 : co x ∘ Sum.inr = 0 := by rw [hx, Matrix.mulVec_smul]; exact h0
  have h2 : star x ⬝ᵥ J *ᵥ x = star (co x ∘ Sum.inl) ⬝ᵥ (co x ∘ Sum.inl) := by
    rw [hq, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec, h1]
    simp [dotProduct]
  have pr (A B : Matrix (Fin n) (Fin (r + 1)) ℂ) (y z : Fin (r + 1) → ℂ) :
      star (A *ᵥ y) ⬝ᵥ J *ᵥ (B *ᵥ z) = star y ⬝ᵥ pairM (starRingEnd ℂ) J B A *ᵥ z := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rfl
  have tf (S : ℂ) (hS : 0 ≤ S) (y : Fin (r + 1) → ℂ) : star y ⬝ᵥ TF r S *ᵥ y ≤ 0 := by
    have : star y ⬝ᵥ TF r S *ᵥ y = -(S * (star (y (Fin.last r)) * y (Fin.last r))) := by
      simp [TF, dotProduct, Matrix.mulVec_diagonal]
      ring
    rw [this, neg_nonpos]
    exact mul_nonneg hS (star_mul_self_nonneg _)
  have eZ : pairM (starRingEnd ℂ) J P P' = (pairM (starRingEnd ℂ) J P' P)ᴴ := by
    change _ = cT (starRingEnd ℂ) (pairM (starRingEnd ℂ) J P' P)
    rw [pairM, pairM, cT_mul, cT_mul, cT_cT (σ := starRingEnd ℂ) star_star, hJ, Matrix.mul_assoc]
  have h3 : star x ⬝ᵥ J *ᵥ x ≤ 0 := by
    rw [hx, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, pr, pr, pr, pr,
      hP.2, hP'.2, eZ, Matrix.dotProduct_mulVec _ _ᴴ, ← Matrix.star_mulVec, Matrix.mulVec_smul, e]
    simpa using add_nonpos (tf T hT c) (tf T' hT' (t • a))
  have h4 : co x ∘ Sum.inl = 0 :=
    dotProduct_star_self_eq_zero.1 (le_antisymm (h2 ▸ h3) (dotProduct_star_self_nonneg _))
  have h5 : x = 0 := by
    have := hco x
    rw [← Sum.elim_comp_inl_inr (co x), h1, h4, Sum.elim_zero_zero, Matrix.mulVec_zero] at this
    ext i
    simpa using congrFun this (ε i)
  obtain ⟨k1, k2⟩ := Iota.indep_of_Gq_ne_zero (σ := starRingEnd ℂ) star_star hJ ⟨hP, hP', rfl⟩ hG c (t • a)
    (hx.symm.trans h5)
  exact hne (Prod.ext k1 ((smul_eq_zero.1 k2).resolve_right ha))

variable {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {T T' : E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {τ : E →+* ℂ}

theorem pairM_map (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) :
    pairM (starRingEnd ℂ) (J.map τ) (P'.map τ) (P.map τ) = (pairM σ J P' P).map τ := by
  rw [pairM, pairM, Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hτ]

theorem isFrame_map (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (hP : IsFrame σ J T P) :
    IsFrame (starRingEnd ℂ) (J.map τ) (τ T) (P.map τ) := by
  obtain ⟨⟨L, hL⟩, h⟩ := hP
  refine ⟨⟨L.map τ, by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]⟩, ?_⟩
  rw [pairM_map hτ, h]
  ext i j
  simp [TF, Matrix.diagonal_apply, apply_ite τ]

theorem det_ne_zero_of_signature (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (hJ : cT σ J = J)
    (hs : Formalism.UG.HasSignature (J.map τ) p (r + 1)) (hT : 0 ≤ τ T) (hT' : 0 ≤ τ T') (hP : IsFrame σ J T P)
    (hP' : IsFrame σ J T' P') (hG : Gq σ T T' (pairM σ J P' P) ≠ 0) : (pairM σ J P' P).det ≠ 0 := by
  have h := det_ne_zero_complex (J := J.map τ) (by
    conv_rhs => rw [← hJ]
    ext i j
    simp [cT, hτ]) hs hT hT' (isFrame_map hτ hP) (isFrame_map hτ hP') (by
    rw [pairM_map hτ]
    refine fun h => hG ((map_eq_zero τ).1 (Eq.trans ?_ h))
    simp only [Gq, SgAlg.lead, map_sub, map_mul, hτ, RingHom.map_det τ]
    rfl)
  rw [pairM_map hτ] at h
  exact fun e => h ((RingHom.map_det τ _).symm.trans (by rw [e, map_zero]))

end Signature

section Record

open Formalism.BasicNotions
open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word}

theorem det_Zhat_ne_zero (t : RecTerm D u u') (hG : t.G ≠ 0) : t.Zhat.det ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hs := D.sp.Y_sig 0 τ
  rw [D.sp.baseSpace_signature_eq τ] at hs
  rw [Term.G, normOf_eq (isFrame_recFrame D u)] at hG
  exact det_ne_zero_of_signature (D.sp.cm.cmUnram.2.1 τ) (isHermU_gram _).1 hs (by simp) (by simp)
    (isFrame_recFrame D u) t.adm.1.1 hG

theorem at_ptOf_of_relevant (t : RecTerm D u u') (hR : t.relevant) (hG : t.G ≠ 0) : t.At t.ptOf := by
  have hZ := det_Zhat_ne_zero t hG
  rw [Term.G, normOf_eq (isFrame_recFrame D u)] at hG
  exact t.at_ptOf (exists_liesAt star_star (isHermU_gram _) (isFrame_recFrame D u) t.adm.1.1 rfl hZ hG hR)

end Record

end GlobalTheory.PtEx
