import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

open GlobalTheory.SgAlg Matrix Module

noncomputable section

namespace GlobalTheory.SgAlg.WittSplit

section Lin
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_not_mem_both (U U' : Submodule K V) (h : finrank K U = finrank K U') (hU : U ≠ ⊤) :
    ∃ v, v ∉ U ∧ v ∉ U' := by
  by_cases h1 : U ≤ U'
  · have hUU : U = U' := Submodule.eq_of_le_of_finrank_eq h1 h
    subst hUU
    obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
      by_contra hc; push_neg at hc; exact hU (eq_top_iff.2 fun x _ => hc x)
    exact ⟨v, hv, hv⟩
  by_cases h2 : U' ≤ U
  · exact absurd (Submodule.eq_of_le_of_finrank_eq h2 h.symm ▸ le_rfl) h1
  obtain ⟨x, hxU, hxU'⟩ := SetLike.not_le_iff_exists.1 h1
  obtain ⟨y, hyU', hyU⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨x + y, fun hm => hyU ?_, fun hm => hxU' ?_⟩
  · simpa using U.sub_mem hm hxU
  · simpa using U'.sub_mem hm hyU'

theorem finrank_sup_singleton (U : Submodule K V) {v : V} (hv : v ∉ U) :
    finrank K (U ⊔ K ∙ v : Submodule K V) = finrank K U + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ U.zero_mem)
  have e := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ v)
  rw [(Submodule.disjoint_span_singleton_of_notMem hv).eq_bot, finrank_bot,
    finrank_span_singleton hv0] at e
  omega

theorem exists_common_compl : ∀ (d : ℕ) (U U' : Submodule K V), finrank K V - finrank K U = d →
    finrank K U = finrank K U' → ∃ S : Submodule K V, IsCompl U S ∧ IsCompl U' S := by
  intro d
  induction d with
  | zero =>
    intro U U' hd h
    have hU : U = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le U) (by omega))
    have hU' : U' = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le U') (by have := Submodule.finrank_le U; omega))
    exact ⟨⊥, hU ▸ isCompl_top_bot, hU' ▸ isCompl_top_bot⟩
  | succ d ih =>
    intro U U' hd h
    have hU : U ≠ ⊤ := by
      rintro rfl; simp [finrank_top] at hd
    obtain ⟨v, hv, hv'⟩ := exists_not_mem_both U U' h hU
    obtain ⟨S1, hS1, hS1'⟩ := ih (U ⊔ K ∙ v) (U' ⊔ K ∙ v)
      (by rw [finrank_sup_singleton U hv]; omega)
      (by rw [finrank_sup_singleton U hv, finrank_sup_singleton U' hv', h])
    refine ⟨(K ∙ v) ⊔ S1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (Submodule.disjoint_span_singleton_of_notMem hv).disjoint_sup_right_of_disjoint_sup_left
        hS1.disjoint
    · rw [codisjoint_iff, ← sup_assoc]; exact codisjoint_iff.1 hS1.codisjoint
    · exact (Submodule.disjoint_span_singleton_of_notMem hv').disjoint_sup_right_of_disjoint_sup_left
        hS1'.disjoint
    · rw [codisjoint_iff, ← sup_assoc]; exact codisjoint_iff.1 hS1'.codisjoint

end Lin

section Mat
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem inj_of_left (u : Matrix m k F) (h : ∃ L : Matrix k m F, L * u = 1) :
    Function.Injective (Matrix.toLin' u) := by
  obtain ⟨L, hL⟩ := h
  intro x y hxy
  simp only [Matrix.toLin'_apply] at hxy
  have := congrArg (L *ᵥ ·) hxy
  simpa [Matrix.mulVec_mulVec, hL] using this

theorem mat_eq_of_mulVec {p q : Type} [Fintype q] [DecidableEq q] (M N : Matrix p q F)
    (h : ∀ c, M *ᵥ c = N *ᵥ c) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using h c)

theorem exists_left_inv_unit (u u' : Matrix m k F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) : ∃ L : Matrix k m F, L * u = 1 ∧ IsUnit (L * u').det := by
  have i := inj_of_left u hu
  have i' := inj_of_left u' hu'
  have hf : finrank F (LinearMap.range (Matrix.toLin' u)) = finrank F (LinearMap.range (Matrix.toLin' u')) := by
    rw [LinearMap.finrank_range_of_inj i, LinearMap.finrank_range_of_inj i']
  obtain ⟨S, hS, hS'⟩ := exists_common_compl _ _ _ rfl hf
  let e := LinearEquiv.ofInjective (Matrix.toLin' u) i
  let L0 : (m → F) →ₗ[F] (k → F) := e.symm.toLinearMap ∘ₗ Submodule.projectionOnto _ _ hS
  have hL0 : ∀ c, L0 (u *ᵥ c) = c := by
    intro c
    have hm : u *ᵥ c ∈ LinearMap.range (Matrix.toLin' u) := ⟨c, rfl⟩
    simp only [L0, LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_left hS ⟨_, hm⟩]
    exact e.symm_apply_eq.2 (Subtype.ext (by simp [e]))
  refine ⟨LinearMap.toMatrix' L0, ?_, ?_⟩
  · exact mat_eq_of_mulVec _ _ fun c => by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hL0, Matrix.one_mulVec]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    simp only [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hxy
    have h0 : L0 (u' *ᵥ (x - y)) = 0 := by rw [Matrix.mulVec_sub, map_sub, hxy, sub_self]
    simp only [L0, LinearMap.comp_apply, LinearEquiv.coe_coe, map_eq_zero_iff _ e.symm.injective] at h0
    have hS0 := (Submodule.projectionOnto_apply_eq_zero_iff hS).1 h0
    have hU0 : u' *ᵥ (x - y) ∈ LinearMap.range (Matrix.toLin' u') := ⟨x - y, rfl⟩
    have hz : u' *ᵥ (x - y) = 0 := (Submodule.disjoint_def.1 hS'.disjoint) _ hU0 hS0
    have : x - y = 0 := i' (by simpa [Matrix.toLin'_apply] using hz)
    exact sub_eq_zero.1 this

theorem exists_right_inv_unit (φ φ' : Matrix k m F) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) : ∃ ψ : Matrix m k F, φ' * ψ = 1 ∧ IsUnit (φ * ψ).det := by
  obtain ⟨ψ1, h1⟩ := hφ
  obtain ⟨ψ2, h2⟩ := hφ'
  obtain ⟨L, hL, hLu⟩ := exists_left_inv_unit φ'ᵀ φᵀ ⟨ψ2ᵀ, by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]⟩
    ⟨ψ1ᵀ, by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]⟩
  refine ⟨Lᵀ, ?_, ?_⟩
  · rw [← Matrix.transpose_transpose φ', ← Matrix.transpose_mul, hL, Matrix.transpose_one]
  · rw [← Matrix.transpose_transpose φ, ← Matrix.transpose_mul, Matrix.det_transpose]; exact hLu

theorem core (u u' : Matrix m k F) (φ φ' : Matrix k m F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) (h : φ * u = φ' * u') :
    ∃ A : Matrix m m F, IsUnit A.det ∧ A * u = u' ∧ φ' * A = φ := by
  obtain ⟨L, hL, hLu'⟩ := exists_left_inv_unit u u' hu hu'
  set B : Matrix m m F := 1 + (u' - u) * L with hBdef
  have hBu : B * u = u' := by
    rw [hBdef, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hL, Matrix.mul_one]; abel
  have hB : IsUnit B.det := by
    have : B.det = (L * u').det := by
      rw [hBdef, Matrix.det_one_add_mul_comm]; congr 1; rw [Matrix.mul_sub, hL]; abel
    rw [this]; exact hLu'
  clear_value B
  obtain ⟨ψ0, hψ0⟩ := hφ
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hφ1 : ∃ ψ : Matrix m k F, φ * B⁻¹ * ψ = 1 := ⟨B * ψ0, by rw [Matrix.mul_assoc φ, ← Matrix.mul_assoc B⁻¹, hBB, Matrix.one_mul, hψ0]⟩
  obtain ⟨ψ, hψ, hψu⟩ := exists_right_inv_unit (φ * B⁻¹) φ' hφ1 hφ'
  have h1u' : φ * B⁻¹ * u' = φ' * u' := by
    conv_lhs => rw [← hBu]
    rw [show φ * B⁻¹ * (B * u) = φ * (B⁻¹ * B) * u by simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, h]
  refine ⟨(1 + ψ * (φ * B⁻¹ - φ')) * B, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hB
    rw [Matrix.det_one_add_mul_comm]
    have : 1 + (φ * B⁻¹ - φ') * ψ = φ * B⁻¹ * ψ := by rw [Matrix.sub_mul, hψ]; abel
    rw [this]; exact hψu
  · rw [Matrix.mul_assoc, hBu, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.sub_mul, h1u',
      sub_self, Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hψ, Matrix.one_mul,
      add_sub_cancel, Matrix.mul_assoc, hBB, Matrix.mul_one]

end Mat

section Ring
variable {E : Type} [CommRing E] (σ : E →+* E)

theorem cT_mul {p q r : Type} [Fintype q] (A : Matrix p q E) (B : Matrix q r E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT; rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add {p q : Type} (A B : Matrix p q E) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]

theorem cT_smul {p q : Type} (c : E) (A : Matrix p q E) : cT σ (c • A) = σ c • cT σ A := by
  ext i j; simp [cT]

theorem cT_one {p : Type} [DecidableEq p] : cT σ (1 : Matrix p p E) = 1 := by
  unfold cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {p q : Type} (A : Matrix p q E) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hσ]

theorem witt_of_field {F : Type} [Field F] (hσ : ∀ x, σ (σ x) = x) (e : E) (he2 : e * e = e)
    (he1 : e + σ e = 1) (π : E →+* F) (s : F → E) (hs1 : ∀ f, π (s f) = f)
    (hs2 : ∀ x, s (π x) = e * x) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) (Fin a) E) (hX : Free X) (hX' : Free X')
    (hG : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  have hee' : e * σ e = 0 := by linear_combination e * he1 - he2
  have he'e : σ e * e = 0 := by rw [mul_comm]; exact hee'

  have K1 : ∀ {p q : Type} (P : Matrix p q E), (P.map π).map s = e • P := by
    intro p q P; ext i j; simp [hs2]
  have K2 : ∀ {p q : Type} (P : Matrix p q F), (P.map s).map π = P := by
    intro p q P; ext i j; simp [hs1]
  have K3 : ∀ {p q : Type} (P : Matrix p q F), e • P.map s = P.map s := by
    intro p q P; ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    have := hs2 (s (P i j)); rw [hs1] at this; exact this.symm
  have T : ∀ {p q : Type} (P Q : Matrix p q E), P.map π = Q.map π → e • P = e • Q := by
    intro p q P Q h; rw [← K1, ← K1, h]

  obtain ⟨L, hL⟩ := hX
  obtain ⟨L', hL'⟩ := hX'
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ.2
  set M := J.map π with hMdef
  have hM : IsUnit M.det := by
    have h := hJ.2.map π; rw [RingHom.map_det] at h; exact h
  have hright : ∀ (Y : Matrix (Fin n) (Fin a) E) (LY : Matrix (Fin a) (Fin n) E), LY * Y = 1 →
      (cT σ Y * J) * (J⁻¹ * cT σ LY) = 1 := by
    intro Y LY h
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, ← cT_mul, h, cT_one]
  obtain ⟨A, hA, hAu, hφA⟩ := core (X.map π) (X'.map π) ((cT σ X * J).map π) ((cT σ X' * J).map π)
    ⟨L.map π, by rw [← Matrix.map_mul, hL, Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨L'.map π, by rw [← Matrix.map_mul, hL', Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨(J⁻¹ * cT σ L).map π, by rw [← Matrix.map_mul, hright X L hL, Matrix.map_one π (map_zero π) (map_one π)]⟩
    ⟨(J⁻¹ * cT σ L').map π, by rw [← Matrix.map_mul, hright X' L' hL', Matrix.map_one π (map_zero π) (map_one π)]⟩
    (by rw [← Matrix.map_mul, ← Matrix.map_mul]; unfold pairM at hG; rw [hG])
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hMM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hMM' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  set C : Matrix (Fin n) (Fin n) F := M * A⁻¹ * M⁻¹ with hCdef
  set Ah := A.map s
  set Ch := C.map s
  have hAh : e • Ah = Ah := K3 A
  have hCh : e • Ch = Ch := K3 C

  have F1 : Ch * J * Ah = e • J := by
    have : e • (Ch * J * Ah) = e • J := T _ _ (by
      rw [Matrix.map_mul, Matrix.map_mul, K2, K2, ← hMdef, hCdef]
      rw [show M * A⁻¹ * M⁻¹ * M * A = M * A⁻¹ * (M⁻¹ * M) * A by simp only [Matrix.mul_assoc],
        hMM, Matrix.mul_one, Matrix.mul_assoc, hAA, Matrix.mul_one])
    rw [← this, ← hCh, Matrix.smul_mul, Matrix.smul_mul, smul_smul, he2]

  have F2 : cT σ X * Ch = e • cT σ X' := by
    have : e • (cT σ X * Ch) = e • cT σ X' := T _ _ (by
      rw [Matrix.map_mul, K2, hCdef]
      have h3 : (cT σ X).map π * M = ((cT σ X' * J).map π) * A := by
        rw [hφA, Matrix.map_mul]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.map_mul, ← hMdef,
        show (cT σ X').map π * M * A * A⁻¹ * M⁻¹ = (cT σ X').map π * (M * (A * A⁻¹) * M⁻¹) by
          simp only [Matrix.mul_assoc],
        Matrix.mul_nonsing_inv A hA, Matrix.mul_one, hMM', Matrix.mul_one])
    calc cT σ X * Ch = e • (cT σ X * Ch) := by rw [← Matrix.mul_smul, hCh]
      _ = e • cT σ X' := this
  have F3 : Ah * X = e • X' := by
    rw [← T (Ah * X) X' (by rw [Matrix.map_mul, K2, hAu]), ← Matrix.smul_mul, hAh]
  refine ⟨Ah + cT σ Ch, ?_, ?_⟩
  · unfold IsUn
    have hJc : cT σ J = J := hJ.1
    rw [cT_add, cT_cT σ hσ, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    have z1 : cT σ Ah * J * Ah = 0 := by
      rw [← hAh, cT_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he'e, zero_smul]
    have z2 : Ch * J * cT σ Ch = 0 := by
      rw [← hCh, cT_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee', zero_smul]
    have z3 : cT σ Ah * J * cT σ Ch = σ e • J := by
      have h4 : cT σ (Ch * J * Ah) = cT σ Ah * J * cT σ Ch := by
        rw [cT_mul, cT_mul, hJc, ← Matrix.mul_assoc]
      rw [← h4, F1, cT_smul, hJc]
    rw [z1, z2, z3, F1, zero_add, add_zero, ← add_smul, add_comm, he1, one_smul]
  · rw [Matrix.add_mul, F3]
    have : cT σ Ch * X = σ e • X' := by
      rw [← cT_cT σ hσ X, ← cT_mul, F2, cT_smul, cT_cT σ hσ]
    rw [this, ← add_smul, he1, one_smul]

end Ring

theorem witt_split : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ →
    (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) →
    ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J →
    ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' →
    ∃ g, IsUn σ J g ∧ g * X = X' := by
  intro E _ σ hQA hsplit n a J hJ X X' hX hX' hG
  obtain ⟨e, he2, he1, hef⟩ := hsplit
  have hee' : e * σ e = 0 := by linear_combination e * he1 - he2
  set I : Ideal E := Ideal.span {σ e} with hIdef
  have hmemI : ∀ z, z * σ e ∈ I := fun z => Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hmax : I.IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    refine ⟨⟨0, 1, ?_⟩, fun x y => mul_comm x y, ?_⟩
    · intro h
      have h1 : (1 : E) ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
      have he0 : e = 0 := by linear_combination -e * hc + c * hee'
      have h01 : (0 : E) = 1 := by rw [← he1, he0, map_zero, add_zero]
      obtain ⟨z, hz⟩ := hQA.2.1
      haveI := subsingleton_of_zero_eq_one h01
      exact hz (Subsingleton.elim _ _)
    · intro x hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hex : e * x ≠ 0 := by
        intro h0; apply hx; rw [Ideal.Quotient.eq_zero_iff_mem]
        have : x = x * σ e := by linear_combination h0 - x * he1
        rw [this]; exact hmemI x
      obtain ⟨y, hy⟩ := hef x hex
      refine ⟨Ideal.Quotient.mk I y, ?_⟩
      rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      have : x * y - 1 = (x * y - 1) * σ e := by linear_combination hy - (x * y - 1) * he1
      rw [this]; exact hmemI _
  letI : Field (E ⧸ I) := Ideal.Quotient.field I
  have hpe : Ideal.Quotient.mk I e = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have : e - 1 = (-1) * σ e := by linear_combination he1
    rw [this]; exact hmemI _
  let s : E ⧸ I → E := fun f => e * (Ideal.Quotient.mk_surjective f).choose
  have hs1 : ∀ f, Ideal.Quotient.mk I (s f) = f := by
    intro f; simp only [s, map_mul, hpe, one_mul]; exact (Ideal.Quotient.mk_surjective f).choose_spec
  have hs2 : ∀ x, s (Ideal.Quotient.mk I x) = e * x := by
    intro x
    have hc := (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I x)).choose_spec
    set y := (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I x)).choose
    rw [Ideal.Quotient.eq] at hc
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hc
    show e * y = e * x
    linear_combination e * hc'.symm + c * hee'
  exact witt_of_field σ hQA.1 e he2 he1 (Ideal.Quotient.mk I) s hs1 hs2 J hJ X X' hX hX' hG

end GlobalTheory.SgAlg.WittSplit
