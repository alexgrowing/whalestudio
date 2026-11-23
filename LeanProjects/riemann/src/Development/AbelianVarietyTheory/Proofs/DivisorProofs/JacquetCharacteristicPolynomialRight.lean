import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.ScalRight

section Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_scalar_gl {n : Type} [Fintype n] [DecidableEq n] (x : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar n x) = x ^ Fintype.card n := by
  ext
  simp [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]

theorem scalar_mem_parab {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (x : kˣ) : GeneralLinearGroup.scalar n x ∈ parab k e := by
  rw [mem_parab_iff]
  intro a b i j hab
  have hne : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h => hab.ne' (congrArg Sigma.fst (e.injective h))
  simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hne]

theorem leviProj_eq_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (x : kˣ) (p : parab k e) (hp : (p : GL n k) = GeneralLinearGroup.scalar n x) :
    leviProj k e p = fun a => GeneralLinearGroup.scalar (m a) x := by
  funext a
  ext i j
  rw [leviProj_apply, hp]
  by_cases h : i = j
  · subst h; simp [Matrix.scalar_apply]
  · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h' => h (by simpa using e.injective h')
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ h]

variable {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem relInd_eq_smul (f : ∀ i, (Σ j, c i j) ≃ m i) (σ : Representation ℂ (∀ i, Levi k (c i)) W)
    (z : Levi k m) (hz : z ∈ relParab k f) (hc : ∀ x, x * z = z * x) (a : ℂ)
    (ha : ((relDeltaHalf k c (relProj k f ⟨z, hz⟩) : ℂˣ) : ℂ) • σ (relProj k f ⟨z, hz⟩) = a • LinearMap.id) :
    relInd f σ z = a • LinearMap.id := by
  refine LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))
  show F.1.1 (x * z) = a • F.1.1 x
  rw [hc x]
  have h1 := F.1.2 ⟨z, hz⟩ x
  refine h1.trans ?_
  exact LinearMap.congr_fun ha (F.1.1 x)

theorem relJac_eq_smul (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (y : ∀ i, Levi k (c i)) (a : ℂ) (ha : ρ (relEmb k f y) = a • LinearMap.id) :
    relJac f ρ y = ((((relDeltaHalf k c y)⁻¹ : ℂˣ) : ℂ) * a) • LinearMap.id := by
  refine LinearMap.ext fun q => Submodule.Quotient.induction_on _ q fun v => ?_
  rw [relJac_mk, ha]
  simp [mul_smul, Submodule.Quotient.mk_smul]

end Gen

theorem extTensor_detRep_eq {k : Type} [Field k] {u v : ℕ} (χ₁ χ₂ : kˣ →* ℂˣ)
    (h : GL (Fin u) k × GL (Fin v) k) :
    extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂) h =
      ((χ₁ (GeneralLinearGroup.det h.1) : ℂ) * (χ₂ (GeneralLinearGroup.det h.2) : ℂ)) • LinearMap.id := by
  refine TensorProduct.ext' fun x y => ?_
  rw [extTensor_tmul]
  simp only [detRep, ofChar_apply, detChar_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [← smul_eq_mul, ← smul_eq_mul (a := (χ₂ _ : ℂ)), TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', smul_smul, mul_comm]

theorem modExp_bool_true (n : Bool → ℕ) : modExp (fun j : Bool => Fin (n j)) true = -(n false : ℤ) := by
  simp [modExp, Finset.sum_filter, Fintype.sum_bool]

theorem modExp_bool_false (n : Bool → ℕ) : modExp (fun j : Bool => Fin (n j)) false = (n true : ℤ) := by
  simp [modExp, Finset.sum_filter, Fintype.sum_bool]

theorem absPow_zero_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : absPow k 0 x = 1 := by
  ext
  simp [val_absPow]

theorem cell_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (ϖ : kˣ) (B : SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin u) (Fin v) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two m (Fin 1) j), cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) = (if B.1 false true = 1 then (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) else (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) • LinearMap.id := by
  intro k _ _ _ _ χ₁ χ₂ u v m _ _ ϖ B f g
  let s : Bool → kˣ := fun j => cond j ϖ 1
  have hZ : ∀ j, (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) j =
      GeneralLinearGroup.scalar (Two m (Fin 1) j) (s j) := by
    intro j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar (n := m) (R := k))).symm
    · rfl
  have hmem : leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) ∈ relParab k g := by
    intro j _
    rw [hZ j]
    exact scalar_mem_parab _ _
  have hc : ∀ x : Levi k (Two m (Fin 1)), x * leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) =
      leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) * x := by
    intro x
    funext j
    rw [Pi.mul_apply, Pi.mul_apply, hZ j]
    exact (GeneralLinearGroup.scalar_commute _ _).symm
  have hP : relProj k g ⟨_, hmem⟩ = fun j i => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j) := by
    funext j
    exact leviProj_eq_scalar (g j) (s j) _ (hZ j)
  refine relInd_eq_smul g _ _ hmem hc _ ?_
  rw [hP]
  have hdet : ∀ i, GeneralLinearGroup.det (relEmb k f (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j)) i) =
      ϖ ^ B.1 i true := by
    intro i
    rw [relEmb_apply, det_leviEmb, Fintype.prod_bool]
    show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (B.1 i true)) ϖ) *
      GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (B.1 i false)) 1) = _
    rw [det_scalar_gl, det_scalar_gl, one_pow, mul_one, Fintype.card_fin]
  have hJ := relJac_eq_smul (k := k) f ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)
    (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j))
    ((χ₁ (ϖ ^ B.1 false true) : ℂ) * (χ₂ (ϖ ^ B.1 true true) : ℂ))
    (by
      rw [MonoidHom.comp_apply, extTensor_detRep_eq]
      show ((χ₁ (GeneralLinearGroup.det (relEmb k f _ false)) : ℂ) *
        (χ₂ (GeneralLinearGroup.det (relEmb k f _ true)) : ℂ)) • LinearMap.id = _
      rw [hdet, hdet])
  show _ • relJac f _ (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j)) = _
  rw [hJ, smul_smul]
  congr 1
  clear hJ hP hc hmem hZ hdet
  simp only [relDeltaHalf_apply, deltaHalf_apply, det_scalar_gl, Fintype.card_fin, Fintype.prod_bool]
  simp only [s, cond_true, cond_false, one_pow, map_one, modExp_bool_true, modExp_bool_false, one_mul, mul_one]
  have hcol : B.1 false true + B.1 true true = 1 := by
    have := B.2.2 true
    simpa [Fintype.sum_bool, add_comm] using this
  have hu : B.1 false false + B.1 false true = u := by
    have := B.2.1 false
    simpa [Fintype.sum_bool, add_comm] using this
  have hv : B.1 true false + B.1 true true = v := by
    have := B.2.1 true
    simpa [Fintype.sum_bool, add_comm] using this
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ : (B.1 false true = 1 ∧ B.1 true true = 0) ∨ (B.1 false true = 0 ∧ B.1 true true = 1) := by
    omega
  · rw [if_pos h1]
    rw [h1, h2]
    have hu' : ((u : ℂ) - 1) = (B.1 false false : ℂ) := by
      have e : (u : ℂ) = (B.1 false false : ℂ) + 1 := by exact_mod_cast (by omega : u = B.1 false false + 1)
      rw [e]; ring
    simp only [pow_zero, pow_one, map_one, one_mul, mul_one, Nat.cast_zero, Int.cast_zero, neg_zero, zero_div,
      absPow_zero_apply, Units.val_one, inv_one]
    rw [hu']
    push_cast
    simp only [Units.val_mul, MonoidHom.mul_apply, Units.val_inv_eq_inv_val, val_absPow, neg_div, Complex.cpow_neg, inv_inv]
    ring
  · rw [if_neg (by omega)]
    rw [h1, h2]
    have hv' : ((v : ℂ) - 1) = (B.1 true false : ℂ) := by
      have e : (v : ℂ) = (B.1 true false : ℂ) + 1 := by exact_mod_cast (by omega : v = B.1 true false + 1)
      rw [e]; ring
    simp only [pow_zero, pow_one, map_one, one_mul, mul_one, Nat.cast_zero, Int.cast_zero, neg_zero, zero_div,
      absPow_zero_apply, Units.val_one, inv_one]
    rw [hv']
    push_cast
    simp only [Units.val_mul, MonoidHom.mul_apply, Units.val_inv_eq_inv_val, val_absPow, neg_div, Complex.cpow_neg, inv_inv]
    ring

theorem aeval_prod_eq_zero_of_filtration {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (z : G) (N : ℕ) (S : Fin (N + 1) → Subrepresentation σ)
    (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (c : Fin N → ℂ)
    (hc : ∀ t : Fin N, ∀ x ∈ (S t.succ).toSubmodule, σ z x - c t • x ∈ (S t.castSucc).toSubmodule) :
    Polynomial.aeval (σ z) (∏ t, (Polynomial.X - Polynomial.C (c t))) = 0 := by
  let c' : ℕ → ℂ := fun t => if h : t < N then c ⟨t, h⟩ else 0
  have key : ∀ n (hn : n ≤ N), ∀ x ∈ (S ⟨n, Nat.lt_succ_of_le hn⟩).toSubmodule,
      Polynomial.aeval (σ z) (∏ t ∈ Finset.range n, (Polynomial.X - Polynomial.C (c' t))) x = 0 := by
    intro n
    induction n with
    | zero =>
      intro hn x hx
      have h0' : S ⟨0, Nat.lt_succ_of_le hn⟩ = ⊥ := h0
      rw [h0'] at hx
      have hx0 : x = 0 := hx
      simp [hx0]
    | succ n ih =>
      intro hn x hx
      rw [Finset.prod_range_succ, map_mul, Module.End.mul_apply]
      apply ih (by omega)
      have h1 := hc ⟨n, by omega⟩ x hx
      have h2 : c' n = c ⟨n, by omega⟩ := dif_pos (by omega)
      simpa [h2, sub_smul] using h1
  have h1 : ∏ t, (Polynomial.X - Polynomial.C (c t)) =
      ∏ t ∈ Finset.range N, (Polynomial.X - Polynomial.C (c' t)) := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [c', t.2]
  rw [h1]
  refine LinearMap.ext fun x => ?_
  refine key N le_rfl x ?_
  have : S ⟨N, Nat.lt_succ_of_le le_rfl⟩ = ⊤ := hN
  rw [this]
  trivial

theorem sub_smul_mem_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G V} {τ : Representation ℂ G W} (S T : Subrepresentation σ)
    (φ : (subQuot S T).Equiv τ) (z : G) (c : ℂ) (hz : τ z = c • LinearMap.id) (x : V)
    (hx : x ∈ S.toSubmodule) : σ z x - c • x ∈ T.toSubmodule := by
  let q : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype := Submodule.Quotient.mk ⟨x, hx⟩
  have h1 := φ.toIntertwiningMap.isIntertwining _ _ z q
  rw [hz] at h1
  have h2 : subQuot S T z q = c • q := by
    apply φ.toLinearEquiv.injective
    refine h1.trans ?_
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact (map_smul φ.toLinearEquiv _ q).symm
  rw [← sub_eq_zero] at h2
  have h3 : subQuot S T z q - c • q =
      Submodule.Quotient.mk (⟨σ z x, S.apply_mem_toSubmodule z hx⟩ - c • ⟨x, hx⟩) := rfl
  rw [h3, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

set_option maxHeartbeats 4000000 in

theorem scal_right : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (e : m ⊕ Fin 1 ≃ Fin (u + v)) (ϖ : kˣ), Polynomial.aeval (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) ((Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) * (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ))) = 0 := by
  intro k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v m _ _ e ϖ
  have hcont : Continuous ((leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have hρ' : IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) := isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hcont
  have hJ : JacquetOfInducedFiltration k := hG k
  obtain ⟨N, b, hb⟩ := hJ Bool Bool (Fin (u + v)) (Two (Fin u) (Fin v)) (Two m (Fin 1))
    (two (stdSum (rfl : u + v = u + v))) (two e)
  have hb' := hb (TensorProduct ℂ ℂ ℂ) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) hρ'
  have h0 := hb'.choose_spec.2.1
  have hN := hb'.choose_spec.2.2.1
  have hS := hb'.choose_spec.2.2.2
  let cv : SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)) → ℂ := fun B =>
    if B.1 false true = 1 then (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
    else (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
  have hfil := aeval_prod_eq_zero_of_filtration _ (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) N hb'.choose h0 hN (fun t => cv (b t))
    (fun t x hx => sub_smul_mem_of_equiv _ _
      (hS t (b t).nonempty_rows.some (b t).nonempty_cols.some).some (leviTwo k m (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) (cv (b t))
      (cell_scalar χ₁ χ₂ u v m ϖ (b t) _ _) x hx)
  haveI := Fintype.ofFinite (SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)))
  rw [show (∏ t, (Polynomial.X - Polynomial.C (cv (b t)))) =
      ∏ B, (Polynomial.X - Polynomial.C (cv B)) from
    Equiv.prod_comp b (fun B => Polynomial.X - Polynomial.C (cv B))] at hfil
  let φB : SizeMatrix (Two (Fin u) (Fin v)) (Two m (Fin 1)) → Bool := fun B => decide (B.1 false true = 1)
  let fB : Bool → Polynomial ℂ := fun x => Polynomial.X - Polynomial.C
    (if x then (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)
      else (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ))
  have hinj : Function.Injective φB := by
    intro B B' hBB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c1 := B.2.2 true
    have r0' := B'.2.1 false
    have r1' := B'.2.1 true
    have c1' := B'.2.2 true
    simp only [Fintype.sum_bool] at r0 r1 c1 r0' r1' c1'
    have hu : Fintype.card (Two (Fin u) (Fin v) false) = u := Fintype.card_fin u
    have hv : Fintype.card (Two (Fin u) (Fin v) true) = v := Fintype.card_fin v
    have h1 : Fintype.card (Two m (Fin 1) true) = 1 := Fintype.card_fin 1
    rw [hu] at r0 r0'
    rw [hv] at r1 r1'
    rw [h1] at c1 c1'
    have hd : (B.1 false true = 1) ↔ (B'.1 false true = 1) := by simpa [φB] using hBB
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> omega
  have hdvd : (∏ B, (Polynomial.X - Polynomial.C (cv B))) ∣
      (Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) := by
    have e1 : (∏ B, (Polynomial.X - Polynomial.C (cv B))) = ∏ x ∈ Finset.univ.image φB, fB x := by
      rw [Finset.prod_image fun B _ B' _ h => hinj h]
      refine Finset.prod_congr rfl fun B _ => ?_
      by_cases h : B.1 false true = 1 <;> simp [cv, fB, φB, h]
    have e2 : (Polynomial.X - Polynomial.C (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) *
        (Polynomial.X - Polynomial.C (((χ₂ * absPow k (((v : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ)) =
          ∏ x, fB x := by
      rw [Fintype.prod_bool]
      simp only [fB, if_true, Bool.false_eq_true, if_false]
    rw [e1, e2]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
  obtain ⟨r, hr⟩ := hdvd
  rw [hr, map_mul]
  exact mul_eq_zero_of_left hfil _

end GlobalTheory.ScalRight
