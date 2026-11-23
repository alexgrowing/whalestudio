import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.SchrodingerApplyZeroOfFst

noncomputable section

namespace PositivityTheory.ThKF0.Chr

open Matrix GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ κ₁ : Type}

def dv (w w' : V R κ) : V R (κ ⊕ κ) := (Sum.elim w.1 w'.1, Sum.elim w.2 (-w'.2))

def dE (R κ : Type) [CommRing R] : (V R κ × V R κ) ≃ₗ[R] V R (κ ⊕ κ) where
  toFun p := dv p.1 p.2
  invFun u := ((u.1 ∘ Sum.inl, u.2 ∘ Sum.inl), (u.1 ∘ Sum.inr, -(u.2 ∘ Sum.inr)))
  map_add' p q := by ext (k | k) <;> simp [dv, add_comm]
  map_smul' a p := by ext (k | k) <;> simp [dv]
  left_inv p := by ext k <;> simp [dv]
  right_inv u := by ext (k | k) <;> simp [dv]

theorem exists_dv (u : V R (κ ⊕ κ)) : ∃ w w', u = dv w w' := ⟨_, _, ((dE R κ).apply_symm_apply u).symm⟩

def dbS (S : V R κ ≃ₗ[R] V R κ) : V R (κ ⊕ κ) ≃ₗ[R] V R (κ ⊕ κ) := (dE R κ).symm ≪≫ₗ S.prodCongr S ≪≫ₗ dE R κ

theorem dbS_dv (S : V R κ ≃ₗ[R] V R κ) (w w' : V R κ) : dbS S (dv w w') = dv (S w) (S w') := by
  show dE R κ (S.prodCongr S ((dE R κ).symm (dE R κ (w, w')))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

theorem rel_dv {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) {w w' : V R κ} {w₁ w₁' : V R κ₁} :
    Rel (dbS S) (Sum.map j j) (dv w w') (dv w₁ w₁') ↔ Rel S j w w₁ ∧ Rel S j w' w₁' := by
  have e : ∀ a b : κ₁ → R, Function.extend (Sum.map j j) (Sum.elim a b) 0 =
      Sum.elim (Function.extend j a 0) (Function.extend j b 0) := fun a b => by
    funext k
    by_cases h : ∃ x, Sum.map j j x = k
    · obtain ⟨x, rfl⟩ := h
      rw [(hj.sumMap hj).extend_apply]
      rcases x with x | x <;> simp [hj.extend_apply]
    · rw [Function.extend_apply' _ _ _ h]
      rcases k with k | k
      · rw [Sum.elim_inl, Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => h ⟨Sum.inl x, by simp [hx]⟩]; rfl
      · rw [Sum.elim_inr, Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => h ⟨Sum.inr x, by simp [hx]⟩]; rfl
  rw [Rel, dbS_dv]
  simp only [Rel, dv, e, funext_iff, Sum.forall, Function.comp_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl,
    Sum.elim_inr, Pi.neg_apply, neg_inj]
  tauto

def kE (R : Type) [CommRing R] (p : κ → Prop) [DecidablePred p] : V R (κ ⊕ κ) ≃ₗ[R] V R (κ ⊕ κ) where
  toFun w := (Sum.elim (fun k => w.1 (.inl k) - w.1 (.inr k)) fun k => if p k then w.2 (.inl k) + w.2 (.inr k) else w.1 (.inr k),
    Sum.elim (fun k => w.2 (.inl k)) fun k => if p k then -w.1 (.inr k) else w.2 (.inl k) + w.2 (.inr k))
  invFun u := (Sum.elim (fun k => u.1 (.inl k) + if p k then -u.2 (.inr k) else u.1 (.inr k))
      fun k => if p k then -u.2 (.inr k) else u.1 (.inr k),
    Sum.elim (fun k => u.2 (.inl k)) fun k => (if p k then u.1 (.inr k) else u.2 (.inr k)) - u.2 (.inl k))
  map_add' a b := by ext (k | k) <;> by_cases h : p k <;> simp [h] <;> ring
  map_smul' a b := by ext (k | k) <;> by_cases h : p k <;> simp [h] <;> ring
  left_inv a := by ext (k | k) <;> by_cases h : p k <;> simp [h]
  right_inv a := by ext (k | k) <;> by_cases h : p k <;> simp [h]

theorem kE_dv (p : κ → Prop) [DecidablePred p] (w w' : V R κ) : kE R p (dv w w') =
    (Sum.elim (w.1 - w'.1) fun k => if p k then w.2 k - w'.2 k else w'.1 k,
      Sum.elim w.2 fun k => if p k then -w'.1 k else w.2 k - w'.2 k) := by
  ext (k | k) <;> by_cases h : p k <;> simp [kE, dv, h, sub_eq_add_neg]

def fE (R κ : Type) [CommRing R] : V R κ ≃ₗ[R] V R κ where
  toFun w := (w.2, -w.1)
  invFun w := (-w.2, w.1)
  map_add' a b := by ext <;> simp [add_comm]
  map_smul' a b := by ext <;> simp
  left_inv a := by simp
  right_inv a := by simp

variable [Fintype κ] [Fintype κ₁]

theorem isSp_fE : IsSp (fE R κ) := fun w w' => by
  show w.2 ⬝ᵥ (-w'.1) - w'.2 ⬝ᵥ (-w.1) = _
  rw [dotProduct_neg, dotProduct_neg, dotProduct_comm w.2, dotProduct_comm w'.2]; ring

theorem isSp_kE (p : κ → Prop) [DecidablePred p] : IsSp (kE R p) := fun w w' => by
  simp only [dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : p k <;> simp [kE, h] <;> ring

theorem IsSp.dbS {S : V R κ ≃ₗ[R] V R κ} (h : IsSp S) : IsSp (dbS S) := fun u u' => by
  obtain ⟨a, b, rfl⟩ := exists_dv u
  obtain ⟨a', b', rfl⟩ := exists_dv u'
  rw [dbS_dv, dbS_dv]
  simp only [dv, sumElim_dotProduct_sumElim, dotProduct_neg]
  linear_combination h a a' - h b b'

variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}

theorem schr_box {κ' : Type} [Fintype κ'] (w : V R κ) (w' : V R κ') (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ (Sum.elim w.1 w'.1, Sum.elim w.2 w'.2) (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ w' φ₂) := by
  funext x
  rw [← Sum.elim_comp_inl_inr x]
  simp only [schr, boxFun, sumElim_dotProduct_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem schr_dv (w w' : V R κ) (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (dv w w') (boxFun φ₁ φ₂) = boxFun (schr ψ w φ₁) (schr ψ (w'.1, -w'.2) φ₂) := schr_box w (w'.1, -w'.2) φ₁ φ₂

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem box_ne {φ₁ : (κ → R) → ℂ} {φ₂ : (κ₁ → R) → ℂ} (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) : boxFun φ₁ φ₂ ≠ 0 := fun e => by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h₁
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h₂
  exact mul_ne_zero hx hy (congrFun e (Sum.elim x y))

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem box_cancel {φ₁ φ₁' : (κ → R) → ℂ} {φ₂ : (κ₁ → R) → ℂ} (h₂ : φ₂ ≠ 0) (h : boxFun φ₁ φ₂ = boxFun φ₁' φ₂) : φ₁ = φ₁' := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h₂
  exact funext fun x => mul_right_cancel₀ hy (congrFun h (Sum.elim x y))

variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem ext_inl (x : κ → R) : Function.extend (Sum.inl : κ → κ ⊕ κ₁) x 0 = Sum.elim x 0 := by
  funext k
  rcases k with k | k
  · exact Sum.inl_injective.extend_apply _ _ _
  · rw [Function.extend_apply' _ _ _ (by simp)]; rfl

omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁] in
theorem ext_inr (x : κ₁ → R) : Function.extend (Sum.inr : κ₁ → κ ⊕ κ₁) x 0 = Sum.elim (0 : κ → R) x := by
  funext k
  rcases k with k | k
  · rw [Function.extend_apply' _ _ _ (by simp)]; rfl
  · exact Sum.inr_injective.extend_apply _ _ _

theorem Ax.box_E (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) : ∀ φ₂ ∈ C.sp κ, ∃ A ∈ C.sp κ₁, ∀ φ₁ ∈ C.sp κ, E (boxFun φ₁ φ₂) = boxFun (e φ₁) A := by
  intro φ₂ h₂
  have key : ∀ y : κ₁ → R, ∃ c : ℂ, ∀ φ₁ ∈ C.sp κ, ∀ x, E (boxFun φ₁ φ₂) (Sum.elim x y) = c * e φ₁ x := fun y => by
    set w := S.symm (Function.extend j y 0, Function.extend j 0 0) with hw
    have hr : Rel S j w (y, 0) := rel_lift hj (y, 0)
    have r0 : Rel S j 0 (0 : V R κ₁) := ⟨by simp [extend_zero' hj], by simp⟩
    have h₂' := h.schr κ (w.1, -w.2) φ₂ h₂
    obtain ⟨c, hc⟩ := h.uniq hS hj he (e' := Chr.res R Sum.inl ∘ₗ E ∘ₗ boxL κ (schr ψ (w.1, -w.2) φ₂)) (fun u u₁ hu φ hφ => by
      have e1 := hE.law _ _ ((rel_dv hj).2 ⟨hu, r0⟩) _ (h.box _ _ _ hφ _ h₂')
      rw [schr_dv, show (((0 : V R κ).1, -(0 : V R κ).2) : V R κ) = 0 by simp, schr_zero] at e1
      funext x
      show E (boxFun _ _) _ = schr ψ u₁ (fun x => E (boxFun _ _) (Function.extend Sum.inl x 0)) x
      rw [e1]
      simp only [schr, dv, ext_inl, sumElim_dotProduct_sumElim, ← Sum.elim_add_add]
      simp) (h.box_adm _ _ _ h₂' _ (hE.adm _ (h.res_adm _ _ _ Sum.inl_injective _ (h.ev0 _))))
    refine ⟨c, fun φ₁ h₁ x => ?_⟩
    have e1 := hE.law _ _ ((rel_dv hj).2 ⟨r0, hr⟩) _ (h.box _ _ _ h₁ _ h₂)
    rw [schr_dv, schr_zero] at e1
    have e2 : E (boxFun φ₁ _) (Function.extend Sum.inl x 0) = c * e φ₁ x := congrFun (hc φ₁ h₁) x
    rw [e1] at e2
    simpa [schr, dv, ext_inl, sumElim_dotProduct_sumElim, ← Sum.elim_add_add] using e2
  choose A hA using key
  obtain ⟨φ, hφ, h0⟩ := he.ne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have hx : e φ x ≠ 0 := hx
  refine ⟨A, ?_, fun φ₁ h₁ => funext fun z => ?_⟩
  · have := (C.sp κ₁).smul_mem (e φ x)⁻¹ (h.res _ _ _ Sum.inr_injective _
      (h.schr _ (Sum.elim x 0, 0) _ (hE.maps _ (h.box _ _ _ hφ _ h₂))))
    convert this using 1
    funext y
    rw [schrodinger_translate_apply]
    show _ = (e φ x)⁻¹ * E (boxFun φ φ₂) (Function.extend Sum.inr y 0 + Sum.elim x 0)
    rw [ext_inr, show (Sum.elim (0 : κ₁ → R) y + Sum.elim x (0 : κ₁ → R)) = Sum.elim x y by ext (k | k) <;> simp, hA y φ hφ]
    field_simp
  · rw [← Sum.elim_comp_inl_inr z, hA _ φ₁ h₁, mul_comm]
    rfl

theorem Ax.box_ne (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (hE : IsE C ψ (dbS S) (Sum.map j j) E)
    {l : ((κ₁ ⊕ κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∃ φ₁ ∈ C.sp κ, ∃ φ₂ ∈ C.sp κ, l (E (boxFun φ₁ φ₂)) ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := h.ne κ
  obtain ⟨w, w', hw⟩ := h.comp_cyc hS.dbS (hj.sumMap hj) hE hl _ (h.box _ _ _ hφ _ hφ) (Chr.box_ne h0 h0)
  obtain ⟨a, b, rfl⟩ := exists_dv w
  obtain ⟨a', b', rfl⟩ := exists_dv w'
  rw [schr_dv, schr_dv] at hw
  exact ⟨_, h.schr _ _ _ (h.schr _ _ _ hφ), _, h.schr _ _ _ (h.schr _ _ _ hφ), hw⟩

theorem Ax.exists_diag (h : Ax C ψ) (κ : Type) [Fintype κ] : ∃ l ∈ C.adm (κ ⊕ κ),
    (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), l (schr ψ (dv w w) φ) = l φ) ∧ Cyc C ψ l := by
  obtain ⟨l, h1, h2, h3⟩ := h.exists_form (isSp_kE (R := R) fun _ : κ => True)
  exact ⟨l, h1, fun w => h2 _ (by rw [kE_dv]; ext (k | k) <;> simp), h3⟩

theorem Ax.exists_avg (h : Ax C ψ) (hI : AxInt C) (hS : IsSp S) (hj : Function.Injective j)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) {l : ((κ₁ ⊕ κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm (κ₁ ⊕ κ₁))
    (hinv : ∀ w : V R κ₁, ∀ φ ∈ C.sp (κ₁ ⊕ κ₁), l (schr ψ (dv w w) φ) = l φ) (hc : Cyc C ψ l)
    (ρ : Type) [Fintype ρ] (i : ρ → κ) (hi : Function.Injective i) (hij : ∀ k, (∃ a, i a = k) ↔ ¬ ∃ a, j a = k) :
    ∃ L ∈ C.adm (κ ⊕ κ), (∃ φ ∈ C.sp (κ ⊕ κ), L φ ≠ 0) ∧ (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), L (schr ψ (dv w w) φ) = L φ) ∧
      ∀ (O : Module.End ℂ ((κ ⊕ κ → R) → ℂ)) (a : ℂ) (g : (ρ → R) ≃ₗ[R] (ρ → R)), a ≠ 0 → (∀ φ ∈ C.sp (κ ⊕ κ), O φ ∈ C.sp (κ ⊕ κ)) →
        (∀ u, ∀ φ ∈ C.sp (κ ⊕ κ), O (schr ψ (dv (S.symm (Function.extend i u 0, 0)) (S.symm (Function.extend i u 0, 0))) φ) =
          schr ψ (dv (S.symm (Function.extend i (g u) 0, 0)) (S.symm (Function.extend i (g u) 0, 0))) (O φ)) →
        (∀ φ ∈ C.sp (κ ⊕ κ), l (E (O φ)) = a * l (E φ)) →
        ∀ φ ∈ C.sp (κ ⊕ κ), L (O φ) = a * ((C.modu (LinearEquiv.det g) : ℝ) : ℂ) * L φ := by
  classical
  set K := (dbS S).trans (kE R fun k => ∃ a, j a = k) with hK
  have hKs : IsSp K := hS.dbS.trans (isSp_kE _)
  have hKd : ∀ w w', K (dv w w') = kE R (fun k => ∃ a, j a = k) (dv (S w) (S w')) := fun w w' => by
    rw [hK, LinearEquiv.trans_apply, dbS_dv]
  obtain ⟨T, hT⟩ := h.imp.ex hKs
  have hi' : Function.Injective (Sum.inr ∘ i : ρ → κ ⊕ κ) := Sum.inr_injective.comp hi
  have hE' := h.isE_res hT hi'
  obtain ⟨I, hIa, hIne, hIt, hIg⟩ := hI ρ
  have hIc : Cyc C ψ I := h.cyc isSp_fE hIa (fun w hw φ hφ => by
    rw [show w = (w.1, 0) from Prod.ext rfl hw, schrodinger_translate_apply, hIt _ _ hφ]) hIne
  have hx : ∀ u : ρ → R, Function.extend (Sum.inr ∘ i : ρ → κ ⊕ κ) u 0 = Sum.elim (0 : κ → R) (Function.extend i u 0) := fun u => by
    funext k
    rcases k with k | k
    · rw [Function.extend_apply' _ _ _ (by simp)]; rfl
    · by_cases hk : ∃ a, i a = k
      · obtain ⟨a, rfl⟩ := hk
        rw [Sum.elim_inr, hi.extend_apply]
        exact hi'.extend_apply _ _ a
      · rw [Sum.elim_inr, Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ (by simpa using hk)]; rfl
  have hrel : ∀ w : V R κ, Rel K (Sum.inr ∘ i) (dv w w) ((S w).1 ∘ i, 0) := fun w => by
    rw [Rel, hKd, kE_dv, hx]
    refine ⟨funext fun k => ?_, funext fun a => ?_⟩
    · rcases k with k | k
      · simp
      · by_cases hk : ∃ a, i a = k
        · have := (hij k).1 hk
          obtain ⟨a, rfl⟩ := hk
          simp only [Sum.elim_inr, if_neg this, hi.extend_apply, Function.comp_apply]
        · simp only [Sum.elim_inr, if_pos (not_not.1 (mt (hij k).2 hk)), Function.extend_apply' _ _ _ hk, sub_self, Pi.zero_apply]
    · simp only [Function.comp_apply, Sum.elim_inr, if_neg ((hij _).1 ⟨a, rfl⟩), sub_self, Pi.zero_apply]
  obtain ⟨c, hc'⟩ := h.line hKs hT (hE.adm l hl) fun w hw φ hφ => by
    obtain ⟨a, b, rfl⟩ := exists_dv w
    rw [hKd, kE_dv] at hw
    have h1 : (S a).1 = (S b).1 := funext fun k => sub_eq_zero.1 (congrFun hw (.inl k))
    have h2 : (S b).1 = Function.extend j ((S b).1 ∘ j) 0 := funext fun k => by
      by_cases hk : ∃ a, j a = k
      · obtain ⟨a, rfl⟩ := hk
        rw [hj.extend_apply]; rfl
      · rw [Function.extend_apply' _ _ _ hk]
        simpa [hk] using congrFun hw (.inr k)
    have h3 : (S a).2 ∘ j = (S b).2 ∘ j := funext fun k => by
      have := congrFun hw (.inr (j k))
      simp only [Sum.elim_inr, if_pos (⟨k, rfl⟩ : ∃ a, j a = j k), Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    show l (E _) = l (E φ)
    rw [hE.law _ _ ((rel_dv hj (w₁ := ((S b).1 ∘ j, (S b).2 ∘ j)) (w₁' := ((S b).1 ∘ j, (S b).2 ∘ j))).2
      ⟨⟨h1.trans h2, h3⟩, ⟨h2, rfl⟩⟩) φ hφ, hinv _ _ (hE.maps φ hφ)]
  have hc0 : c ≠ 0 := fun e0 => by
    obtain ⟨φ, hφ, hne⟩ := h.comp_ne hS.dbS (hj.sumMap hj) hE hc
    exact hne ((hc' φ hφ).trans (by rw [e0, zero_mul]))
  have hF : ∀ u, ∀ φ ∈ C.sp (κ ⊕ κ), c * (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ u =
      l (E (schr ψ (dv (S.symm (Function.extend i u 0, 0)) (S.symm (Function.extend i u 0, 0))) φ)) := fun u φ hφ => by
    refine Eq.trans ?_ (hc' _ (h.schr _ _ _ hφ)).symm
    have e1 := congrFun (hE'.law _ _ (hrel (S.symm (Function.extend i u 0, 0))) φ hφ) 0
    rw [S.apply_symm_apply, Function.extend_comp hi, schrodinger_translate_apply] at e1
    simp only [zero_add] at e1
    rw [← e1, LinearMap.comp_apply, Chr.res, LinearMap.funLeft_apply, extend_zero' hi']
  refine ⟨I ∘ₗ Chr.res R (Sum.inr ∘ i) ∘ₗ T, hE'.adm I hIa, h.comp_ne hKs hi' hE' hIc, fun w φ hφ => ?_,
    fun O a g ha hO hOl hOa φ hφ => ?_⟩
  · show I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) _) = I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ)
    rw [hE'.law _ _ (hrel w) φ hφ, schrodinger_translate_apply, hIt _ _ (hE'.maps φ hφ)]
  · have e1 : (Chr.res R (Sum.inr ∘ i) ∘ₗ T) (O φ) = a • fun u => (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ (g.symm u) := by
      funext u
      refine mul_left_cancel₀ hc0 ?_
      rw [hF _ _ (hO φ hφ), Pi.smul_apply, smul_eq_mul, mul_left_comm, hF _ _ hφ, ← hOa _ (h.schr _ _ _ hφ), hOl _ _ hφ,
        g.apply_symm_apply]
    have m1 : (fun u => (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ (g.symm u)) ∈ C.sp ρ := by
      have := (C.sp ρ).smul_mem a⁻¹ (hE'.maps _ (hO φ hφ))
      rwa [e1, smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    show I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) _) = _ * I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ)
    rw [e1, map_smul, hIg g _ (hE'.maps φ hφ) m1, smul_eq_mul, mul_assoc]

end PositivityTheory.ThKF0.Chr
