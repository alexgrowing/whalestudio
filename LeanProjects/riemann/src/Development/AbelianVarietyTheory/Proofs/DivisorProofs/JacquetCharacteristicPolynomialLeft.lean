import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ScalLeft

theorem sub_mem_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {σ : Representation ℂ G W}
    (φ : (subQuot S T).Equiv σ) (z : G) (c : ℂ) (hz : ∀ x, σ z x = c • x) (v : V)
    (hv : v ∈ S.toSubmodule) : ρ z v - c • v ∈ T.toSubmodule := by
  let w : S.toSubmodule := ⟨v, hv⟩
  have h1 : φ.toLinearEquiv (subQuot S T z (Submodule.Quotient.mk w)) =
      φ.toLinearEquiv (c • Submodule.Quotient.mk w) := by
    rw [map_smul]
    have := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap z (Submodule.Quotient.mk w)
    refine this.trans ?_
    exact hz _
  have h2 := φ.toLinearEquiv.injective h1
  change Submodule.Quotient.mk (S.toRepresentation z w) = Submodule.Quotient.mk (c • w) at h2
  rw [Submodule.Quotient.eq] at h2
  exact h2

theorem aeval_prod_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) {N : ℕ}
    (S : Fin (N + 1) → Submodule ℂ V) (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤)
    (q : Fin N → Polynomial ℂ)
    (hq : ∀ (t : Fin N) (v : V), v ∈ S t.succ → Polynomial.aeval T (q t) v ∈ S t.castSucc) :
    Polynomial.aeval T (∏ t, q t) = 0 := by
  classical
  let q' : ℕ → Polynomial ℂ := fun s => if h : s < N then q ⟨s, h⟩ else 1
  have key : ∀ t (ht : t ≤ N), ∀ v ∈ S ⟨t, Nat.lt_succ_of_le ht⟩,
      Polynomial.aeval T (∏ s ∈ Finset.range t, q' s) v = 0 := by
    intro t
    induction t with
    | zero =>
      intro _ v hv
      have : v = 0 := by
        have h0' : S ⟨0, Nat.zero_lt_succ N⟩ = ⊥ := h0
        rw [h0'] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      simp [this]
    | succ t ih =>
      intro ht v hv
      have htN : t < N := ht
      rw [Finset.prod_range_succ, map_mul, Module.End.mul_apply]
      have hq' : q' t = q ⟨t, htN⟩ := dif_pos htN
      rw [hq']
      exact ih htN.le _ (hq ⟨t, htN⟩ v hv)
  ext v
  have h1 : ∏ t, q t = ∏ s ∈ Finset.range N, q' s := by
    rw [Finset.prod_range (fun s => q' s)]
    exact Finset.prod_congr rfl fun i _ => by
      show q i = if h : (i : ℕ) < N then q ⟨i, h⟩ else 1
      rw [dif_pos i.2]
  rw [h1]
  have hv : v ∈ S ⟨N, Nat.lt_succ_self N⟩ := by
    have : S ⟨N, Nat.lt_succ_self N⟩ = ⊤ := hN
    rw [this]; trivial
  simpa using key N le_rfl v hv

theorem aeval_prod_eq_zero_of_steps {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (z : G) {N : ℕ} (S : Fin (N + 1) → Subrepresentation ρ)
    (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (c : Fin N → ℂ)
    (hc : ∀ t : Fin N, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W),
      Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv σ) ∧ ∀ x, σ z x = c t • x) :
    Polynomial.aeval (ρ z) (∏ t, (Polynomial.X - Polynomial.C (c t))) = 0 := by
  refine aeval_prod_eq_zero (ρ z) (fun t => (S t).toSubmodule) (by rw [h0]; rfl) (by rw [hN]; rfl) _
    fun t w hw => ?_
  obtain ⟨W, _, _, σ, ⟨φ⟩, hσ⟩ := hc t
  have := sub_mem_of_equiv _ _ φ z (c t) hσ w hw
  simpa using this

section Gen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem scalar_entry {n : Type} [Fintype n] [DecidableEq n] (t : kˣ) (i j : n) :
    ((GeneralLinearGroup.scalar n t : GL n k) : Matrix n n k) i j = if i = j then (t : k) else 0 := by
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem det_scalar {n : Type} [Fintype n] [DecidableEq n] (t : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar n t : GL n k) = t ^ Fintype.card n := by
  ext
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] in

theorem scalar_mem_relParab (f : ∀ i, (Σ j, c i j) ≃ m i) (t : α → kˣ) :
    (fun i => GeneralLinearGroup.scalar (m i) (t i) : Levi k m) ∈ relParab k f := by
  rw [relParab, Subgroup.mem_pi]
  intro i _
  rw [mem_parab]
  intro x y hxy
  rw [scalar_entry, if_neg]
  rintro rfl
  exact lt_irrefl _ hxy

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] in

theorem relProj_scalar (f : ∀ i, (Σ j, c i j) ≃ m i) (t : α → kˣ) :
    relProj k f ⟨_, scalar_mem_relParab f t⟩ =
      fun i j => GeneralLinearGroup.scalar (c i j) (t i) := by
  funext i j
  ext a b
  change ((GeneralLinearGroup.scalar (m i) (t i) : GL (m i) k) : Matrix (m i) (m i) k)
    (f i ⟨j, a⟩) (f i ⟨j, b⟩) = _
  rw [scalar_entry, scalar_entry]
  simp [(f i).injective.eq_iff]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] in

theorem scalar_comm (t : α → kˣ) (y : Levi k m) :
    y * (fun i => GeneralLinearGroup.scalar (m i) (t i) : Levi k m) =
      (fun i => GeneralLinearGroup.scalar (m i) (t i) : Levi k m) * y := by
  funext i
  ext a b
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]

theorem relInd_scalar (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (∀ i, Levi k (c i)) W)
    (t : α → kˣ) (d : ℂ)
    (hd : ∀ w, ρ (fun i j => GeneralLinearGroup.scalar (c i j) (t i)) w = d • w)
    (F : smoothPart (ind (relParab k f) ((twist ρ (relDeltaHalf k c)).comp (relProj k f)))) :
    relInd f ρ (fun i => GeneralLinearGroup.scalar (m i) (t i)) F =
      ((relDeltaHalf k c (fun i j => GeneralLinearGroup.scalar (c i j) (t i)) : ℂ) * d) • F := by
  refine Subtype.ext (Subtype.ext (funext fun y => ?_))
  change F.1.1 (y * _) = _
  rw [scalar_comm]
  refine (F.1.2 ⟨_, scalar_mem_relParab f t⟩ y).trans ?_
  change (twist ρ (relDeltaHalf k c)) (relProj k f ⟨_, scalar_mem_relParab f t⟩) (F.1.1 y) = _
  rw [relProj_scalar, twist_apply, hd, smul_smul]
  rfl

theorem relJac_of_scalar (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (Φ : Levi k m → ℂ) (hρ : ∀ g w, ρ g w = Φ g • w) (y : ∀ i, Levi k (c i))
    (x : Jacquet ρ (relUnip k f)) :
    relJac f ρ y x = ((((relDeltaHalf k c y)⁻¹ : ℂˣ) : ℂ) * Φ (relEmb k f y)) • x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [relJac_mk, hρ, Submodule.Quotient.mk_smul, smul_smul]

end Gen

section Spec
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem detPair_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (g : Levi k (Two (Fin u) (Fin v))) (w : ℂ ⊗[ℂ] ℂ) :
    ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) g w =
      ((χ₁ (GeneralLinearGroup.det (g false)) : ℂ) * (χ₂ (GeneralLinearGroup.det (g true)) : ℂ)) • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    change extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂) (g false, g true) (a ⊗ₜ b) = _
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply]
    rw [← smul_eq_mul, ← smul_eq_mul (a := ((χ₂ _ : ℂˣ) : ℂ)), ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul, mul_comm]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem modExp_bool_false (n : Bool → Type) [∀ a, Fintype (n a)] :
    modExp n false = Fintype.card (n true) := by
  simp [modExp, Finset.sum_filter]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem modExp_bool_true (n : Bool → Type) [∀ a, Fintype (n a)] :
    modExp n true = -Fintype.card (n false) := by
  simp [modExp, Finset.sum_filter]

theorem absPow_zero' (x : kˣ) : absPow k 0 x = 1 := by
  ext; simp [val_absPow]

end Spec

section Cells
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem leviTwo_scalar_one (ϖ : kˣ) (m : Type) [Fintype m] [DecidableEq m] :
    leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) =
      fun j => GeneralLinearGroup.scalar (Two (Fin 1) m j) (cond j 1 ϖ) := by
  funext j
  cases j
  · rfl
  · exact (map_one (GeneralLinearGroup.scalar m)).symm

theorem cell_scalar_fst (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m]
    (b : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin v) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j) (ϖ : kˣ) (hb : b.1 false false = 1)
    (x : _) : cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)
      (leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) x =
      (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • x := by
  have key := relInd_scalar g _ (fun j => cond j 1 ϖ) _
    (fun w => relJac_of_scalar f _ _ (detPair_apply χ₁ χ₂ u v) _ w) x
  refine (congrArg (fun z => cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) z x) (leviTwo_scalar_one ϖ m)).trans (key.trans ?_)
  congr 1
  have hb0 : b.1 true false = 0 := by
    have := b.2.2 false
    rw [Fintype.sum_bool] at this
    have := this.trans (Fintype.card_fin 1)
    omega
  have hu : b.1 false true + b.1 false false = u := by
    have := b.2.1 false
    rw [Fintype.sum_bool] at this
    exact this.trans (Fintype.card_fin u)
  have h1 : relDeltaHalf k (fun j i => Fin (b.1 i j))
      (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ)) = 1 := by
    rw [relDeltaHalf_apply]
    simp [Fintype.prod_bool, deltaHalf_apply, det_scalar, modExp_bool_false, modExp_bool_true, hb0, absPow_zero']
  have h2 : relDeltaHalf k (fun i j => Fin (b.1 i j))
      (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) =
      absPow k ((b.1 false true : ℂ) / 2) ϖ := by
    rw [relDeltaHalf_apply]
    simp [swapBlocks, Fintype.prod_bool, deltaHalf_apply, det_scalar, modExp_bool_false, modExp_bool_true, hb0, hb, absPow_zero']
  have h3 : GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) false) = ϖ := by
    simp [relEmb_apply, swapBlocks, det_leviEmb, Fintype.prod_bool, det_scalar, hb]
  have h4 : GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) true) = 1 := by
    simp [relEmb_apply, swapBlocks, det_leviEmb, Fintype.prod_bool, det_scalar, hb0]
  rw [h1, h2, h3, h4]
  have hs : (1 - (u : ℂ)) / 2 = -((b.1 false true : ℂ) / 2) := by
    have hu' : (u : ℂ) = (b.1 false true : ℂ) + 1 := by
      have hu'' : u = b.1 false true + 1 := by omega
      exact_mod_cast hu''
    rw [hu']; ring
  rw [hs, absPow_neg]
  simp [mul_comm]

theorem cell_scalar_snd (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m]
    (b : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin v) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j) (ϖ : kˣ) (hb : b.1 true false = 1)
    (x : _) : cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)
      (leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) x =
      (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • x := by
  have key := relInd_scalar g _ (fun j => cond j 1 ϖ) _
    (fun w => relJac_of_scalar f _ _ (detPair_apply χ₁ χ₂ u v) _ w) x
  refine (congrArg (fun z => cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) z x) (leviTwo_scalar_one ϖ m)).trans (key.trans ?_)
  congr 1
  have hb0 : b.1 false false = 0 := by
    have := b.2.2 false
    rw [Fintype.sum_bool] at this
    have := this.trans (Fintype.card_fin 1)
    omega
  have hv : b.1 true true + b.1 true false = v := by
    have := b.2.1 true
    rw [Fintype.sum_bool] at this
    exact this.trans (Fintype.card_fin v)
  have h1 : relDeltaHalf k (fun j i => Fin (b.1 i j))
      (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ)) = 1 := by
    rw [relDeltaHalf_apply]
    simp [Fintype.prod_bool, deltaHalf_apply, det_scalar, modExp_bool_false, modExp_bool_true, hb0, absPow_zero']
  have h2 : relDeltaHalf k (fun i j => Fin (b.1 i j))
      (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) =
      absPow k ((b.1 true true : ℂ) / 2) ϖ := by
    rw [relDeltaHalf_apply]
    simp [swapBlocks, Fintype.prod_bool, deltaHalf_apply, det_scalar, modExp_bool_false, modExp_bool_true, hb0, hb, absPow_zero']
  have h3 : GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) false) = 1 := by
    simp [relEmb_apply, swapBlocks, det_leviEmb, Fintype.prod_bool, det_scalar, hb0]
  have h4 : GeneralLinearGroup.det (relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (fun j i => GeneralLinearGroup.scalar (Fin (b.1 i j)) (cond j 1 ϖ))) true) = ϖ := by
    simp [relEmb_apply, swapBlocks, det_leviEmb, Fintype.prod_bool, det_scalar, hb]
  rw [h1, h2, h3, h4]
  have hs : (1 - (v : ℂ)) / 2 = -((b.1 true true : ℂ) / 2) := by
    have hv' : (v : ℂ) = (b.1 true true : ℂ) + 1 := by
      have hv'' : v = b.1 true true + 1 := by omega
      exact_mod_cast hv''
    rw [hv']; ring
  rw [hs, absPow_neg]
  simp [mul_comm]
end Cells

set_option maxHeartbeats 1000000 in

theorem aeval_jac₂_scalar_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (m : Type) [Fintype m] [DecidableEq m] (e : Fin 1 ⊕ m ≃ Fin (u + v)) (ϖ : kˣ), Polynomial.aeval (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) ((Polynomial.X - Polynomial.C (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ)) * (Polynomial.X - Polynomial.C (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ))) = 0 := by
  intro k _ _ _ _ hG χ₁ χ₂ hχ₁ hχ₂ u v m _ _ e ϖ
  let c₁ : ℂ := (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ)
  let c₂ : ℂ := (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ)
  have hcont : Continuous (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom := by
    show Continuous fun g : Levi k (Two (Fin u) (Fin v)) => ((g false : GL (Fin u) k), (g true : GL (Fin v) k))
    exact (continuous_apply false).prodMk (continuous_apply true)
  have hsm : IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 hχ₁.detChar)
      ((isSmooth_ofChar_iff _).2 hχ₂.detChar)) _ hcont
  obtain ⟨N, b, hb⟩ := hG k Bool Bool (Fin (u + v)) (Two (Fin u) (Fin v)) (Two (Fin 1) m)
    (two (stdSum rfl)) (two e)
  refine Exists.elim (hb (ℂ ⊗[ℂ] ℂ) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) hsm) fun S hS => ?_
  have h0 := hS.2.1
  have hN := hS.2.2.1
  have hstep := hS.2.2.2
  haveI := Fintype.ofFinite (SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m))
  let cc : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m) → ℂ := fun b' =>
    if b'.1 false false = 1 then c₁ else c₂
  let z : Levi k (Two (Fin 1) m) := leviTwo k (Fin 1) m (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)
  have col : ∀ b' : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m),
      b'.1 true false + b'.1 false false = 1 := by
    intro b'
    have := b'.2.2 false
    rw [Fintype.sum_bool] at this
    exact this.trans (Fintype.card_fin 1)
  have hcell : ∀ (b' : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m))
      (f : ∀ i, (Σ j, Fin (b'.1 i j)) ≃ Two (Fin u) (Fin v) i)
      (g : ∀ j, (Σ i, Fin (b'.1 i j)) ≃ Two (Fin 1) m j) x,
      cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) z x = cc b' • x := by
    intro b' f g x
    by_cases h : b'.1 false false = 1
    · simp only [cc, if_pos h]
      exact cell_scalar_fst χ₁ χ₂ u v m b' f g ϖ h x
    · simp only [cc, if_neg h]
      have h' : b'.1 true false = 1 := by have := col b'; omega
      exact cell_scalar_snd χ₁ χ₂ u v m b' f g ϖ h' x
  have hkill := aeval_prod_eq_zero_of_steps (jac (two e) (parInd (two (stdSum rfl)) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom))) z S h0 hN
    (fun t => cc (b t)) fun t => ⟨_, _, _, _, hstep t (b t).nonempty_rows.some (b t).nonempty_cols.some,
      hcell _ _ _⟩
  have hinj : Function.Injective fun b' : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m) =>
      decide (b'.1 false false = 1) := by
    intro b₁ b₂ h
    have r₁ : ∀ i, b₁.1 i true + b₁.1 i false = Fintype.card (Two (Fin u) (Fin v) i) := fun i => by
      have := b₁.2.1 i; rwa [Fintype.sum_bool] at this
    have r₂ : ∀ i, b₂.1 i true + b₂.1 i false = Fintype.card (Two (Fin u) (Fin v) i) := fun i => by
      have := b₂.2.1 i; rwa [Fintype.sum_bool] at this
    have c1 := col b₁
    have c2 := col b₂
    have h00 : b₁.1 false false = b₂.1 false false := by
      simp only [decide_eq_decide] at h
      omega
    have h10 : b₁.1 true false = b₂.1 true false := by omega
    apply Subtype.ext
    funext i j
    cases j
    · cases i
      · exact h00
      · exact h10
    · have := r₁ i
      have := r₂ i
      cases i
      · omega
      · omega
  have hdvd : ∏ t, (Polynomial.X - Polynomial.C (cc (b t))) ∣
      (Polynomial.X - Polynomial.C c₁) * (Polynomial.X - Polynomial.C c₂) := by
    let Q : Bool → Polynomial ℂ := fun x => if x then Polynomial.X - Polynomial.C c₁
      else Polynomial.X - Polynomial.C c₂
    have e1 : ∏ t, (Polynomial.X - Polynomial.C (cc (b t))) =
        ∏ b' : SizeMatrix (Two (Fin u) (Fin v)) (Two (Fin 1) m), Q (decide (b'.1 false false = 1)) := by
      refine Fintype.prod_equiv b _ _ fun t => ?_
      by_cases h : (b t).1 false false = 1 <;> simp [Q, cc, h]
    rw [e1, ← Finset.prod_image (f := Q) (fun x _ y _ hxy => hinj hxy)]
    refine (Finset.prod_dvd_prod_of_subset _ Finset.univ Q (Finset.subset_univ _)).trans ?_
    rw [Fintype.prod_bool]
    exact dvd_rfl
  exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hkill

end GlobalTheory.ScalLeft
