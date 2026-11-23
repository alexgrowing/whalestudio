import Mathlib

open Matrix

namespace GlobalTheory.FitSquare

variable {R : Type} [CommRing R]

theorem exists_lift {ι N M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (h : (ι → R) →ₗ[R] M) (g : N →ₗ[R] M)
    (hh : ∀ y, ∃ z, g z = h y) : ∃ l : (ι → R) →ₗ[R] N, g ∘ₗ l = h := by
  choose z hz using hh
  refine ⟨(Pi.basisFun R ι).constr R (fun i => z (Pi.basisFun R ι i)), ?_⟩
  apply (Pi.basisFun R ι).ext
  intro i
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, hz]

section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_updateRow_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α]
    (Φ : Matrix α α R) (k : α) (w : α → R) :
    (Φ.updateRow k w).det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(l, k), rfl⟩)

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Φ : Matrix α α R) :
    Φ.det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  have h := det_updateRow_mem_span_adjugate_entries Φ i (Φ i)
  rwa [updateRow_eq_self] at h

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₂₁_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₂₁ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₂₁ _ _ _

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₁₂_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₁₂ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₁₂ _ _ _

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.FitSquare.relations_mem {M : Type} [AddCommGroup M] [Module R M]
    (π : (n → R) →ₗ[R] M) (hπ : Function.Surjective π) (Φ : Matrix n n R)
    (hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (T : Matrix m m R)
    (hT : ∀ y, q (T *ᵥ y) = 0) :
    T.det ∈ Ideal.span {Φ.det} ∧ (Nonempty n → ∀ i j, T.adjugate i j ∈
      Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2)) := by
  choose a ha using fun j : m => hπ (q (Pi.single j 1))
  choose b hb using fun i : n => hq (π (Pi.single i 1))
  let A : Matrix n m R := Matrix.of fun i j => a j i
  let B : Matrix m n R := Matrix.of fun j i => b i j
  have hA : ∀ v, π (A *ᵥ v) = q v := by
    have h : π ∘ₗ A.mulVecLin = q := by
      ext j
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, LinearMap.single_apply,
        mulVec_single_one]
      rw [← ha j]
      rfl
    intro v
    exact LinearMap.congr_fun h v
  let U : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 (-A) 0 1
  let D : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks Φ 0 0 1
  let N : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 0 (-B) T
  have hker : ∀ u v, π u + q v = 0 → ∃ w, (U * D) *ᵥ w = Sum.elim u v := by
    intro u v h
    obtain ⟨z, hz⟩ := hΦ (u + A *ᵥ v) (by rw [map_add, hA, h])
    refine ⟨Sum.elim z v, ?_⟩
    rw [← mulVec_mulVec]
    simp [U, D, fromBlocks_mulVec, hz, neg_mulVec]
  have hcol : ∀ c, ∃ w, (U * D) *ᵥ w = fun r => N r c := by
    rintro (i | j)
    · obtain ⟨w, hw⟩ := hker (Pi.single i 1) (-b i) (by rw [map_neg, hb, add_neg_cancel])
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N, B, Pi.single_apply, one_apply]
    · obtain ⟨w, hw⟩ := hker 0 (fun r => T r j) (by
        have h := hT (Pi.single j 1)
        rw [mulVec_single_one] at h
        rw [map_zero, zero_add]
        exact h)
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N]
  choose w hw using hcol
  have hN : N = U * D * Matrix.of fun r c => w c r := by
    ext r c
    exact (congrFun (hw c) r).symm
  have hdetN : N.det = T.det := by simp [N, det_fromBlocks_zero₁₂]
  have hdetUD : (U * D).det = Φ.det := by simp [U, D, det_fromBlocks_zero₂₁, det_mul]
  refine ⟨?_, ?_⟩
  · rw [← hdetN, hN, det_mul, hdetUD]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro hn p p'
    have hdetJ := det_mem_span_adjugate_entries Φ
    have hD : ∀ x y, D.adjugate x y ∈
        Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2) := by
      intro x y
      rw [adjugate_apply]
      rcases y with k | k
      · rw [det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h : (D.updateRow (Sum.inl k) (Pi.single x 1)).toBlocks₁₁ =
              Φ.updateRow k (fun l => (Pi.single x 1 : n ⊕ m → R) (Sum.inl l)) := by
            ext s t
            by_cases hs : s = k <;> simp [D, toBlocks₁₁, updateRow_apply, hs]
          rw [h]
          exact Ideal.mul_mem_right _ _ (det_updateRow_mem_span_adjugate_entries _ _ _)
        · ext s t
          simp [D, toBlocks₂₁, updateRow_apply]
      · rw [det_eq_mul_of_toBlocks₁₂_eq_zero]
        · have h : (D.updateRow (Sum.inr k) (Pi.single x 1)).toBlocks₁₁ = Φ := by
            ext s t
            simp [D, toBlocks₁₁, updateRow_apply]
          rw [h]
          exact Ideal.mul_mem_right _ _ hdetJ
        · ext s t
          simp [D, toBlocks₁₂, updateRow_apply]
    have hadj : T.adjugate p p' = N.adjugate (Sum.inr p) (Sum.inr p') := by
      rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₁₂_eq_zero]
      · have h₁ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ = 1 := by
          ext s t
          simp [N, toBlocks₁₁, updateRow_apply]
        have h₂ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
            T.updateRow p' (Pi.single p 1) := by
          ext s t
          by_cases hs : s = p' <;> simp [N, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
        rw [h₁, h₂, det_one, one_mul]
      · ext s t
        simp [N, toBlocks₁₂, updateRow_apply]
    rw [hadj, hN, adjugate_mul_distrib, adjugate_mul_distrib, mul_apply]
    refine Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_
    rw [mul_apply]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_right _ _ (hD x y)

end blocks

open Matrix in
variable {R : Type} [CommRing R] in

theorem _root_.GlobalTheory.FitSquare.fitting_exact : ∀ (R : Type) [CommRing R] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), Function.Exact f g → Function.Surjective g → ∀ (k : ℕ) (x : R) (v : Fin k → M₁), Submodule.span R (Set.range v) = ⊤ → (∀ m : M₁, x • m = 0) → ∀ (a b : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Ψ : Matrix (Fin b) (Fin b) R), Nonempty (M₂ ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.mulVecLin)) → Nonempty (M₃ ≃ₗ[R] ((Fin b → R) ⧸ LinearMap.range Ψ.mulVecLin)) → x ^ k * Ψ.det ∈ Ideal.span {Φ.det} ∧ (a = 0 ∨ ((∀ p q, x ^ k * Ψ.adjugate p q ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)) ∧ (b = 0 → x ^ k ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)))) := by
  intro R _ M₁ M₂ M₃ _ _ _ _ _ _ f g hfg hg k x v hv hx a b Φ Ψ ⟨e₂⟩ ⟨e₃⟩
  let π : (Fin a → R) →ₗ[R] M₂ := e₂.symm.toLinearMap ∘ₗ (LinearMap.range Φ.mulVecLin).mkQ
  have hπ : Function.Surjective π := e₂.symm.surjective.comp (Submodule.mkQ_surjective _)
  have hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y := by
    intro y hy
    have hy' : (LinearMap.range Φ.mulVecLin).mkQ y = 0 := by
      simpa [π] using hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, hz⟩
  let ρ : (Fin b → R) →ₗ[R] M₃ := e₃.symm.toLinearMap ∘ₗ (LinearMap.range Ψ.mulVecLin).mkQ
  have hρ : Function.Surjective ρ := e₃.symm.surjective.comp (Submodule.mkQ_surjective _)
  choose u hu using fun j : Fin b => hg (ρ (Pi.single j 1))
  let H : (Fin b → R) →ₗ[R] M₂ := Fintype.linearCombination R u
  have hgH : ∀ t, g (H t) = ρ t := by
    have h : g ∘ₗ H = ρ := by
      ext j
      simp [H, hu]
    exact fun t => LinearMap.congr_fun h t
  have hkerg : ∀ y, g y = 0 → ∃ c : Fin k → R, ∑ i, c i • f (v i) = y := by
    intro y hy
    obtain ⟨m₁, rfl⟩ := (hfg y).1 hy
    have hm : m₁ ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hm
    exact ⟨c, by simp [map_sum]⟩
  let q : (Fin k ⊕ Fin b → R) →ₗ[R] M₂ :=
    Fintype.linearCombination R (Sum.elim (fun i => f (v i)) u)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨t, ht⟩ := hρ (g y)
    obtain ⟨c, hc⟩ := hkerg (y - H t) (by rw [map_sub, hgH, ht, sub_self])
    refine ⟨Sum.elim c t, ?_⟩
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hc]
    simp [H, Fintype.linearCombination_apply]
  have hcolΨ : ∀ j, ∃ c : Fin k → R, ∑ i, c i • f (v i) = H (fun r => Ψ r j) := by
    intro j
    apply hkerg
    rw [hgH]
    simp only [ρ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨Pi.single j 1, by
      rw [mulVecLin_apply, mulVec_single_one]; rfl⟩), map_zero]
  choose C hC using hcolΨ
  let T : Matrix (Fin k ⊕ Fin b) (Fin k ⊕ Fin b) R :=
    fromBlocks (x • 1) (-Matrix.of fun i j => C j i) 0 Ψ
  have hT : ∀ y, q (T *ᵥ y) = 0 := by
    have h0 : q ∘ₗ T.mulVecLin = 0 := by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
        LinearMap.single_apply, mulVec_single_one, LinearMap.zero_apply]
      rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
      rcases c with i | j
      · simp [T, col, one_apply]
        rw [← map_smul, hx, map_zero]
      · have hCj := hC j
        simp only [H, Fintype.linearCombination_apply] at hCj
        simp [T, col, neg_smul, Finset.sum_neg_distrib, hCj]
    exact fun y => LinearMap.congr_fun h0 y
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.FitSquare.relations_mem π hπ Φ hΦ q hq T hT
  have hdetT : T.det = x ^ k * Ψ.det := by simp [T, det_fromBlocks_zero₂₁, det_smul]
  rw [hdetT] at h₁
  refine ⟨h₁, ?_⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact Or.inl ha
  · right
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    refine ⟨fun p p' => ?_, fun hb0 => ?_⟩
    · have hadj : T.adjugate (Sum.inr p) (Sum.inr p') = x ^ k * Ψ.adjugate p p' := by
        rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h₁₁ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ =
              x • 1 := by
            ext s t
            simp [T, toBlocks₁₁, updateRow_apply]
          have h₂₂ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
              Ψ.updateRow p' (Pi.single p 1) := by
            ext s t
            by_cases hs : s = p' <;> simp [T, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
          rw [h₁₁, h₂₂, det_smul, det_one, mul_one, Fintype.card_fin]
        · ext s t
          simp [T, toBlocks₂₁, updateRow_apply]
      rw [← hadj]
      exact h₂ ‹_› _ _
    · subst hb0
      have h₃ : x ^ k ∈ Ideal.span {Φ.det} := by simpa [det_isEmpty] using h₁
      exact (Ideal.span_singleton_le_iff_mem _).2 (det_mem_span_adjugate_entries Φ) h₃

end GlobalTheory.FitSquare
