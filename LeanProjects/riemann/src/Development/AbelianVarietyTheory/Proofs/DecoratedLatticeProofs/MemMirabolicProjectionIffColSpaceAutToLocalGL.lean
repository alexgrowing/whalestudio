import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.VolBridge

section PrXIff
variable {E : Type} [Field E] {M c' : ℕ}

theorem inX_castAdd (v : Sp E M) (i : Fin M) : Loc.inX E M c' v (Fin.castAdd c' i) = v i := by
  simp [Loc.inX]

theorem inX_natAdd (v : Sp E M) (i : Fin c') : Loc.inX E M c' v (Fin.natAdd M i) = 0 := by
  simp [Loc.inX]

theorem extX_inX (y : Sp E M ≃ₗ[E] Sp E M) (v : Sp E M) :
    extX c' y (Loc.inX E M c' v) = Loc.inX E M c' (y v) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [extX_castAdd, inX_castAdd]
    have h : (fun j => Loc.inX E M c' v (Fin.castAdd c' j)) = v := funext fun j => inX_castAdd v j
    rw [h]
  · rw [extX_natAdd, inX_natAdd, inX_natAdd]

variable {A : Type} {c : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem e_inl (a : A) : e (Sum.inl a) = Fin.castAdd c' (eX e hcc he a) := Fin.ext (by simp [eX_val])

include he in
theorem e_inr (i : Fin c) : e (Sum.inr i) = Fin.natAdd M (⟨i.val, hcc ▸ i.isLt⟩ : Fin c') := Fin.ext (by simp [he])

theorem single_inl (a : A) :
    (Pi.single (e (Sum.inl a)) 1 : Sp E (M + c')) = Loc.inX E M c' (Pi.single (eX e hcc he a) 1) := by
  rw [e_inl e hcc he]
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [inX_castAdd]
    by_cases h : i = eX e hcc he a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_injective _ _ h')), Pi.single_eq_of_ne h]
  · rw [inX_natAdd, Pi.single_eq_of_ne]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end PrXIff

section Blocks
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
  (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

theorem locHom_inl_inl (r : Sp E (M + c') ≃ₗ[E] Sp E (M + c')) (y : Sp E M ≃ₗ[E] Sp E M)
    (hr : ∀ v, r (Loc.inX E M c' v) = Loc.inX E M c' (y v)) (a b : A) :
    (locHom ι e r).val (Sum.inl a) (Sum.inl b) = (locHom ι (eX e hcc he) y).val a b := by
  show ι (r (Pi.single (e (Sum.inl b)) 1) (e (Sum.inl a))) = ι (y (Pi.single (eX e hcc he b) 1) (eX e hcc he a))
  rw [single_inl e hcc he, hr, e_inl e hcc he, inX_castAdd]

theorem locHom_extX (y : Sp E M ≃ₗ[E] Sp E M) :
    locHom ι e (extX c' y) = embX c (locHom ι (eX e hcc he) y) := by
  ext i j
  rw [GlobalTheory.RootEx.VolN.val_embX]
  show ι (extX c' y (Pi.single (e j) 1) (e i)) = _
  rcases i with a | s
  · rw [e_inl e hcc he, extX_castAdd]
    rcases j with b | t
    · rw [single_inl e hcc he]
      have h : (fun l => Loc.inX E M c' (Pi.single (eX e hcc he b) (1 : E)) (Fin.castAdd c' l)) = Pi.single (eX e hcc he b) 1 :=
        funext fun l => inX_castAdd _ l
      rw [h]
      rfl
    · have h : (fun l => (Pi.single (e (Sum.inr t)) (1 : E) : Sp E (M + c')) (Fin.castAdd c' l)) = 0 := by
        funext l
        rw [Pi.single_eq_of_ne]
        · rfl
        intro h'
        have := congrArg Fin.val h'
        simp [he] at this
        omega
      rw [h, map_zero]
      simp
  · rw [e_inr e hcc he, extX_natAdd]
    rcases j with b | t
    · rw [Pi.single_eq_of_ne]
      · simp
      intro h'
      have := congrArg Fin.val h'
      simp [eX_val] at this
      have := eX_lt e hcc he b
      omega
    · rw [e_inr e hcc he]
      by_cases h : s = t
      · subst h; simp
      · rw [Pi.single_eq_of_ne]
        · simp [Matrix.one_apply, h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        exact h (Fin.ext this)

end Blocks

theorem prX_iff_locHom : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  intro E k _ _ _ _ _ ι A _ _ M c c' e hcc he hN hdense CE Ck O hO hCkO hCkR hCE y
  constructor
  · rintro ⟨r, hr, hry⟩
    have hg : locHom ι e r ∈ Ck := (hCE r).1 hr
    obtain ⟨x', u, hu, hxu⟩ := GlobalTheory.RootEx.VolN.exists_of_mem_R (hCkR hg)
    have hu' := GlobalTheory.RootEx.Model.mem_N_iff.1 hu
    have hx' : x' = locHom ι (eX e hcc he) y := by
      ext a b
      rw [← locHom_inl_inl ι e hcc he r y hry a b, hxu, Units.val_mul, GlobalTheory.RootEx.VolN.val_embX, Matrix.mul_apply,
        Fintype.sum_sum_type]
      have h1 : ∀ a', u.val (Sum.inl a') (Sum.inl b) = if a' = b then 1 else 0 := fun a' => by
        rw [hu' (Sum.inl a') (Sum.inl b) le_rfl]
        simp [Matrix.one_apply]
      simp [h1]
    refine ⟨embX c x' * u * (embX c x')⁻¹, ?_, ?_⟩
    · have := GlobalTheory.RootEx.Model.conj_mem hu x'⁻¹
      simpa [map_inv, inv_inv] using this
    · rw [← hx']
      simpa [mul_assoc, ← hxu] using hg
  · rintro ⟨u, hu, huC⟩
    set x := locHom ι (eX e hcc he) y with hx
    have huO : u * embX c x ∈ O := (hCkO _ (hCkR huC)).1 huC
    have hV : IsOpen {v : GL (A ⊕ Fin c) k | v * embX c x ∈ O} := hO.preimage (continuous_mul_const _)
    obtain ⟨x₀, hx₀, hx₀V⟩ := hdense u hu _ hV huO
    refine ⟨x₀ * extX c' y, ?_, fun v => ?_⟩
    · rw [hCE, map_mul, locHom_extX ι e hcc he]
      have hR : locHom ι e x₀ * embX c x ∈ R k A c 1 :=
        mul_mem (Subgroup.mem_sup_right ((hN x₀).1 hx₀)) (Subgroup.mem_sup_left ⟨x, rfl⟩)
      exact (hCkO _ hR).2 hx₀V
    · show x₀ (extX c' y (Loc.inX E M c' v)) = _
      rw [extX_inX]
      exact (Subgroup.mem_inf.1 hx₀).2 (y v)

end GlobalTheory.VolBridge
