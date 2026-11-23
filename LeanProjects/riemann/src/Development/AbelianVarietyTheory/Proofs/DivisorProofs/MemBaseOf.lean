import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain.MapDown

section
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {h : ℕ}

theorem mv_apply (φ : A →+* B) (M : Matrix (Fin h) (Fin h) ℤ) (x : Fin h → A) (i : Fin h) :
    mv φ M x i = ∑ k, (M i k : B) * φ (x k) := by
  simp [mv, Matrix.mulVec, dotProduct]

theorem mv_one (φ : A →+* B) (x : Fin h → A) : mv φ 1 x = fun i => φ (x i) := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]

theorem mv_zero (φ : A →+* B) (M : Matrix (Fin h) (Fin h) ℤ) : mv φ M 0 = 0 := by
  funext i; simp [mv_apply]

theorem mv_add (φ : A →+* B) (M : Matrix (Fin h) (Fin h) ℤ) (x y : Fin h → A) :
    mv φ M (x + y) = mv φ M x + mv φ M y := by
  funext i; simp [mv_apply, mul_add, Finset.sum_add_distrib]

theorem mv_sub (φ : A →+* B) (M : Matrix (Fin h) (Fin h) ℤ) (x y : Fin h → A) :
    mv φ M (x - y) = mv φ M x - mv φ M y := by
  funext i; simp [mv_apply, mul_sub, Finset.sum_sub_distrib]

theorem mv_smul (φ : A →+* B) (M : Matrix (Fin h) (Fin h) ℤ) (a : A) (x : Fin h → A) :
    mv φ M (a • x) = φ a • mv φ M x := by
  funext i; simp [mv_apply, Finset.mul_sum, mul_left_comm]

theorem mem_baseOf (π : A) (x : Fin h → A) : x ∈ baseOf π h ↔ ∀ i, π ∣ x i := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨fun ⟨y, _, e⟩ i => ⟨y i, (congrFun e i).symm⟩, fun k => ?_⟩
  choose y hy using k
  exact ⟨y, trivial, funext fun i => (hy i).symm⟩

theorem mk_eq_iff {P : Submodule A (Fin h → A)} (π : A) (x y : P) :
    (Submodule.Quotient.mk x : Qt P (baseOf π h)) = Submodule.Quotient.mk y ↔ ∀ i, π ∣ x.1 i - y.1 i := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_baseOf]; rfl

end

theorem map_down : ∀ (p h o : ℕ) (A₁ A₂ B₁ B₂ : Type) [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂] (g₁ : A₁ →+* B₁) (g₂ : A₂ →+* B₂) (φ' : A₁ →+* A₂) (φ : B₁ →+* B₂) (π₁ : A₁) (π₂ : A₂) (ϖ₁ : B₁) (ϖ₂ : B₂) (γ₁ : ℕ → A₁) (γ₂ : ℕ → A₂) (δ₁ : ℕ → B₁) (δ₂ : ℕ → B₂) (Lie₁ Om₁ Lie₂ Om₂ LB₁ OB₁ LB₂ OB₂ : Type) [AddCommGroup Lie₁] [Module A₁ Lie₁] [AddCommGroup Om₁] [Module A₁ Om₁] [AddCommGroup Lie₂] [Module A₂ Lie₂] [AddCommGroup Om₂] [Module A₂ Om₂] [AddCommGroup LB₁] [Module B₁ LB₁] [AddCommGroup OB₁] [Module B₁ OB₁] [AddCommGroup LB₂] [Module B₂ LB₂] [AddCommGroup OB₂] [Module B₂ OB₂] (C₁ : RChain p A₁ h o π₁ γ₁ Lie₁ Om₁) (C₂ : RChain p A₂ h o π₂ γ₂ Lie₂ Om₂) (D₁ : RChain p B₁ h o ϖ₁ δ₁ LB₁ OB₁) (D₂ : RChain p B₂ h o ϖ₂ δ₂ LB₂ OB₂) (M : Matrix (Fin h) (Fin h) ℤ) (l₁ : Lie₁ → LB₁) (m₁ : Om₁ → OB₁) (l₂ : Lie₂ →+ LB₂) (m₂ : Om₂ → OB₂) (l : LB₁ → LB₂) (m : OB₁ → OB₂) (l' : Lie₁ → Lie₂) (m' : Om₁ →ₛₗ[φ'] Om₂) (G : Set Om₁), φ.comp g₁ = g₂.comp φ' → φ' π₁ = π₂ → g₂ π₂ = ϖ₂ → (∀ x : A₂, ϖ₂ ∣ g₂ x → π₂ ∣ x) → (∀ y : Lie₂, l₂ y ∈ (p : B₂) • (⊤ : Submodule B₂ LB₂) → y ∈ (p : A₂) • (⊤ : Submodule A₂ Lie₂)) → (∀ n ≤ o, ∀ x, piMap g₂ (Fin h) x ∈ D₂.L n → x ∈ C₂.L n) → (∀ n, o < n → C₁.L n = baseOf π₁ h) → C₁.Map D₁ g₁ 1 l₁ m₁ → C₂.Map D₂ g₂ 1 l₂ m₂ → D₁.Map D₂ φ M l m → (∀ y, l (l₁ y) = l₂ (l' y)) → Submodule.span A₁ G = ⊤ → (∀ w ∈ G, ∃ (x : C₁.L 0) (x' : C₂.L 0), x'.1 = mv φ' M x.1 ∧ C₁.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) ∧ C₂.ρ (m' w) = Submodule.Quotient.mk (Submodule.Quotient.mk x')) → C₁.Map C₂ φ' M l' m' := by
  intro p h o A₁ A₂ B₁ B₂ _ _ _ _ g₁ g₂ φ' φ π₁ π₂ ϖ₁ ϖ₂ γ₁ γ₂ δ₁ δ₂ Lie₁ Om₁ Lie₂ Om₂ LB₁ OB₁ LB₂ OB₂
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C₁ C₂ D₁ D₂ M l₁ m₁ l₂ m₂ l m l' m' G hc hπ hϖ hd hl hm hb H₁ H₂ H hll hG hρ
  have sq : ∀ x : Fin h → A₁, mv g₂ 1 (mv φ' M x) = mv φ M (mv g₁ 1 x) := fun x => by
    have e : ∀ a, φ (g₁ a) = g₂ (φ' a) := fun a => RingHom.congr_fun hc a
    funext i
    rw [mv_one, mv_one]
    simp [mv_apply, e]
  have mem : ∀ n, ∀ x ∈ C₁.L n, mv φ' M x ∈ C₂.L n := fun n x hx => by
    by_cases hn : n ≤ o
    · refine hm n hn _ ?_
      have := H.mem n _ (H₁.mem n x hx)
      rw [← sq, mv_one] at this
      exact this
    · rw [hb n (by omega), Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨y, -, rfl⟩ := hx
      rw [mv_smul, hπ]
      exact C₂.base_le n (Submodule.smul_mem_pointwise_smul _ _ _ trivial)
  let u₁ : ∀ {n}, C₁.L n → D₁.L n := fun {n} x => ⟨mv g₁ 1 x.1, H₁.mem n _ x.2⟩
  let u₂ : ∀ {n}, C₂.L n → D₂.L n := fun {n} x => ⟨mv g₂ 1 x.1, H₂.mem n _ x.2⟩
  have hu : ∀ {n} (x : C₁.L n) (x' : C₂.L n), x'.1 = mv φ' M x.1 → (u₂ x').1 = mv φ M (u₁ x).1 := fun x x' e => by
    change mv g₂ 1 x'.1 = _
    rw [e, sq]
  have inj : ∀ {n} (z x : C₂.L n), (Submodule.Quotient.mk (u₂ z) : Qt (D₂.L n) (baseOf ϖ₂ h)) =
      Submodule.Quotient.mk (u₂ x) →
      (Submodule.Quotient.mk z : Qt (C₂.L n) (baseOf π₂ h)) = Submodule.Quotient.mk x := fun z x e => by
    rw [mk_eq_iff] at e ⊢
    intro i
    refine hd _ ?_
    have := e i
    simp only [u₂, mv_one] at this
    rwa [map_sub]
  have hj : ∀ (y : Lie₁) (x : C₁.L 0) (x' : C₂.L 0), x'.1 = mv φ' M x.1 → C₁.j y = Submodule.Quotient.mk x →
      C₂.j (l' y) = Submodule.Quotient.mk x' := fun y x x' e k => by
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C₂.j (l' y))
    have a := H.j _ _ _ (hu x x' e) (H₁.j y x (u₁ x) rfl k)
    have b := H₂.j _ z (u₂ z) rfl hz.symm
    rw [← hz]
    exact inj _ _ (by rw [← b, ← hll, a])
  refine ⟨mem, hj, ?_, ?_, ?_⟩
  · have ex : ∀ w : Om₁, ∃ (x : C₁.L 0) (x' : C₂.L 0), x'.1 = mv φ' M x.1 ∧
        C₁.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk x) ∧
        C₂.ρ (m' w) = Submodule.Quotient.mk (Submodule.Quotient.mk x') := fun w => by
      have hw : w ∈ Submodule.span A₁ G := hG ▸ trivial
      induction hw using Submodule.span_induction with
      | mem w hw => exact hρ w hw
      | zero => exact ⟨0, 0, (mv_zero _ _).symm, by simp, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨x, x', e, k, k'⟩ := ha
        obtain ⟨y, y', f, n, n'⟩ := hb
        refine ⟨x + y, x' + y', ?_, by simp [k, n], by simp [k', n']⟩
        simp [mv_add, e, f]
      | smul a b _ hb =>
        obtain ⟨x, x', e, k, k'⟩ := hb
        refine ⟨a • x, φ' a • x', ?_, by simp [k], by simp [k', map_smulₛₗ]⟩
        simp [mv_smul, e]
    intro w x x' e k
    obtain ⟨y, y', f, n, n'⟩ := ex w
    rw [n']
    obtain ⟨t, ht⟩ := (Submodule.Quotient.eq _).1 (n.symm.trans k)
    rw [← Submodule.Quotient.mk_sub] at ht
    refine (Submodule.Quotient.eq _).2 ⟨l' t, ?_⟩
    rw [← Submodule.Quotient.mk_sub]
    exact hj t _ _ (by simp [mv_sub, e, f]) ht
  · intro n hn x x' y y' e f k
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C₂.ψ n (Submodule.Quotient.mk x'))
    have a := H.ψ n hn _ _ _ _ (hu x x' e) (hu y y' f) (H₁.ψ n hn x (u₁ x) y (u₁ y) rfl rfl k)
    have b := H₂.ψ n hn x' (u₂ x') z (u₂ z) rfl rfl hz.symm
    rw [← hz]
    exact inj _ _ (by rw [← b, a])
  · intro n hn x x' y e k
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C₂.κ n (Submodule.Quotient.mk x'))
    have a := H.κ n hn _ _ _ (hu x x' e) (H₁.κ n hn x (u₁ x) y rfl k)
    have b := H₂.κ n hn x' (u₂ x') z rfl hz.symm
    rw [← hz]
    refine (Submodule.Quotient.eq _).2 (hl _ ?_)
    rw [map_sub, ← hll]
    exact (Submodule.Quotient.eq _).1 (b.symm.trans a)

end GlobalTheory.RingChain.MapDown
