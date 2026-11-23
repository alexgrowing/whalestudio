import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

noncomputable section

section Defs

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

def IsP (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUpUni p ∧ ∀ a b : Fin n, (k < a.val ∨ b.val ≤ k) → p a b ∈ R

def IsPP (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Prop := IsP R k p ∧ IsP R k p⁻¹

def IsD (k : ℕ) (D : Matrix (Fin n) (Fin n) K) : Prop :=
  IsUpUni D ∧ IsInt R D ∧ ∀ a b : Fin n, a.val ≤ k → D a b = (1 : Matrix (Fin n) (Fin n) K) a b

def msk (k : ℕ) (y : Fin n → K) : Fin n → K := fun j => if k < j.val then y j else 0

def b22 (k : ℕ) (p : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun a b => if k < a.val then p a b else (1 : Matrix (Fin n) (Fin n) K) a b

def abelian₂ (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : (Fin n → R) →ₗ[R] (Fin n → K) :=
  LinearMap.pi (fun j => if k < j.val then lamTil R Z j.val else 0)

def colSpan (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : Submodule R (Fin n → R) where
  carrier := {x | ∃ t : Fin n → R, (∀ j : Fin n, k < j.val → t j = 0) ∧
    Z *ᵥ coeLin R t = coeLin R x}
  add_mem' := by
    rintro x y ⟨t, ht, e⟩ ⟨s, hs, e'⟩
    exact ⟨t + s, fun j hj => by simp [ht j hj, hs j hj], by
      rw [map_add, map_add, Matrix.mulVec_add, e, e']⟩
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  smul_mem' := by
    rintro r x ⟨t, ht, e⟩
    refine ⟨r • t, fun j hj => by simp [ht j hj], ?_⟩
    rw [map_smul, map_smul, A5x2.smul_coe, A5x2.smul_coe, Matrix.mulVec_smul, e]

abbrev MM (k : ℕ) (Z : Matrix (Fin n) (Fin n) K) : Type := (Fin n → R) ⧸ colSpan R k Z

def dRel (k : ℕ) (Z₀ : Matrix (Fin n) (Fin n) K) :
    Setoid {D : Matrix (Fin n) (Fin n) K // IsD R k D} where
  r D₁ D₂ := ∀ (x : Fin n → R) (j : Fin n), ((D₁.1 - D₂.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R
  iseqv := ⟨fun D x j => by simp [R.zero_mem],
    fun {D₁ D₂} h x j => by
      have := R.neg_mem (h x j)
      rwa [← Pi.neg_apply, ← Matrix.neg_mulVec, neg_sub] at this,
    fun {D₁ D₂ D₃} h h' x j => by
      have := R.add_mem (h x j) (h' x j)
      rwa [← Pi.add_apply, ← Matrix.add_mulVec, sub_add_sub_cancel] at this⟩

def Nrm (k : ℕ) (Z₀ : Matrix (Fin n) (Fin n) K) (D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) :
    Prop := Quotient.out (Quotient.mk (dRel R k Z₀) D) = D

structure GB (k : ℕ) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀') :
    Prop where
  e : Ψ (Submodule.Quotient.mk (eLast R)) = Submodule.Quotient.mk (eLast R)
  lift : ∃ D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}, Nrm R k Z₀ D ∧
    ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      abelian₂ R k Z₀' y = D.1 *ᵥ abelian₂ R k Z₀ x
  bad : ∃ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
    abelian₂ R k Z₀ x = 0 ∧ lamTil R Z₀' k y - lamTil R Z₀ k x ∉ R

def Rel {k : ℕ} {Z₀ Z₀' : Matrix (Fin n) (Fin n) K} (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀')
    (L L' : Submodule R (Fin n → R)) : Prop :=
  ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → (x ∈ L ↔ y ∈ L')

end Defs

end

end Formalism.FourierDecayAlt.P.A5x9

end

section

namespace Formalism.FourierDecayAlt.P.A5x9

theorem lift_abs {R P P' V : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] [AddCommGroup V] [Module R V]
    (L S0 : Submodule R P) (L' S0' : Submodule R P') (Λ : P →ₗ[R] V) (Λ' : P' →ₗ[R] V)
    (DD : V →ₗ[R] V) (φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L'))
    (hS : S0 ≤ L) (hS' : S0' ≤ L') (hk : ∀ x ∈ S0, Λ x = 0) (hk' : ∀ y ∈ S0', Λ' y = 0)
    (h1 : ∀ x ∈ L, DD (Λ x) = 0 → x ∈ S0) (h1' : ∀ y ∈ L', Λ' y = 0 → y ∈ S0')
    (h2 : ∀ x, ∃ y, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x))
    (h3 : ∀ y, ∃ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) :
    ∃ Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0'), ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) := by
  let f : P →ₗ[R] (P' ⧸ L') × V := LinearMap.prod (φ.toLinearMap.comp L.mkQ) (DD.comp Λ)
  let f' : P' →ₗ[R] (P' ⧸ L') × V := LinearMap.prod L'.mkQ Λ'
  have fx : ∀ x, f x = (φ (Submodule.Quotient.mk x), DD (Λ x)) := fun x => rfl
  have fy : ∀ y, f' y = (Submodule.Quotient.mk y, Λ' y) := fun y => rfl
  have hf : S0 ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker, fx, (Submodule.Quotient.mk_eq_zero L).2 (hS hx), map_zero, hk x hx,
      map_zero]
    rfl
  have hf' : S0' ≤ LinearMap.ker f' := by
    intro y hy
    rw [LinearMap.mem_ker, fy, (Submodule.Quotient.mk_eq_zero L').2 (hS' hy), hk' y hy]
    rfl
  have kf : LinearMap.ker f ≤ S0 := by
    intro x hx
    rw [LinearMap.mem_ker, fx, Prod.mk_eq_zero] at hx
    have hxL : x ∈ L := by
      rw [← Submodule.Quotient.mk_eq_zero L]
      exact φ.map_eq_zero_iff.1 hx.1
    exact h1 x hxL hx.2
  have kf' : LinearMap.ker f' ≤ S0' := by
    intro y hy
    rw [LinearMap.mem_ker, fy, Prod.mk_eq_zero] at hy
    exact h1' y ((Submodule.Quotient.mk_eq_zero L').1 hy.1) hy.2
  let ι := S0.liftQ f hf
  let ι' := S0'.liftQ f' hf'
  have hι : Function.Injective ι := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ kf)
  have hι' : Function.Injective ι' :=
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ kf')
  have hr : LinearMap.range ι = LinearMap.range ι' := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := h2 x
      exact ⟨y, by rw [fx, fy, hy1, hy2]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := h3 y
      exact ⟨x, by rw [fx, fy, hx1, hx2]⟩
  let Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0') :=
    (LinearEquiv.ofInjective ι hι).trans
      ((LinearEquiv.ofEq _ _ hr).trans (LinearEquiv.ofInjective ι' hι').symm)
  have key : ∀ z, ι' (Ψ z) = ι z := by
    intro z
    have h := (LinearEquiv.ofInjective ι' hι').apply_symm_apply
      (LinearEquiv.ofEq _ _ hr (LinearEquiv.ofInjective ι hι z))
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨Ψ, fun x y => ?_⟩
  have e1 : ι (Submodule.Quotient.mk x) = f x := rfl
  have e2 : ι' (Submodule.Quotient.mk y) = f' y := rfl
  rw [← hι'.eq_iff, key, e1, e2, fx, fy, Prod.mk.injEq]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

theorem desc_abs {R P P' : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] (L S0 : Submodule R P) (L' S0' : Submodule R P')
    (Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0')) (hS : S0 ≤ L) (hS' : S0' ≤ L')
    (hrel : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → (x ∈ L ↔ y ∈ L')) :
    ∃ φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L'), ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  have hq' : S0' ≤ LinearMap.ker L'.mkQ := by rw [Submodule.ker_mkQ]; exact hS'
  have hq : S0 ≤ LinearMap.ker L.mkQ := by rw [Submodule.ker_mkQ]; exact hS
  let F : P →ₗ[R] P' ⧸ L' := (S0'.liftQ L'.mkQ hq').comp (Ψ.toLinearMap.comp S0.mkQ)
  let G : P' →ₗ[R] P ⧸ L := (S0.liftQ L.mkQ hq).comp (Ψ.symm.toLinearMap.comp S0'.mkQ)
  have hFv : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      F x = Submodule.Quotient.mk y := by
    intro x y h
    show (S0'.liftQ L'.mkQ hq') (Ψ (Submodule.Quotient.mk x)) = _
    rw [h]; rfl
  have hGv : ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      G y = Submodule.Quotient.mk x := by
    intro x y h
    show (S0.liftQ L.mkQ hq) (Ψ.symm (Submodule.Quotient.mk y)) = _
    rw [← h, Ψ.symm_apply_apply]; rfl
  have hF : L ≤ LinearMap.ker F := by
    intro x hx
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk x))
    rw [LinearMap.mem_ker, hFv x y hy.symm, Submodule.Quotient.mk_eq_zero]
    exact (hrel x y hy.symm).1 hx
  have hG : L' ≤ LinearMap.ker G := by
    intro y hy
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.symm (Submodule.Quotient.mk y))
    have hxy : Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
      rw [hx, Ψ.apply_symm_apply]
    rw [LinearMap.mem_ker, hGv x y hxy, Submodule.Quotient.mk_eq_zero]
    exact (hrel x y hxy).2 hy
  let φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L') :=
    LinearEquiv.ofLinearMap (L.liftQ F hF) (L'.liftQ G hG)
      (by
        apply LinearMap.ext
        intro c
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.symm (Submodule.Quotient.mk y))
        have hxy : Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
          rw [hx, Ψ.apply_symm_apply]
        show (L.liftQ F hF) (G y) = Submodule.Quotient.mk y
        rw [hGv x y hxy]
        exact hFv x y hxy)
      (by
        apply LinearMap.ext
        intro c
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk x))
        show (L'.liftQ G hG) (F x) = Submodule.Quotient.mk x
        rw [hFv x y hy.symm]
        exact hGv x y hy.symm)
  exact ⟨φ, fun x y h => hFv x y h⟩

theorem equiv_of_birel {α β : Type} (A : α → Prop) (B : β → Prop) (C : β → α → Prop)
    (c1 : ∀ a, A a → ∃ b, B b ∧ C b a) (c2 : ∀ b, B b → ∃ a, A a ∧ C b a)
    (c3 : ∀ b a₁ a₂, C b a₁ → C b a₂ → a₁ = a₂)
    (c4 : ∀ a b₁ b₂, B b₁ → B b₂ → C b₁ a → C b₂ a → b₁ = b₂) :
    Nonempty ({a // A a} ≃ {b // B b}) := by
  classical
  let f : {a // A a} → {b // B b} := fun a =>
    ⟨Classical.choose (c1 a.1 a.2), (Classical.choose_spec (c1 a.1 a.2)).1⟩
  have hf : ∀ a : {a // A a}, C (f a).1 a.1 := fun a => (Classical.choose_spec (c1 a.1 a.2)).2
  refine ⟨Equiv.ofBijective f ⟨fun a₁ a₂ h => ?_, fun b => ?_⟩⟩
  · apply Subtype.ext
    have h1 := hf a₁
    rw [h] at h1
    exact c3 _ _ _ h1 (hf a₂)
  · obtain ⟨a, ha, hC⟩ := c2 b.1 b.2
    exact ⟨⟨a, ha⟩, Subtype.ext (c4 a _ _ (f ⟨a, ha⟩).2 b.2 (hf ⟨a, ha⟩) hC)⟩

theorem sum_eq_zero_of_shift {α : Type} (E : Finset α) (Φ : α → ℂ) (S : α → α)
    (hS : Function.Injective S) (hE : ∀ q ∈ E, S q ∈ E) (ζ : ℂ) (hζ : ζ ≠ 1)
    (hΦ : ∀ q ∈ E, Φ (S q) = ζ * Φ q) : ∑ q ∈ E, Φ q = 0 := by
  classical
  have him : E.image S = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
      exact hE q hq
    · rw [Finset.card_image_of_injective _ hS]
  have h1 : ∑ q ∈ E, Φ q = ζ * ∑ q ∈ E, Φ q := by
    conv_lhs => rw [← him]
    rw [Finset.sum_image (fun a _ b _ h => hS h), Finset.mul_sum]
    exact Finset.sum_congr rfl hΦ
  have h2 : (1 - ζ) * ∑ q ∈ E, Φ q = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hζ
  · exact h

open Classical in
theorem sum_card_eq_zero {α X : Type} (F : Finset α) (Φ : α → ℂ) (rel : X → α → Prop)
    (hfin : ∀ q ∈ F, Finite {x // rel x q})
    (h0 : ∀ x, ∑ q ∈ F.filter (fun q => rel x q), Φ q = 0) :
    ∑ q ∈ F, (Nat.card {x // rel x q} : ℂ) * Φ q = 0 := by
  have hT : (⋃ q ∈ F, {x | rel x q}).Finite := by
    apply Set.Finite.biUnion F.finite_toSet
    intro q hq
    have : Finite ({x | rel x q} : Set X) := hfin q hq
    exact Set.toFinite {x | rel x q}
  let U : Finset X := hT.toFinset
  have hU : ∀ q ∈ F, ∀ x, rel x q → x ∈ U := by
    intro q hq x hx
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_biUnion hq hx
  have hc : ∀ q ∈ F, (Nat.card {x // rel x q} : ℂ) * Φ q =
      ∑ x ∈ U, if rel x q then Φ q else 0 := by
    intro q hq
    rw [Nat.subtype_card (U.filter (fun x => rel x q))
      (fun x => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hU q hq x h, h⟩⟩),
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hc, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  rw [← Finset.sum_filter]
  exact h0 x

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

section Mat

open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Lam_apply (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    abelian₂ R k Z x = msk k (Z⁻¹ *ᵥ coeLin R x) := by
  ext j
  simp only [abelian₂, LinearMap.pi_apply, msk]
  by_cases h : k < j.val
  · rw [if_pos h, if_pos h, A5x2.lamTil_fin]
  · rw [if_neg h, if_neg h]; rfl

theorem mem_colSpan (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    x ∈ colSpan R k Z ↔ ∃ t : Fin n → R, (∀ j : Fin n, k < j.val → t j = 0) ∧
      Z *ᵥ coeLin R t = coeLin R x := Iff.rfl

theorem isMirabolic_mul {p q : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) (hq : IsP R k q) :
    IsP R k (p * q) := by
  refine ⟨isUpUni_mul K hp.1 hq.1, fun a b hab => ?_⟩
  rw [Matrix.mul_apply]
  refine R.sum_mem fun l _ => ?_
  by_cases h1 : l < a
  · rw [up_zero hp.1 h1, zero_mul]; exact R.zero_mem
  by_cases h2 : b < l
  · rw [up_zero hq.1 h2, mul_zero]; exact R.zero_mem
  have h1' : a.val ≤ l.val := Fin.le_def.1 (not_lt.1 h1)
  have h2' : l.val ≤ b.val := Fin.le_def.1 (not_lt.1 h2)
  rcases hab with h | h
  · exact R.mul_mem (hp.2 a l (Or.inl h)) (hq.2 l b (Or.inl (by omega)))
  · exact R.mul_mem (hp.2 a l (Or.inr (by omega))) (hq.2 l b (Or.inr h))

theorem isP_one : IsP R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isUpUni_one K, fun a b _ => ?_⟩
  rw [Matrix.one_apply]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem isPP_one : IsPP R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isP_one R k, ?_⟩
  rw [inv_one]
  exact isP_one R k

theorem isPP_mul {p q : Matrix (Fin n) (Fin n) K} (hp : IsPP R k p) (hq : IsPP R k q) :
    IsPP R k (p * q) := by
  refine ⟨isMirabolic_mul R k hp.1 hq.1, ?_⟩
  rw [Matrix.mul_inv_rev]
  exact isMirabolic_mul R k hq.2 hp.2

theorem isPP_inv {p : Matrix (Fin n) (Fin n) K} (hp : IsPP R k p) : IsPP R k p⁻¹ := by
  refine ⟨hp.2, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv p (by simp [isUpUni_det K hp.1.1])]
  exact hp.1

theorem isPP_of_int {g : Matrix (Fin n) (Fin n) K} (hg : IsUpUni g) (hi : IsInt R g) :
    IsPP R k g :=
  ⟨⟨hg, fun a b _ => hi a b⟩, ⟨isUpUni_inv K hg, fun a b _ =>
    isInt_inv R hi (isUpUni_det K hg) a b⟩⟩

theorem isD_one : IsD R k (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨isUpUni_one K, fun a b => ?_, fun _ _ _ => rfl⟩
  rw [Matrix.one_apply]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem isD_mul {D E : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (hE : IsD R k E) :
    IsD R k (D * E) := by
  refine ⟨isUpUni_mul K hD.1 hE.1, isInt_mul R hD.2.1 hE.2.1, fun a b ha => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hD.2.2 a a ha, Matrix.one_apply_eq, one_mul, hE.2.2 a b ha]
  · intro l _ hl
    rw [hD.2.2 a l ha, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
  · simp

theorem isD_inv {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) : IsD R k D⁻¹ := by
  refine ⟨isUpUni_inv K hD.1, isInt_inv R hD.2.1 (isUpUni_det K hD.1), fun a b ha => ?_⟩
  have h1 : (D * D⁻¹) a b = (1 : Matrix (Fin n) (Fin n) K) a b := by
    rw [mul_inv_one_up hD.1]
  rw [← h1, Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hD.2.2 a a ha, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rw [hD.2.2 a l ha, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
  · simp

theorem isD_mulVec_int {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) {y : Fin n → K}
    (hy : ∀ j, y j ∈ R) : ∀ j, (D *ᵥ y) j ∈ R := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun l _ => R.mul_mem (hD.2.1 j l) (hy l)

theorem isD_mulVec_msk {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (y : Fin n → K) :
    D *ᵥ msk k y = msk k (D *ᵥ y) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, msk]
  by_cases h : k < j.val
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k < l.val
    · rw [if_pos hl]
    · have : l < j := by rw [Fin.lt_def]; omega
      rw [up_zero hD.1 this, zero_mul, zero_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : k < l.val
    · have : j ≠ l := fun e => h (e ▸ hl)
      rw [hD.2.2 j l (by omega), Matrix.one_apply_ne this, zero_mul]
    · rw [if_neg hl, mul_zero]

theorem lower_right_block_is_diagonal {p : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) : IsD R k (b22 k p) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    simp only [b22]
    split_ifs
    · exact up_zero hp.1 hab'
    · exact Matrix.one_apply_ne (ne_of_gt hab')
  · intro a
    simp only [b22]
    split_ifs
    · exact hp.1.2 a
    · exact Matrix.one_apply_eq a
  · intro a b
    simp only [b22]
    split_ifs with h
    · exact hp.2 a b (Or.inl h)
    · rw [Matrix.one_apply]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem
  · intro a b ha
    simp only [b22]
    rw [if_neg (by omega)]

theorem msk_mulVec {p : Matrix (Fin n) (Fin n) K} (hp : IsUpUni p) (y : Fin n → K) :
    msk k (p *ᵥ y) = b22 k p *ᵥ msk k y := by
  ext j
  simp only [Matrix.mulVec, dotProduct, msk, b22]
  by_cases h : k < j.val
  · simp only [if_pos h]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k < l.val
    · rw [if_pos hl]
    · have : l < j := by rw [Fin.lt_def]; omega
      rw [up_zero hp this, zero_mul, zero_mul]
  · simp only [if_neg h]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : k < l.val
    · have : j ≠ l := fun e => h (e ▸ hl)
      rw [Matrix.one_apply_ne this, zero_mul]
    · rw [if_neg hl, mul_zero]

theorem msk_msk (y : Fin n → K) : msk k (msk k y) = msk k y := by
  ext j
  simp only [msk]
  split_ifs <;> rfl

end Mat

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase

section Mat

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Lam_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R) :
    abelian₂ R k (Z₀ * p) x = b22 k p⁻¹ *ᵥ abelian₂ R k Z₀ x := by
  rw [Lam_apply, Lam_apply, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, msk_mulVec k hp.2.1]

theorem Lam_mul' (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R) :
    abelian₂ R k Z₀ x = b22 k p *ᵥ abelian₂ R k (Z₀ * p) x := by
  rw [Lam_apply, Lam_apply, ← msk_mulVec k hp.1.1, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, mul_inv_one_up hp.1.1, Matrix.one_mul]

theorem mat_low {q : Matrix (Fin n) (Fin n) K} (hq : IsP R k q) (t : Fin n → R)
    (ht : ∀ j : Fin n, k < j.val → t j = 0) :
    ∃ s : Fin n → R, (∀ j : Fin n, k < j.val → s j = 0) ∧ coeLin R s = q *ᵥ coeLin R t := by
  have hmem : ∀ a, (q *ᵥ coeLin R t) a ∈ R := by
    intro a
    simp only [Matrix.mulVec, dotProduct]
    refine R.sum_mem fun b _ => ?_
    rw [coeLin_apply]
    by_cases hb : b.val ≤ k
    · exact R.mul_mem (hq.2 a b (Or.inr hb)) (t b).2
    · rw [ht b (by omega)]; simp [R.zero_mem]
  refine ⟨fun a => ⟨_, hmem a⟩, fun j hj => ?_, ?_⟩
  · apply Subtype.ext
    show (q *ᵥ coeLin R t) j = 0
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [coeLin_apply]
    by_cases hb : b.val ≤ k
    · rw [up_zero hq.1 (show b < j from Fin.lt_def.2 (by omega)), zero_mul]
    · rw [ht b (by omega)]; simp
  · funext a
    rw [coeLin_apply]

theorem colSpan_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) :
    colSpan R k (Z₀ * p) = colSpan R k Z₀ := by
  ext x
  rw [mem_colSpan, mem_colSpan]
  constructor
  · rintro ⟨t, ht, e⟩
    obtain ⟨s, hs, es⟩ := mat_low R k hp.1 t ht
    exact ⟨s, hs, by rw [es, Matrix.mulVec_mulVec]; exact e⟩
  · rintro ⟨t, ht, e⟩
    obtain ⟨s, hs, es⟩ := mat_low R k hp.2 t ht
    refine ⟨s, hs, ?_⟩
    rw [es, Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_inv_one_up hp.1.1, Matrix.mul_one]
    exact e

theorem colSpan_le_latZ (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) :
    colSpan R k Z₀ ≤ latZ R (Z₀ * p) := by
  intro x hx
  rw [← colSpan_mul R k Z₀ p hp, mem_colSpan] at hx
  obtain ⟨t, _, e⟩ := hx
  exact (mem_latZ R _ x).2 ⟨t, e⟩

theorem Lam_colSpan (Z₀ : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (x : Fin n → R)
    (hx : x ∈ colSpan R k Z₀) : abelian₂ R k Z₀ x = 0 := by
  obtain ⟨t, ht, e⟩ := (mem_colSpan R k Z₀ x).1 hx
  rw [Lam_apply, ← e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  funext j
  simp only [msk, Pi.zero_apply]
  split_ifs with hj
  · rw [coeLin_apply, ht j hj]; rfl
  · rfl

theorem mat_det_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p) :
    IsUnit (Z₀ * p).det := by
  rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hd

theorem mat_Lam_mulVec (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (x t : Fin n → R)
    (e : Z *ᵥ coeLin R t = coeLin R x) : abelian₂ R k Z x = msk k (coeLin R t) := by
  rw [Lam_apply, ← e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

theorem mem_colSpan_of (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (x : Fin n → R) (hx : x ∈ latZ R (Z₀ * p)) (h0 : abelian₂ R k Z₀ x = 0) : x ∈ colSpan R k Z₀ := by
  obtain ⟨t, e⟩ := (mem_latZ R _ x).1 hx
  have h1 : abelian₂ R k (Z₀ * p) x = 0 := by rw [Lam_mul R k Z₀ p hp, h0, Matrix.mulVec_zero]
  rw [mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) x t e] at h1
  rw [← colSpan_mul R k Z₀ p hp, mem_colSpan]
  refine ⟨t, fun j hj => ?_, e⟩
  have h2 := congrFun h1 j
  simp only [msk, if_pos hj, Pi.zero_apply, coeLin_apply] at h2
  exact Subtype.ext h2

theorem Lam_latZ_int (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (x : Fin n → R) (hx : x ∈ latZ R (Z₀ * p)) : ∀ j, abelian₂ R k Z₀ x j ∈ R := by
  obtain ⟨t, e⟩ := (mem_latZ R _ x).1 hx
  rw [Lam_mul' R k Z₀ p hp, mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) x t e]
  refine isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.1) fun j => ?_
  simp only [msk]
  split_ifs
  · rw [coeLin_apply]; exact (t j).2
  · exact R.zero_mem

theorem exists_latZ_Lam (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (hZ : IsInt R (Z₀ * p)) (r : Fin n → K) (hr : ∀ j, r j ∈ R) (hr0 : msk k r = r) :
    ∃ z ∈ latZ R (Z₀ * p), abelian₂ R k Z₀ z = r := by
  have ht := isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.2) hr
  let t : Fin n → R := fun j => ⟨_, ht j⟩
  have et : coeLin R t = b22 k p⁻¹ *ᵥ r := by
    funext j; rw [coeLin_apply]
  let z : Fin n → R := liftR R (Z₀ * p) hZ *ᵥ t
  have ez : (Z₀ * p) *ᵥ coeLin R t = coeLin R z := by rw [coeLin_mulVec, liftR_map]
  refine ⟨z, (mem_latZ R _ z).2 ⟨t, ez⟩, ?_⟩
  rw [Lam_mul' R k Z₀ p hp, mat_Lam_mulVec R k _ (mat_det_mul R k Z₀ p hd hp) z t ez, et]
  conv_lhs => rw [← hr0]
  rw [← msk_mulVec k hp.2.1, msk_msk, ← msk_mulVec k hp.1.1, Matrix.mulVec_mulVec,
    mul_inv_one_up hp.1.1, Matrix.one_mulVec, hr0]

theorem lamTil_k_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (x : Fin n → R)
    (h0 : abelian₂ R k Z₀ x = 0) : lamTil R (Z₀ * p) k x = lamTil R Z₀ k x := by
  by_cases hk : k < n
  · have e1 := A5x2.lamTil_fin R (Z₀ * p) ⟨k, hk⟩ x
    have e2 := A5x2.lamTil_fin R Z₀ ⟨k, hk⟩ x
    simp only at e1 e2
    rw [e1, e2, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rw [Lam_apply] at h0
    generalize Z₀⁻¹ *ᵥ coeLin R x = y at h0 ⊢
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · rw [hp.2.1.2, one_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [up_zero hp.2.1 h, zero_mul]
      · have h2 := congrFun h0 b
        have hkb : k < b.val := Fin.lt_def.1 h
        simp only [msk, if_pos hkb, Pi.zero_apply] at h2
        rw [h2, mul_zero]
    · simp
  · rw [A5x2.lamTil_big R _ k (by omega), A5x2.lamTil_big R _ k (by omega)]

theorem latZ_mul_int (Z g : Matrix (Fin n) (Fin n) K) (hg : IsUpUni g) (hi : IsInt R g) :
    latZ R (Z * g) = latZ R Z := by
  ext x
  rw [mem_latZ, mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    refine ⟨liftR R g hi *ᵥ t, ?_⟩
    rw [coeLin_mulVec, liftR_map, Matrix.mulVec_mulVec]; exact e
  · rintro ⟨t, e⟩
    have hi' := isInt_inv R hi (isUpUni_det K hg)
    refine ⟨liftR R g⁻¹ hi' *ᵥ t, ?_⟩
    rw [coeLin_mulVec, liftR_map, Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_inv_one_up hg,
      Matrix.mul_one]
    exact e

theorem mat_add_vecMulVec (Z : Matrix (Fin n) (Fin n) K) (m β y : Fin n → K) :
    (Z + vecMulVec m β) *ᵥ y = Z *ᵥ y + (β ⬝ᵥ y) • m := by
  rw [Matrix.add_mulVec]
  congr 1
  funext a
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem mem_latZ_rank1 (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R)
    (β : Fin n → K) (hβ : ∀ b, β b ∈ R) (h0 : β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R m) = 0) (x : Fin n → R) :
    x ∈ latZ R (Z + vecMulVec (coeLin R m) β) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R Z := by
  rw [mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    rw [mat_add_vecMulVec] at e
    have hmem : β ⬝ᵥ coeLin R t ∈ R := by
      simp only [dotProduct]
      refine R.sum_mem fun b _ => ?_
      rw [coeLin_apply]
      exact R.mul_mem (hβ b) (t b).2
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · show β ⬝ᵥ coeLin R t = _
      rw [← e, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd,
        Matrix.one_mulVec, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, h0, smul_zero,
        add_zero]
    · rw [mem_latZ]
      refine ⟨t, ?_⟩
      rw [map_sub, map_smul, ← e, A5x2.smul_coe]
      simp
  · rintro ⟨r, hr, hx⟩
    obtain ⟨t, e⟩ := (mem_latZ R _ _).1 hx
    rw [map_sub, map_smul, A5x2.smul_coe] at e
    have ht : coeLin R t = Z⁻¹ *ᵥ coeLin R x - (r : K) • (Z⁻¹ *ᵥ coeLin R m) := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub, ← e, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
    have hb : β ⬝ᵥ coeLin R t = (r : K) := by
      rw [ht, dotProduct_sub, dotProduct_smul, h0, smul_zero, sub_zero, hr]
    refine ⟨t, ?_⟩
    rw [mat_add_vecMulVec, hb, e]
    simp

end Mat

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

section Cnt

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

noncomputable def cntaCoef {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (j : Fin n) : ℕ → R :=
  fun l => if h : l < n then ⟨D j ⟨l, h⟩, hD.2.1 _ _⟩ else 0

theorem cnta_coef_fin {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (j b : Fin n) :
    cntaCoef R k hD j b.val = ⟨D j b, hD.2.1 _ _⟩ := by
  simp [cntaCoef]

theorem cnta_Lam_coord (Z : Matrix (Fin n) (Fin n) K) (v : Fin n → R) (j : Fin n) :
    abelian₂ R k Z v j = if k < j.val then lamTil R Z j.val v else 0 := by
  simp only [abelian₂, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem cnta_row {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (j : Fin n) (hj : k < j.val) (v : Fin n → R) :
    (Submodule.Quotient.mk ((D *ᵥ abelian₂ R k Z v) j) : KR R) =
      lamN R Z j.val v + ∑ l ∈ Finset.Ioo j.val n, cntaCoef R k hD j l • lamN R Z l v := by
  have h1 : (Submodule.Quotient.mk ((D *ᵥ abelian₂ R k Z v) j) : KR R) =
      ∑ b : Fin n, cntaCoef R k hD j b.val • lamN R Z b.val v := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Submodule.mkQ_apply, cnta_coef_fin, cnta_Lam_coord]
    by_cases hb : k < b.val
    · rw [if_pos hb]
      show _ = _ • (Submodule.Quotient.mk (lamTil R Z b.val v) : KR R)
      rw [A5x3.smul_mk]
    · have hbj : b < j := by rw [Fin.lt_def]; omega
      have h0 : D j b = 0 := Formalism.DoubleCosetMeasures.P.Phase.up_zero hD.1 hbj
      have h0' : (⟨D j b, hD.2.1 _ _⟩ : R) = 0 := Subtype.ext h0
      rw [if_neg hb, h0', mul_zero, zero_smul]
      rfl
  rw [h1, Fin.sum_univ_eq_sum_range (fun l => cntaCoef R k hD j l • lamN R Z l v) n]
  have h2 : ∑ l ∈ Finset.range n, cntaCoef R k hD j l • lamN R Z l v =
      ∑ l ∈ Finset.Ico j.val n, cntaCoef R k hD j l • lamN R Z l v := by
    symm
    apply Finset.sum_subset
    · intro l hl
      rw [Finset.mem_Ico] at hl
      exact Finset.mem_range.2 hl.2
    · intro l hl hl'
      rw [Finset.mem_range] at hl
      rw [Finset.mem_Ico] at hl'
      have hlj : (⟨l, hl⟩ : Fin n) < j := by rw [Fin.lt_def]; simp only; omega
      have h0 : D j ⟨l, hl⟩ = 0 := Formalism.DoubleCosetMeasures.P.Phase.up_zero hD.1 hlj
      have := cnta_coef_fin R k hD j ⟨l, hl⟩
      simp only at this
      rw [this]
      have h0' : (⟨D j ⟨l, hl⟩, hD.2.1 _ _⟩ : R) = 0 := Subtype.ext h0
      rw [h0', zero_smul]
  rw [h2, ← Finset.Ioo_insert_left j.2, Finset.sum_insert (by simp)]
  congr 1
  rw [cnta_coef_fin]
  have h1' : (⟨D j j, hD.2.1 _ _⟩ : R) = 1 := Subtype.ext (hD.1.2 j)
  rw [h1', one_smul]

theorem inTT_iff (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') :
    InTT R (k + 1) Z Z' φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z' v' - D *ᵥ abelian₂ R k Z v) j ∈ R := by
  constructor
  · intro hT
    have hex : ∀ j : Fin n, ∃ a : ℕ → R, k < j.val → ∀ (v v' : Fin n → R),
        φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
          lamN R Z' j.val v' = lamN R Z j.val v +
            ∑ l ∈ Finset.Ioo j.val n, a l • lamN R Z l v := by
      intro j
      by_cases hj : k < j.val
      · obtain ⟨a, ha⟩ := hT j.val hj j.2
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose α hα using hex
    let D : Matrix (Fin n) (Fin n) K := fun a b =>
      if k < a.val then (if a = b then 1 else if a < b then ((α a b.val : R) : K) else 0)
      else (1 : Matrix (Fin n) (Fin n) K) a b
    have hD : IsD R k D := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro i j hji
        have hji' : j < i := hji
        simp only [D]
        by_cases hi : k < i.val
        · rw [if_pos hi, if_neg hji'.ne', if_neg (not_lt.2 hji'.le)]
        · rw [if_neg hi, Matrix.one_apply_ne hji'.ne']
      · intro a
        simp only [D]
        by_cases ha : k < a.val
        · rw [if_pos ha, if_pos trivial]
        · rw [if_neg ha, Matrix.one_apply_eq]
      · intro a b
        simp only [D]
        split_ifs with h1 h2 h3
        · exact R.one_mem
        · exact (α a b.val).2
        · exact R.zero_mem
        · rw [Matrix.one_apply]
          split_ifs
          · exact R.one_mem
          · exact R.zero_mem
      · intro a b ha
        simp only [D]
        rw [if_neg (by omega)]
    refine ⟨D, hD, fun v v' hv j => ?_⟩
    by_cases hj : k < j.val
    · rw [Pi.sub_apply, ← A5x3.mk_eq_mk, cnta_row R k hD Z j hj v, cnta_Lam_coord, if_pos hj]
      show lamN R Z' j.val v' = _
      rw [hα j hj v v' hv]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_Ioo] at hl
      congr 1
      have := cnta_coef_fin R k hD j ⟨l, hl.2⟩
      simp only at this
      rw [this]
      apply Subtype.ext
      have hjl : j < (⟨l, hl.2⟩ : Fin n) := by rw [Fin.lt_def]; exact hl.1
      simp only [D]
      rw [if_pos hj, if_neg hjl.ne, if_pos hjl]
    · rw [Lam_apply, Lam_apply, isD_mulVec_msk R k hD]
      simp [msk, hj, R.zero_mem]
  · rintro ⟨D, hD, h⟩ j hkj hjn
    refine ⟨cntaCoef R k hD ⟨j, hjn⟩, fun v v' hv => ?_⟩
    have hj : k < (⟨j, hjn⟩ : Fin n).val := hkj
    have h1 := h v v' hv ⟨j, hjn⟩
    rw [Pi.sub_apply, ← A5x3.mk_eq_mk, cnta_row R k hD Z ⟨j, hjn⟩ hj v, cnta_Lam_coord,
      if_pos hj] at h1
    exact h1

theorem inTT_iff_base (Z₀ Z₀' p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p)
    (hp' : IsPP R k p') (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) :
    InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ↔ ∃ D, IsD R k D ∧ ∀ v v' : Fin n → R,
      φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z₀' v' - D *ᵥ abelian₂ R k Z₀ v) j ∈ R := by
  rw [inTT_iff]
  constructor
  · rintro ⟨D, hD, h⟩
    refine ⟨b22 k p' * D * b22 k p⁻¹,
      isD_mul R k (isD_mul R k (lower_right_block_is_diagonal R k hp'.1) hD) (lower_right_block_is_diagonal R k hp.2), fun v v' hv => ?_⟩
    have e : abelian₂ R k Z₀' v' - (b22 k p' * D * b22 k p⁻¹) *ᵥ abelian₂ R k Z₀ v =
        b22 k p' *ᵥ (abelian₂ R k (Z₀' * p') v' - D *ᵥ abelian₂ R k (Z₀ * p) v) := by
      rw [Matrix.mulVec_sub, ← Lam_mul' R k Z₀' p' hp' v', Lam_mul R k Z₀ p hp v,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e]
    exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp'.1) (h v v' hv)
  · rintro ⟨D, hD, h⟩
    refine ⟨b22 k p'⁻¹ * D * b22 k p,
      isD_mul R k (isD_mul R k (lower_right_block_is_diagonal R k hp'.2) hD) (lower_right_block_is_diagonal R k hp.1), fun v v' hv => ?_⟩
    have e : abelian₂ R k (Z₀' * p') v' - (b22 k p'⁻¹ * D * b22 k p) *ᵥ abelian₂ R k (Z₀ * p) v =
        b22 k p'⁻¹ *ᵥ (abelian₂ R k Z₀' v' - D *ᵥ abelian₂ R k Z₀ v) := by
      rw [Matrix.mulVec_sub, ← Lam_mul R k Z₀' p' hp' v', Lam_mul' R k Z₀ p hp v,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e]
    exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp'.2) (h v v' hv)

end Cnt

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

section Cnt

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem cnt_Lam_coord (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) (j : Fin n) :
    abelian₂ R k Z x j = if k < j.val then lamTil R Z j.val x else 0 := by
  simp only [abelian₂, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem cnt_msk_sub (a b : Fin n → K) : msk k (a - b) = msk k a - msk k b := by
  ext j
  simp only [msk, Pi.sub_apply]
  split_ifs <;> simp

theorem cnt_msk_Lam (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    msk k (abelian₂ R k Z x) = abelian₂ R k Z x := by
  rw [Lam_apply, msk_msk]

theorem cnt_msk_D {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (x : Fin n → R) : msk k (D *ᵥ abelian₂ R k Z x) = D *ᵥ abelian₂ R k Z x := by
  rw [Lam_apply, isD_mulVec_msk R k hD, msk_msk]

theorem cnt_nrm_exists (Z₀ : Matrix (Fin n) (Fin n) K)
    (D : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) :
    ∃ D' : {D : Matrix (Fin n) (Fin n) K // IsD R k D}, Nrm R k Z₀ D' ∧
      ∀ (x : Fin n → R) (j : Fin n), ((D'.1 - D.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R := by
  refine ⟨Quotient.out (Quotient.mk (dRel R k Z₀) D), ?_, ?_⟩
  · unfold Nrm; rw [Quotient.out_eq]
  · exact Quotient.exact (Quotient.out_eq (Quotient.mk (dRel R k Z₀) D))

theorem cnt_nrm_unique (Z₀ : Matrix (Fin n) (Fin n) K)
    (D₁ D₂ : {D : Matrix (Fin n) (Fin n) K // IsD R k D}) (h₁ : Nrm R k Z₀ D₁)
    (h₂ : Nrm R k Z₀ D₂)
    (h : ∀ (x : Fin n → R) (j : Fin n), ((D₁.1 - D₂.1) *ᵥ abelian₂ R k Z₀ x) j ∈ R) : D₁ = D₂ := by
  unfold Nrm at h₁ h₂
  rw [← h₁, ← h₂]
  congr 1
  exact Quotient.sound (s := dRel R k Z₀) h

theorem cnt_det_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p) :
    IsUnit (Z₀ * p).det := by
  rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hd

theorem cnt_bad_iff (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det)
    (p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (hp' : IsPP R k p')
    (hZ : IsInt R (Z₀ * p)) (hfin : Finite (coker R (Z₀ * p)))
    (φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p')) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀')
    (hC : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
    (hT : InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ) (D : Matrix (Fin n) (Fin n) K)
    (hL : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      abelian₂ R k Z₀' y = D *ᵥ abelian₂ R k Z₀ x) :
    ¬ InTT R k (Z₀ * p) (Z₀' * p') φ ↔
      ∃ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
        abelian₂ R k Z₀ x = 0 ∧ lamTil R Z₀' k y - lamTil R Z₀ k x ∉ R := by
  have hdZ := cnt_det_mul R k Z₀ p hd hp
  have hdZ' := cnt_det_mul R k Z₀' p' hd' hp'
  have hstep := Formalism.FourierDecayAlt.P.triple_form_recursion K R ψ hsd n (Z₀ * p) (Z₀' * p') hdZ hdZ' hfin φ k
    (by omega) hT
  rw [hstep]
  constructor
  · intro h
    push Not at h
    obtain ⟨v, v', hv, hker, hne⟩ := h
    have hint : ∀ j, abelian₂ R k (Z₀ * p) v j ∈ R := by
      intro j
      rw [cnt_Lam_coord]
      split_ifs with hj
      · exact (A5x3.mk_eq_zero R _).1 (hker j.val hj)
      · exact R.zero_mem
    have hint0 : ∀ j, abelian₂ R k Z₀ v j ∈ R := by
      rw [Lam_mul' R k Z₀ p hp v]
      exact isD_mulVec_int R k (lower_right_block_is_diagonal R k hp.1) hint
    obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀ p hd hp hZ _ hint0 (cnt_msk_Lam R k Z₀ v)
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk (v - z)))
    have hx0 : abelian₂ R k Z₀ (v - z) = 0 := by rw [map_sub, hzL, sub_self]
    have hy0 : abelian₂ R k Z₀' y = 0 := by rw [hL _ _ hy.symm, hx0, Matrix.mulVec_zero]
    refine ⟨v - z, y, hy.symm, hx0, ?_⟩
    intro hmem
    apply hne
    have e1 : φ (Submodule.Quotient.mk (v - z)) = Submodule.Quotient.mk y := hC _ _ hy.symm
    have e2 : (Submodule.Quotient.mk (v - z) : coker R (Z₀ * p)) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hz, sub_zero]
    rw [e2, hv] at e1
    have e3 : v' - y ∈ latZ R (Z₀' * p') := (Submodule.Quotient.eq _).1 e1
    have e4 : lamN R (Z₀' * p') k v' = lamN R (Z₀' * p') k y := by
      have := A5x2.lamN_latZ R _ hdZ' k e3
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    have e5 : lamN R (Z₀ * p) k v = lamN R (Z₀ * p) k (v - z) := by
      have := A5x2.lamN_latZ R _ hdZ k hz
      rw [LinearMap.mem_ker] at this
      rw [map_sub, this, sub_zero]
    rw [e4, e5]
    show (Submodule.Quotient.mk (lamTil R (Z₀' * p') k y) : KR R) =
      Submodule.Quotient.mk (lamTil R (Z₀ * p) k (v - z))
    rw [lamTil_k_mul R k Z₀' p' hp' y hy0, lamTil_k_mul R k Z₀ p hp _ hx0]
    exact (A5x3.mk_eq_mk R _ _).2 hmem
  · rintro ⟨x, y, hxy, hx0, hnot⟩ h
    apply hnot
    have hy0 : abelian₂ R k Z₀' y = 0 := by rw [hL _ _ hxy, hx0, Matrix.mulVec_zero]
    have hker : ∀ j, k < j → lamN R (Z₀ * p) j x = 0 := by
      intro j hj
      by_cases hjn : j < n
      · have h1 : abelian₂ R k (Z₀ * p) x = 0 := by
          rw [Lam_mul R k Z₀ p hp, hx0, Matrix.mulVec_zero]
        have h2 := congrFun h1 ⟨j, hjn⟩
        rw [cnt_Lam_coord, if_pos hj] at h2
        show (Submodule.Quotient.mk (lamTil R (Z₀ * p) j x) : KR R) = 0
        rw [(A5x3.mk_eq_zero R _)]
        simp only at h2
        rw [h2]; exact R.zero_mem
      · rw [A5x2.lamN_big R _ j (by omega)]; rfl
    have h3 : (Submodule.Quotient.mk (lamTil R (Z₀' * p') k y) : KR R) =
        Submodule.Quotient.mk (lamTil R (Z₀ * p) k x) := h x y (hC _ _ hxy) hker
    rw [lamTil_k_mul R k Z₀' p' hp' y hy0, lamTil_k_mul R k Z₀ p hp _ hx0] at h3
    exact (A5x3.mk_eq_mk R _ _).1 h3

theorem countId (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det)
    (he : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀⁻¹ a b = 0)
    (he' : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀'⁻¹ a b = 0)
    (p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (hp' : IsPP R k p')
    (hZ : IsInt R (Z₀ * p)) (hZ' : IsInt R (Z₀' * p')) (hfin : Finite (coker R (Z₀ * p))) :
    Nonempty ({φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') //
        φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
          ¬ InTT R k (Z₀ * p) (Z₀' * p') φ} ≃
      {Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀' // GB R k Z₀ Z₀' Ψ ∧
        Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p'))}) := by
  have hdZ := cnt_det_mul R k Z₀ p hd hp
  have hdZ' := cnt_det_mul R k Z₀' p' hd' hp'
  have hn : 0 < n := by omega
  have hLe : abelian₂ R k Z₀ (eLast R) = 0 := by
    ext j
    rw [cnt_Lam_coord]
    split_ifs with hj
    · rw [A5x2.lamTil_eLast R Z₀ j ⟨n - 1, by omega⟩ (by simp only; omega)]
      exact he j _ hj (by simp only; omega)
    · rfl
  have hLe' : abelian₂ R k Z₀' (eLast R) = 0 := by
    ext j
    rw [cnt_Lam_coord]
    split_ifs with hj
    · rw [A5x2.lamTil_eLast R Z₀' j ⟨n - 1, by omega⟩ (by simp only; omega)]
      exact he' j _ hj (by simp only; omega)
    · rfl
  apply equiv_of_birel
    (fun φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') =>
      φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
          ¬ InTT R k (Z₀ * p) (Z₀' * p') φ)
    (fun Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀' => GB R k Z₀ Z₀' Ψ ∧
        Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p')))
    (fun Ψ φ => ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
  ·
    rintro φ ⟨hiso, hT, hnT⟩
    obtain ⟨D₁, hD₁, hD₁r⟩ := (inTT_iff_base R k Z₀ Z₀' p p' hp hp' φ).1 hT
    obtain ⟨D, hN, hDD⟩ := cnt_nrm_exists R k Z₀ ⟨D₁, hD₁⟩
    have hDr : ∀ v v' : Fin n → R, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z₀' v' - D.1 *ᵥ abelian₂ R k Z₀ v) j ∈ R := by
      intro v v' h j
      have h1 := hD₁r v v' h j
      have h2 := hDD v j
      have e : (abelian₂ R k Z₀' v' - D.1 *ᵥ abelian₂ R k Z₀ v) j =
          (abelian₂ R k Z₀' v' - D₁ *ᵥ abelian₂ R k Z₀ v) j - ((D.1 - D₁) *ᵥ abelian₂ R k Z₀ v) j := by
        rw [Matrix.sub_mulVec]; simp only [Pi.sub_apply]; ring
      rw [e]; exact R.sub_mem h1 h2
    have hDdet : IsUnit D.1.det := by rw [isUpUni_det K D.2.1]; exact isUnit_one
    have hDi := isD_inv R k D.2
    have h1 : ∀ x ∈ latZ R (Z₀ * p),
        (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) = 0 → x ∈ colSpan R k Z₀ := by
      intro x hx h0
      have h0' : D.1 *ᵥ abelian₂ R k Z₀ x = 0 := h0
      have h00 : abelian₂ R k Z₀ x = 0 := by
        have := congrArg (fun y => D.1⁻¹ *ᵥ y) h0'
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hDdet] using this
      exact mem_colSpan_of R k Z₀ p hd hp x hx h00
    have h2 : ∀ x : Fin n → R, ∃ y : Fin n → R,
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
          abelian₂ R k Z₀' y = (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) := by
      intro x
      obtain ⟨y0, hy0⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
      have hr := hDr x y0 hy0.symm
      have hm : msk k (abelian₂ R k Z₀' y0 - D.1 *ᵥ abelian₂ R k Z₀ x) =
          abelian₂ R k Z₀' y0 - D.1 *ᵥ abelian₂ R k Z₀ x := by
        rw [cnt_msk_sub, cnt_msk_Lam, cnt_msk_D R k D.2]
      obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀' p' hd' hp' hZ' _ hr hm
      refine ⟨y0 - z, ?_, ?_⟩
      · rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hz, sub_zero, hy0]
      · rw [map_sub, hzL, sub_sub_cancel]; rfl
    have h3 : ∀ y : Fin n → R, ∃ x : Fin n → R,
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
          abelian₂ R k Z₀' y = (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) := by
      intro y
      obtain ⟨x0, hx0⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (Submodule.Quotient.mk y))
      have hx0' : φ (Submodule.Quotient.mk x0) = Submodule.Quotient.mk y := by
        rw [hx0, φ.apply_symm_apply]
      have hr := hDr x0 y hx0'
      have hm : msk k (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0) =
          abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0 := by
        rw [cnt_msk_sub, cnt_msk_Lam, cnt_msk_D R k D.2]
      have hr1 := isD_mulVec_int R k hDi hr
      have hm1 : msk k (D.1⁻¹ *ᵥ (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0)) =
          D.1⁻¹ *ᵥ (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0) := by
        rw [← isD_mulVec_msk R k hDi, hm]
      obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀ p hd hp hZ _ hr1 hm1
      refine ⟨x0 + z, ?_, ?_⟩
      · rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hz, add_zero, hx0']
      · show _ = D.1 *ᵥ abelian₂ R k Z₀ (x0 + z)
        rw [map_add, hzL, Matrix.mulVec_add, Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ hDdet, Matrix.one_mulVec, add_sub_cancel]
    obtain ⟨Ψ, hΨ⟩ := lift_abs (latZ R (Z₀ * p)) (colSpan R k Z₀) (latZ R (Z₀' * p'))
      (colSpan R k Z₀') (abelian₂ R k Z₀) (abelian₂ R k Z₀') (D.1.mulVecLin.restrictScalars R) φ
      (colSpan_le_latZ R k Z₀ p hp) (colSpan_le_latZ R k Z₀' p' hp') (Lam_colSpan R k Z₀ hd)
      (Lam_colSpan R k Z₀' hd') h1 (mem_colSpan_of R k Z₀' p' hd' hp') h2 h3
    have hC : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := fun x y h => ((hΨ x y).1 h).1
    have hL : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        abelian₂ R k Z₀' y = D.1 *ᵥ abelian₂ R k Z₀ x := fun x y h => ((hΨ x y).1 h).2
    refine ⟨Ψ, ⟨⟨?_, ⟨D, hN, hL⟩, ?_⟩, ?_⟩, hC⟩
    · exact (hΨ _ _).2 ⟨hiso.1, by rw [hLe', hLe, map_zero]⟩
    · exact (cnt_bad_iff R k ψ hsd hk Z₀ Z₀' hd hd' p p' hp hp' hZ hfin φ Ψ hC hT D.1 hL).1 hnT
    · intro x y h
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero (latZ R (Z₀' * p')),
        ← hC x y h]
      exact (LinearEquiv.map_eq_zero_iff φ).symm
  ·
    rintro Ψ ⟨hG, hR⟩
    obtain ⟨φ, hφ⟩ := desc_abs (latZ R (Z₀ * p)) (colSpan R k Z₀) (latZ R (Z₀' * p'))
      (colSpan R k Z₀') Ψ (colSpan_le_latZ R k Z₀ p hp) (colSpan_le_latZ R k Z₀' p' hp') hR
    obtain ⟨D, hN, hL⟩ := hG.lift
    have hT : InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ := by
      refine (inTT_iff_base R k Z₀ Z₀' p p' hp hp' φ).2 ⟨D.1, D.2, fun v v' h j => ?_⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk v))
      have h1 := hφ v y hy.symm
      rw [h] at h1
      have h2 : v' - y ∈ latZ R (Z₀' * p') := (Submodule.Quotient.eq _).1 h1
      have h3 := Lam_latZ_int R k Z₀' p' hd' hp' _ h2 j
      rw [map_sub, hL v y hy.symm] at h3
      exact h3
    refine ⟨φ, ⟨⟨hφ _ _ hG.e, ?_⟩, hT,
      (cnt_bad_iff R k ψ hsd hk Z₀ Z₀' hd hd' p p' hp hp' hZ hfin φ Ψ hφ hT D.1 hL).2 hG.bad⟩, hφ⟩
    intro v v' h
    rw [A5x2.lamLin_eq R _ hn, A5x2.lamLin_eq R _ hn]
    obtain ⟨a, ha⟩ := hT (n - 1) (by omega) (by omega)
    rw [ha v v' h]
    have hE : Finset.Ioo (n - 1) n = ∅ := by
      ext l; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [hE, Finset.sum_empty, add_zero]
  · intro Ψ φ₁ φ₂ h₁ h₂
    apply LinearEquiv.ext
    intro c
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk v))
    rw [h₁ v y hy.symm, h₂ v y hy.symm]
  · rintro φ Ψ₁ Ψ₂ ⟨hG₁, -⟩ ⟨hG₂, -⟩ h₁ h₂
    obtain ⟨D₁, hN₁, hL₁⟩ := hG₁.lift
    obtain ⟨D₂, hN₂, hL₂⟩ := hG₂.lift
    have key : ∀ x y₁ y₂ : Fin n → R, Ψ₁ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y₁ →
        Ψ₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y₂ →
        y₁ - y₂ ∈ latZ R (Z₀' * p') := by
      intro x y₁ y₂ e₁ e₂
      rw [← Submodule.Quotient.eq, ← h₁ x y₁ e₁, ← h₂ x y₂ e₂]
    have hDeq : D₁ = D₂ := by
      refine cnt_nrm_unique R k Z₀ D₁ D₂ hN₁ hN₂ (fun x j => ?_)
      obtain ⟨y₁, e₁⟩ := Submodule.Quotient.mk_surjective _ (Ψ₁ (Submodule.Quotient.mk x))
      obtain ⟨y₂, e₂⟩ := Submodule.Quotient.mk_surjective _ (Ψ₂ (Submodule.Quotient.mk x))
      have h3 := Lam_latZ_int R k Z₀' p' hd' hp' _ (key x y₁ y₂ e₁.symm e₂.symm) j
      rw [map_sub, hL₁ x y₁ e₁.symm, hL₂ x y₂ e₂.symm, ← Matrix.sub_mulVec] at h3
      exact h3
    apply LinearEquiv.ext
    intro c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨y₁, e₁⟩ := Submodule.Quotient.mk_surjective _ (Ψ₁ (Submodule.Quotient.mk x))
    obtain ⟨y₂, e₂⟩ := Submodule.Quotient.mk_surjective _ (Ψ₂ (Submodule.Quotient.mk x))
    rw [← e₁, ← e₂, Submodule.Quotient.eq]
    apply mem_colSpan_of R k Z₀' p' hd' hp' _ (key x y₁ y₂ e₁.symm e₂.symm)
    rw [map_sub, hL₁ x y₁ e₁.symm, hL₂ x y₂ e₂.symm, hDeq, sub_self]

end Cnt

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

section Shf

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem shf_isP (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : IsP R k (1 + vecMulVec ξ β) := by
  have key : ∀ a b : Fin n, (k < a.val ∨ b.val ≤ k) → vecMulVec ξ β a b = 0 := by
    intro a b h
    rcases h with h | h
    · simp [vecMulVec_apply, hξ a h]
    · simp [vecMulVec_apply, hβ b h]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    have h0 : vecMulVec ξ β a b = 0 := by
      apply key
      have := Fin.lt_def.1 hab'
      omega
    rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_ne hab'.ne']
  · intro a
    have h0 : vecMulVec ξ β a a = 0 := key a a (by omega)
    rw [Matrix.add_apply, h0, add_zero, Matrix.one_apply_eq]
  · intro a b h
    rw [Matrix.add_apply, key a b h, add_zero]
    by_cases hab : a = b
    · rw [hab, Matrix.one_apply_eq]; exact R.one_mem
    · rw [Matrix.one_apply_ne hab]; exact R.zero_mem

theorem shf_dot_zero (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : β ⬝ᵥ ξ = 0 := by
  simp only [dotProduct]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h : k < a.val
  · rw [hξ a h, mul_zero]
  · rw [hβ a (by omega), zero_mul]

theorem shf_inv (ξ β : Fin n → K) (h : β ⬝ᵥ ξ = 0) :
    (1 + vecMulVec ξ β)⁻¹ = 1 + vecMulVec (-ξ) β := by
  apply Matrix.inv_eq_right_inv
  have h2 : vecMulVec ξ β * vecMulVec ξ β = 0 := by
    rw [Matrix.mul_vecMulVec]
    have : vecMulVec ξ β *ᵥ ξ = 0 := by
      ext a
      simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.zero_apply]
      have : ∑ l, ξ a * β l * ξ l = ξ a * (β ⬝ᵥ ξ) := by
        simp only [dotProduct, Finset.mul_sum, mul_assoc]
      rw [this, h, mul_zero]
    rw [this]
    ext a b
    simp [vecMulVec_apply]
  have h3 : vecMulVec (-ξ) β = - vecMulVec ξ β := by
    ext a b
    simp [vecMulVec_apply]
  rw [h3, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_neg, h2]
  simp

theorem shf_isPP (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : IsPP R k (1 + vecMulVec ξ β) := by
  refine ⟨shf_isP R k ξ β hξ hβ, ?_⟩
  rw [shf_inv ξ β (shf_dot_zero k ξ β hξ hβ)]
  exact shf_isP R k (-ξ) β (fun j hj => by rw [Pi.neg_apply, hξ j hj, neg_zero]) hβ

theorem shf_sUp (ξ β : Fin n → K) (hξ : ∀ j : Fin n, k < j.val → ξ j = 0)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) (r c : Fin n) (hr : r.val = k) (hc : c.val = k + 1) :
    sUp (1 + vecMulVec ξ β) = ξ r * β c := by
  unfold sUp
  rw [Finset.sum_eq_single r]
  · have h : r.val + 1 < n := by rw [hr, ← hc]; exact c.2
    rw [dif_pos h]
    have e : (⟨r.val + 1, h⟩ : Fin n) = c := Fin.ext (by simp [hr, hc])
    rw [e]
    have hne : r ≠ c := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, vecMulVec_apply]
  · intro j _ hj
    by_cases h : j.val + 1 < n
    · rw [dif_pos h]
      have hne : j ≠ ⟨j.val + 1, h⟩ := by
        intro h'
        have := congrArg Fin.val h'
        simp at this
      have h0 : ξ j * β ⟨j.val + 1, h⟩ = 0 := by
        rcases lt_trichotomy j.val k with h1 | h1 | h1
        · rw [hβ ⟨j.val + 1, h⟩ (by simp only; omega), mul_zero]
        · exact absurd (Fin.ext (h1.trans hr.symm)) hj
        · rw [hξ j h1, zero_mul]
      rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, vecMulVec_apply, h0]
    · rw [dif_neg h]
  · simp

theorem shf_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (m : Fin n → R)
    (β : Fin n → K) :
    Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p) =
      Z₀ * p + vecMulVec (coeLin R m) (β ᵥ* p) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

theorem shf_vecMul_int {p : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) (β : Fin n → K)
    (hβi : ∀ b, β b ∈ R) (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : ∀ b, (β ᵥ* p) b ∈ R := by
  intro b
  simp only [Matrix.vecMul, dotProduct]
  refine R.sum_mem fun a _ => ?_
  by_cases h : k < a.val
  · exact R.mul_mem (hβi a) (hp.2 a b (Or.inl h))
  · rw [hβ a (by omega), zero_mul]; exact R.zero_mem

theorem shf_dot (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsUpUni p) (β v : Fin n → K) :
    (β ᵥ* p) ⬝ᵥ ((Z₀ * p)⁻¹ *ᵥ v) = β ⬝ᵥ (Z₀⁻¹ *ᵥ v) := by
  have hdp : IsUnit p.det := by rw [isUpUni_det K hp]; exact isUnit_one
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdp, Matrix.one_mulVec]

theorem shf_Lam_zero (Z₀ : Matrix (Fin n) (Fin n) K) (m : Fin n → R) (h : abelian₂ R k Z₀ m = 0) :
    ∀ j : Fin n, k < j.val → (Z₀⁻¹ *ᵥ coeLin R m) j = 0 := by
  intro j hj
  have := congrFun h j
  rw [Lam_apply] at this
  simpa [msk, hj] using this

theorem shf_isInt (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (hZ : IsInt R (Z₀ * p)) (m : Fin n → R) (β : Fin n → K) (hβi : ∀ b, β b ∈ R)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) :
    IsInt R (Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p)) := by
  rw [shf_mul R Z₀ p hd m β]
  intro a b
  rw [Matrix.add_apply, vecMulVec_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
  exact R.add_mem (hZ a b) (R.mul_mem (m a).2 (shf_vecMul_int R k hp.1 β hβi hβ b))

theorem shf_mem (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (m : Fin n → R) (hm : abelian₂ R k Z₀ m = 0) (β : Fin n → K) (hβi : ∀ b, β b ∈ R)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) (x : Fin n → R) :
    x ∈ latZ R (Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p)) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R (Z₀ * p) := by
  have hdp : IsUnit (Z₀ * p).det := by
    rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hd
  rw [shf_mul R Z₀ p hd m β, mem_latZ_rank1 R (Z₀ * p) hdp m (β ᵥ* p)
    (shf_vecMul_int R k hp.1 β hβi hβ)
    (by rw [shf_dot Z₀ p hp.1.1]; exact shf_dot_zero k _ β (shf_Lam_zero R k Z₀ m hm) hβ) x,
    shf_dot Z₀ p hp.1.1]

theorem shiftData (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det) (Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀') (hΨ : GB R k Z₀ Z₀' Ψ) :
    ∃ σ σ' : Matrix (Fin n) (Fin n) K, IsPP R k σ ∧ IsPP R k σ' ∧ ψ (sUp σ - sUp σ') ≠ 1 ∧
      ∀ p p' : Matrix (Fin n) (Fin n) K, IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) →
        IsInt R (Z₀' * p') → Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p')) →
        IsInt R (Z₀ * (σ * p)) ∧ IsInt R (Z₀' * (σ' * p')) ∧
          Rel R Ψ (latZ R (Z₀ * (σ * p))) (latZ R (Z₀' * (σ' * p'))) := by
  obtain ⟨D, _, hL⟩ := hΨ.lift
  obtain ⟨x0, y0, hxy, hx0, hbad⟩ := hΨ.bad
  have hex : ∃ r ∈ R, ψ ((lamTil R Z₀' k y0 - lamTil R Z₀ k x0) * r) ≠ 1 := by
    by_contra hcon
    refine hbad ((hsd _).1 fun r hr => ?_)
    by_contra h
    exact hcon ⟨r, hr, h⟩
  obtain ⟨r0, hr0, hψ⟩ := hex
  let ρ : R := ⟨r0, hr0⟩
  let m : Fin n → R := ρ • x0
  let m' : Fin n → R := ρ • y0
  have hmm : Ψ (Submodule.Quotient.mk m) = Submodule.Quotient.mk m' := by
    simp only [m, m', Submodule.Quotient.mk_smul, map_smul, hxy]
  have hm : abelian₂ R k Z₀ m = 0 := by simp only [m, map_smul, hx0, smul_zero]
  have hm' : abelian₂ R k Z₀' m' = 0 := by rw [hL m m' hmm, hm, Matrix.mulVec_zero]
  let c : Fin n := ⟨k + 1, by omega⟩
  let r : Fin n := ⟨k, by omega⟩
  have hDi := isD_inv R k D.2
  let β : Fin n → K := Pi.single c 1
  let β' : Fin n → K := D.1⁻¹ c
  have hβi : ∀ b, β b ∈ R := by
    intro b
    by_cases h : b = c
    · simp [β, h, R.one_mem]
    · simp [β, h, R.zero_mem]
  have hβ : ∀ b : Fin n, b.val ≤ k → β b = 0 := by
    intro b hb
    have : b ≠ c := by
      intro h
      rw [h] at hb
      simp [c] at hb
    simp [β, this]
  have hβi' : ∀ b, β' b ∈ R := fun b => hDi.2.1 c b
  have hβ' : ∀ b : Fin n, b.val ≤ k → β' b = 0 := by
    intro b hb
    have hbc : b < c := by
      rw [Fin.lt_def]
      simp only [c]
      omega
    exact hDi.1.1 hbc
  have hξ := shf_Lam_zero R k Z₀ m hm
  have hξ' := shf_Lam_zero R k Z₀' m' hm'
  refine ⟨1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β, 1 + vecMulVec (Z₀'⁻¹ *ᵥ coeLin R m') β',
    shf_isPP R k _ β hξ hβ, shf_isPP R k _ β' hξ' hβ', ?_, ?_⟩
  · rw [shf_sUp k _ β hξ hβ r c rfl rfl, shf_sUp k _ β' hξ' hβ' r c rfl rfl]
    have e1 : β c = 1 := by simp [β]
    have e2 : β' c = 1 := hDi.1.2 c
    rw [e1, e2, mul_one, mul_one, ← A5x2.lamTil_fin R Z₀ r m, ← A5x2.lamTil_fin R Z₀' r m']
    have e3 : lamTil R Z₀ r.val m - lamTil R Z₀' r.val m' =
        -((lamTil R Z₀' k y0 - lamTil R Z₀ k x0) * r0) := by
      simp only [m, m', map_smul, r]
      have hs : ∀ a : K, ρ • a = r0 * a := fun a => rfl
      rw [hs, hs]
      ring
    rw [e3, AddChar.map_neg_eq_inv]
    intro h
    exact hψ (inv_eq_one.1 h)
  · intro p p' hp hp' hZ hZ' hrel
    refine ⟨shf_isInt R k Z₀ p hd hp hZ m β hβi hβ, shf_isInt R k Z₀' p' hd' hp' hZ' m' β' hβi' hβ',
      ?_⟩
    intro x y hxy'
    rw [shf_mem R k Z₀ p hd hp m hm β hβi hβ x, shf_mem R k Z₀' p' hd' hp' m' hm' β' hβi' hβ' y]
    have hρ : β' ⬝ᵥ (Z₀'⁻¹ *ᵥ coeLin R y) = β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) := by
      have h1 := hL x y hxy'
      have h2 : D.1⁻¹ *ᵥ abelian₂ R k Z₀' y = abelian₂ R k Z₀ x := by
        rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (by rw [isUpUni_det K D.2.1]; exact isUnit_one), Matrix.one_mulVec]
      rw [Lam_apply, Lam_apply, isD_mulVec_msk R k hDi] at h2
      have h3 := congrFun h2 c
      have hkc : k < c.val := by simp [c]
      simp only [msk, hkc, if_true] at h3
      have h4 : β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) = (Z₀⁻¹ *ᵥ coeLin R x) c := by
        simp [β]
      rw [h4, ← h3]
      rfl
    have hsub : ∀ s : R, Ψ (Submodule.Quotient.mk (x - s • m)) =
        Submodule.Quotient.mk (y - s • m') := by
      intro s
      have e1 : (Submodule.Quotient.mk (x - s • m) : MM R k Z₀) =
          Submodule.Quotient.mk x - s • Submodule.Quotient.mk m := rfl
      have e2 : (Submodule.Quotient.mk (y - s • m') : MM R k Z₀') =
          Submodule.Quotient.mk y - s • Submodule.Quotient.mk m' := rfl
      rw [e1, e2, map_sub, map_smul, hxy', hmm]
    constructor
    · rintro ⟨s, hs, hmem⟩
      exact ⟨s, by rw [hρ]; exact hs, (hrel _ _ (hsub s)).1 hmem⟩
    · rintro ⟨s, hs, hmem⟩
      exact ⟨s, by rw [← hρ]; exact hs, (hrel _ _ (hsub s)).2 hmem⟩

end Shf

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

theorem matrixHeart {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
    (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (n n' : ℕ) (hn : n = n') (k : ℕ) (hk : k + 2 ≤ n)
    (Z₀ : Matrix (Fin n) (Fin n) K) (Z₀' : Matrix (Fin n') (Fin n') K)
    (hd : IsUnit Z₀.det) (hd' : IsUnit Z₀'.det)
    (he : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀⁻¹ a b = 0)
    (he' : ∀ a b : Fin n', k < a.val → b.val + 1 = n' → Z₀'⁻¹ a b = 0) :
    ∃ (X : Type) (rel : X → Submodule R (Fin n → R) → Submodule R (Fin n' → R) → Prop),
      (∀ p p', IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) → IsInt R (Z₀' * p') →
        Nonempty ({φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') //
          φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
            ¬ InTT R k (Z₀ * p) (Z₀' * p') φ} ≃
          {x : X // rel x (latZ R (Z₀ * p)) (latZ R (Z₀' * p'))})) ∧
      (∀ x : X, ∃ σ σ', IsPP R k σ ∧ IsPP R k σ' ∧ ψ (sUp σ - sUp σ') ≠ 1 ∧
        ∀ p p', IsPP R k p → IsPP R k p' → IsInt R (Z₀ * p) → IsInt R (Z₀' * p') →
          rel x (latZ R (Z₀ * p)) (latZ R (Z₀' * p')) →
          IsInt R (Z₀ * (σ * p)) ∧ IsInt R (Z₀' * (σ' * p')) ∧
            rel x (latZ R (Z₀ * (σ * p))) (latZ R (Z₀' * (σ' * p')))) := by
  subst hn
  refine ⟨{Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀' // GB R k Z₀ Z₀' Ψ}, fun x L L' => Rel R x.1 L L',
    ?_, ?_⟩
  · intro p p' hp hp' hZ hZ'
    have hdp : IsUnit (Z₀ * p).det := by
      rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hd
    obtain ⟨e⟩ := countId R k ψ hsd hk Z₀ Z₀' hd hd' he he' p p' hp hp' hZ hZ'
      (hfin _ _ hZ hdp)
    exact ⟨e.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm⟩
  · intro x
    exact shiftData R k ψ hsd hk Z₀ Z₀' hd hd' x.1 x.2

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x9

noncomputable section

section Grp

variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)

def PPsub (N : ℕ) : Subgroup (upUniG K N) where
  carrier := {u | IsPP R k ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)}
  one_mem' := by
    show IsPP R k (((1 : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa using isPP_one R k
  mul_mem' := by
    intro a b ha hb
    show IsPP R k (((a * b : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa using isPP_mul R k ha hb
  inv_mem' := by
    intro a ha
    show IsPP R k (((a⁻¹ : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
    simpa [Matrix.coe_units_inv] using isPP_inv R k ha

theorem grp_mem_PPsub {N : ℕ} (u : upUniG K N) :
    u ∈ PPsub R k N ↔ IsPP R k ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := Iff.rfl

def kap (w : Point K) (q : Cos R w) :
    Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) ×
      (upUniG K w.1.sum ⧸ PPsub R k w.1.sum) :=
  (q.1, QuotientGroup.mk q.2.out)

def base (w : Point K) (y : Quotient (QuotientGroup.rightRel (intSub R (lowW K w.1 w.2))) ×
    (upUniG K w.1.sum ⧸ PPsub R k w.1.sum)) : Matrix (Fin w.1.sum) (Fin w.1.sum) K :=
  orbZ w (y.1.out, y.2.out)

theorem grp_orbZ_det (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]
  exact Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI w.1 w.2)

theorem base_det (w : Point K) (y) : IsUnit (base R k w y).det := grp_orbZ_det w _

theorem base_last (h : Point K) (s : ℕ) (t : Kˣ) (hs : 1 ≤ s) (hk : h.1.sum ≤ k) (y)
    (a b : Fin (addBlock h s t).1.sum) (ha : k < a.val) (hb : b.val + 1 = (addBlock h s t).1.sum) :
    (base R k (addBlock h s t) y)⁻¹ a b = 0 := by
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  let c : Fin (addBlock h s t).1.sum := ⟨h.1.sum, by omega⟩
  exact (inverse_last_column_formula K h s t hs _ _ (y.1.out).2.1 (y.2.out).2 a b c hb rfl).2.1
    (by rw [Fin.lt_def]; show h.1.sum < a.val; omega)

theorem orbZ_rep_eq_base_mul (w : Point K) (y) (q : Cos R w) (hq : kap R k w q = y) :
    ∃ p, IsPP R k p ∧ orbZ w (rep R q) = base R k w y * p := by
  subst hq
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (PPsub R k w.1.sum) q.2.out
  refine ⟨(((h⁻¹ : PPsub R k w.1.sum) : upUniG K w.1.sum) : GL (Fin w.1.sum) K),
    (h⁻¹ : PPsub R k w.1.sum).2, ?_⟩
  unfold base kap
  simp only [orbZ, rep]
  rw [hh]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, Subgroup.coe_inv]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem grp_sUp_mul {N : ℕ} (a b : upUniG K N) :
    sUp (((a * b : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      sUp ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) +
        sUp ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  rw [Subgroup.coe_mul, Units.val_mul]
  exact (Formalism.DoubleCosetMeasures.P.simpleAdd K N _ _).2 a.2 b.2

theorem grp_sUp_one {N : ℕ} :
    sUp (((1 : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 0 := by
  have := grp_sUp_mul (1 : upUniG K N) 1
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem grp_sUp_conj {N : ℕ} (a b : upUniG K N) :
    sUp (((a * b * a⁻¹ : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      sUp ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  have h1 := grp_sUp_mul a a⁻¹
  rw [mul_inv_cancel, grp_sUp_one] at h1
  rw [grp_sUp_mul, grp_sUp_mul]
  linear_combination -h1

theorem exists_injective_shift_of_orbZ (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K) (y)
    (σ : Matrix (Fin w.1.sum) (Fin w.1.sum) K) (hσ : IsPP R k σ) :
    ∃ S : Cos R w → Cos R w, Function.Injective S ∧ ∀ q, kap R k w q = y →
      kap R k w (S q) = y ∧ phase ψ (rep R (S q)) = phase ψ (rep R q) * ψ (sUp σ) ∧
      ∀ p, orbZ w (rep R q) = base R k w y * p →
        ∃ g, IsUpUni g ∧ IsInt R g ∧ orbZ w (rep R (S q)) = base R k w y * (σ * p) * g := by
  obtain ⟨y1, y2⟩ := y
  have hσd : IsUnit σ.det := by rw [isUpUni_det K hσ.1.1]; exact isUnit_one
  obtain ⟨σG, hσG⟩ : ∃ x : upUniG K w.1.sum,
      ((x : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = σ :=
    ⟨⟨Matrix.nonsingInvUnit σ hσd, hσ.1.1⟩, rfl⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u : upUniG K w.1.sum, y2.out = u := ⟨_, rfl⟩
  have hmk : (QuotientGroup.mk u₀ : upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2 := by
    rw [← hu₀]; exact QuotientGroup.out_eq' y2
  obtain ⟨τ, hτ⟩ : ∃ x : upUniG K w.1.sum, x = u₀ * σG * u₀⁻¹ := ⟨_, rfl⟩
  refine ⟨fun q => (q.1, QuotientGroup.mk (τ * q.2.out)), ?_, ?_⟩
  · intro a b hab
    have h1 : a.1 = b.1 := (Prod.mk.inj hab).1
    have h2 : (QuotientGroup.mk (τ * a.2.out) : upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)) =
        QuotientGroup.mk (τ * b.2.out) := (Prod.mk.inj hab).2
    rw [QuotientGroup.eq] at h2
    have h3 : (τ * a.2.out)⁻¹ * (τ * b.2.out) = a.2.out⁻¹ * b.2.out := by group
    rw [h3, ← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
    exact Prod.ext h1 h2
  · intro q hq
    have hq1 : q.1 = y1 := (Prod.mk.inj hq).1
    have hq2 : (QuotientGroup.mk q.2.out : upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2 :=
      (Prod.mk.inj hq).2
    subst hq1
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (intSub R (upUniG K w.1.sum)) (τ * q.2.out)
    have hp0 : u₀⁻¹ * q.2.out ∈ PPsub R k w.1.sum := by
      rw [← QuotientGroup.eq, hmk, hq2]
    have hγP : (γ : upUniG K w.1.sum) ∈ PPsub R k w.1.sum :=
      isPP_of_int R k (γ : upUniG K w.1.sum).2 γ.2.1
    have hσP : σG ∈ PPsub R k w.1.sum := by
      rw [grp_mem_PPsub, hσG]; exact hσ
    refine ⟨?_, ?_, ?_⟩
    · refine Prod.ext rfl ?_
      show (QuotientGroup.mk (QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out :
          upUniG K w.1.sum ⧸ PPsub R k w.1.sum) = y2
      rw [hγ, ← hmk, eq_comm, QuotientGroup.eq]
      have : u₀⁻¹ * (τ * q.2.out * γ) = σG * (u₀⁻¹ * q.2.out) * γ := by
        rw [hτ]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσP hp0) hγP
    · show ψ (sLow _ + sUp (((QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out : GL (Fin w.1.sum) K) :
          Matrix (Fin w.1.sum) (Fin w.1.sum) K)) = ψ (sLow _ + sUp _) * ψ (sUp σ)
      rw [hγ, grp_sUp_mul, grp_sUp_mul, hτ, grp_sUp_conj, hσG, ← AddChar.map_add_eq_mul]
      have h1 := hψ _ (Formalism.DoubleCosetMeasures.P.sUp_mem R _ γ.2.1)
      rw [← add_assoc, AddChar.map_add_eq_mul, h1, mul_one]
      congr 1
      simp only [rep]
      ring
    · intro p hp
      refine ⟨((γ : upUniG K w.1.sum) : GL (Fin w.1.sum) K), (γ : upUniG K w.1.sum).2, γ.2.1, ?_⟩
      have e0 : ((u₀ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
          (((u₀⁻¹ : upUniG K w.1.sum) : GL (Fin w.1.sum) K) :
            Matrix (Fin w.1.sum) (Fin w.1.sum) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
      have e1 : ∀ M : Matrix (Fin w.1.sum) (Fin w.1.sum) K,
          ((u₀ : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) *
          ((((u₀⁻¹ : upUniG K w.1.sum) : GL (Fin w.1.sum) K) :
            Matrix (Fin w.1.sum) (Fin w.1.sum) K) * M) = M := by
        intro M; rw [← Matrix.mul_assoc, e0, Matrix.one_mul]
      have hb : base R k w (q.1, y2) * (((u₀⁻¹ * q.2.out : upUniG K w.1.sum) :
          GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = orbZ w (rep R q) := by
        simp only [base, orbZ, rep, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hu₀]
        rw [e1]
      have hpe : p = (((u₀⁻¹ * q.2.out : upUniG K w.1.sum) :
          GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
        have := congrArg (fun M => (base R k w (q.1, y2))⁻¹ * M) (hb.trans hp)
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ (base_det R k w (q.1, y2))] at this
        exact this.symm
      show orbZ w (q.1.out, (QuotientGroup.mk (τ * q.2.out) :
        upUniG K w.1.sum ⧸ intSub R (upUniG K w.1.sum)).out) = _
      rw [hγ, hpe, hτ]
      simp only [base, orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hσG, hu₀]

end Grp

end

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x9

noncomputable section

section Top

variable {K : Type} [CommRing K] (R : Subring K)

def badN (k : ℕ) (w w' : Point K) (q : Cos R w × Cos R w') : ℕ :=
  Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
    φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
      InTT R (k + 1) (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ ∧
      ¬ InTT R k (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ}

open Classical in

theorem fib_core (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (w w' : Point K) (k : ℕ) (hn : w.1.sum = w'.1.sum) (hkn : k + 2 ≤ w.1.sum)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) (y) (y')
    (he : ∀ a b : Fin w.1.sum, k < a.val → b.val + 1 = w.1.sum → (base R k w y)⁻¹ a b = 0)
    (he' : ∀ a b : Fin w'.1.sum, k < a.val → b.val + 1 = w'.1.sum →
      (base R k w' y')⁻¹ a b = 0) :
    ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (badN R k w w' q : ℂ) * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have := (hsd 1).2 R.one_mem r hr
    simpa using this
  have hbd := base_det R k w y
  have hbd' := base_det R k w' y'
  obtain ⟨X, rel, hcnt, hshift⟩ := matrixHeart R ψ hsd hfin w.1.sum w'.1.sum hn k hkn
    (base R k w y) (base R k w' y') hbd hbd' he he'
  have hdetp : ∀ (N : ℕ) (B p : Matrix (Fin N) (Fin N) K), IsUnit B.det → IsPP R k p →
      IsUnit (B * p).det := by
    intro N B p hB hp
    rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hB

  have hb : ∀ q ∈ Q.filter (fun q => kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      Nonempty ({φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
          InTT R (k + 1) (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ ∧
          ¬ InTT R k (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} ≃
        {x : X // rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2)))}) ∧
      Finite (coker R (orbZ w (rep R q.1))) ∧ Finite (coker R (orbZ w' (rep R q.2))) := by
    intro q hq
    rw [Finset.mem_filter, hQ] at hq
    obtain ⟨⟨hi, hi'⟩, hy, hy'⟩ := hq
    obtain ⟨p, hp, e⟩ := orbZ_rep_eq_base_mul R k w y q.1 hy
    obtain ⟨p', hp', e'⟩ := orbZ_rep_eq_base_mul R k w' y' q.2 hy'
    rw [e] at hi ⊢
    rw [e'] at hi' ⊢
    exact ⟨hcnt p p' hp hp' hi hi', hfin _ _ hi (hdetp _ _ _ hbd hp),
      hfin _ _ hi' (hdetp _ _ _ hbd' hp')⟩
  have hsum : ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (badN R k w w' q : ℂ) * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) =
      ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (Nat.card {x : X // rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2)))} : ℂ)
        * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨⟨e⟩, -, -⟩ := hb q hq
    rw [badN, Nat.card_congr e]
  have key := sum_card_eq_zero (Q.filter (fun q => kap R k w q.1 = y ∧ kap R k w' q.2 = y'))
    (fun q => phase ψ (rep R q.1) * conj (phase ψ (rep R q.2)))
    (fun x q => rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2))))
    (by
      intro q hq
      obtain ⟨⟨e⟩, f1, f2⟩ := hb q hq
      have : Finite (coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2))) :=
        Finite.of_injective (fun φ => (φ : coker R (orbZ w (rep R q.1)) →
          coker R (orbZ w' (rep R q.2)))) DFunLike.coe_injective
      exact Finite.of_equiv _ e
    )
    (by
      intro x
      obtain ⟨σ, σ', hσ, hσ', hζ, hsh⟩ := hshift x
      obtain ⟨S, hSinj, hS⟩ := exists_injective_shift_of_orbZ R k ψ hψ w y σ hσ
      obtain ⟨S', hSinj', hS'⟩ := exists_injective_shift_of_orbZ R k ψ hψ w' y' σ' hσ'
      refine sum_eq_zero_of_shift _ _ (Prod.map S S') (hSinj.prodMap hSinj') ?_
        (ψ (sUp σ - sUp σ')) hζ ?_
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_filter, hQ] at hq
        obtain ⟨⟨⟨hi, hi'⟩, hy, hy'⟩, hr⟩ := hq
        obtain ⟨p, hp, e⟩ := orbZ_rep_eq_base_mul R k w y q.1 hy
        obtain ⟨p', hp', e'⟩ := orbZ_rep_eq_base_mul R k w' y' q.2 hy'
        obtain ⟨hk1, -, h3⟩ := hS q.1 hy
        obtain ⟨hk1', -, h3'⟩ := hS' q.2 hy'
        obtain ⟨g, hg, hgi, eg⟩ := h3 p e
        obtain ⟨g', hg', hgi', eg'⟩ := h3' p' e'
        rw [e] at hi hr
        rw [e'] at hi' hr
        obtain ⟨j1, j2, j3⟩ := hsh p p' hp hp' hi hi' hr
        rw [Finset.mem_filter, Finset.mem_filter, hQ]
        simp only [Prod.map_fst, Prod.map_snd]
        rw [eg, eg', latZ_mul_int R _ g hg hgi, latZ_mul_int R _ g' hg' hgi']
        exact ⟨⟨⟨Formalism.DoubleCosetMeasures.P.isInt_mul R j1 hgi, Formalism.DoubleCosetMeasures.P.isInt_mul R j2 hgi'⟩, hk1, hk1'⟩, j3⟩
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_filter] at hq
        obtain ⟨⟨-, hy, hy'⟩, -⟩ := hq
        obtain ⟨-, h2, -⟩ := hS q.1 hy
        obtain ⟨-, h2', -⟩ := hS' q.2 hy'
        simp only [Prod.map_fst, Prod.map_snd]
        rw [h2, h2', map_mul, hun (sUp σ'), sub_eq_add_neg, AddChar.map_add_eq_mul]
        ring
    )
  rw [hsum]
  exact key

open Classical in

theorem fibre_zero (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ) (hh : h.1.sum = h'.1.sum) (hk : h.1.sum ≤ k)
    (hks : k + 2 ≤ h.1.sum + s)
    (Q : Finset (Cos R (addBlock h s t) × Cos R (addBlock h' s t')))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2))) (y) (y') :
    ∑ q ∈ Q with (kap R k (addBlock h s t) q.1 = y ∧ kap R k (addBlock h' s t') q.2 = y'),
      (badN R k (addBlock h s t) (addBlock h' s t') q : ℂ) *
        (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  have hs : 1 ≤ s := by omega
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hsum' : (addBlock h' s t').1.sum = h'.1.sum + s := by simp [addBlock]
  exact fib_core R ψ hsd hun hfin (addBlock h s t) (addBlock h' s t') k (by rw [hsum, hsum', hh])
    (by rw [hsum]; exact hks) Q hQ y y'
    (fun a b ha hb => base_last R k h s t hs hk y a b ha hb)
    (fun a b ha hb => base_last R k h' s t' hs (hh ▸ hk) y' a b ha hb)

end Top

end

end Formalism.FourierDecayAlt.P.A5x9

end

section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x9

noncomputable section

section Top

variable {K : Type} [CommRing K] (R : Subring K)

theorem bad_zero (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (h h' : Point K) (s : ℕ) (t t' : Kˣ) (k : ℕ) (hh : h.1.sum = h'.1.sum) (hk : h.1.sum ≤ k)
    (hks : k + 2 ≤ h.1.sum + s)
    (Q : Finset (Cos R (addBlock h s t) × Cos R (addBlock h' s t')))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2))) :
    ∑ q ∈ Q, (badN R k (addBlock h s t) (addBlock h' s t') q : ℂ) *
        (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := Q.image (fun q => (kap R k (addBlock h s t) q.1, kap R k (addBlock h' s t') q.2)))
    (g := fun q => (kap R k (addBlock h s t) q.1, kap R k (addBlock h' s t') q.2))
    (fun q hq => Finset.mem_image_of_mem _ hq)]
  apply Finset.sum_eq_zero
  rintro ⟨y, y'⟩ _
  have key := fibre_zero R ψ hsd hun hfin h h' s t t' k hh hk hks Q hQ y y'
  rw [← key]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Prod.mk.injEq]

theorem isUnit_orbZ_det (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det K p.1.2.1, isUpUni_det K p.2.2, one_mul,
    mul_one]
  exact Matrix.isUnit_det_of_right_inverse (Formalism.DoubleCosetMeasures.P.Phase.pt_mul_ptI w.1 w.2)

theorem top_intTT_eq (ψ : AddChar K ℂ) (k₁ : ℕ) (w w' : Point K)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) :
    intTT R ψ k₁ w w' = ∑ q ∈ Q,
      (Nat.card {φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
        InTT R k₁ (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} : ℂ) *
      (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) := by
  unfold intTT
  rw [finsum_eq_sum_of_support_subset (s := Q)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    rw [if_pos ((hQ q).1 hq), mul_assoc]
  · intro q hq
    by_contra hn
    apply hq
    have hn' : ¬ (IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) :=
      fun hh => hn (Finset.mem_coe.2 ((hQ q).2 hh))
    simp only
    rw [if_neg hn', zero_mul, zero_mul]

theorem card_and_eq_add_card {α : Type} [Finite α] (A B C : α → Prop) (hBC : ∀ x, C x → B x) :
    Nat.card {x // A x ∧ B x} =
      Nat.card {x // A x ∧ C x} + Nat.card {x // A x ∧ B x ∧ ¬ C x} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨ha, hb⟩
      by_cases hc : C x
      · exact Or.inl ⟨ha, hc⟩
      · exact Or.inr ⟨ha, hb, hc⟩
    · rintro (⟨ha, hc⟩ | ⟨ha, hb, _⟩)
      · exact ⟨ha, hBC x hc⟩
      · exact ⟨ha, hb⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx'.2.2 hx.2

end Top

end

end Formalism.FourierDecayAlt.P.A5x9

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x9 in
theorem lattice_average_identity : Formalism.FourierDecayAlt.A5.AvgClaim := by
  intro K _ _ _ R ψ hD h h' s t t' k hh hk hks
  classical
  have hF := (integral_points_finite K R ψ hD (addBlock h s t)).prod
    (integral_points_finite K R ψ hD (addBlock h' s t'))
  have hQ : ∀ q, q ∈ hF.toFinset ↔ IsInt R (orbZ (addBlock h s t) (rep R q.1)) ∧
      IsInt R (orbZ (addBlock h' s t') (rep R q.2)) := by
    intro q
    rw [Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z) := fun m Z hZ hd => A5x3.finite_coker hD Z hZ hd
  have hbad := bad_zero R ψ hD.selfDual hD.unitary hfin h h' s t t' k hh hk hks hF.toFinset hQ
  rw [top_intTT_eq R ψ (k + 1) _ _ hF.toFinset hQ, top_intTT_eq R ψ k _ _ hF.toFinset hQ]
  refine Eq.trans ?_ (add_zero _)
  rw [← hbad, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← add_mul]
  congr 1
  have hq' := (hQ q).1 hq
  have f1 := hfin _ _ hq'.1 (isUnit_orbZ_det _ _)
  have f2 := hfin _ _ hq'.2 (isUnit_orbZ_det _ _)
  have f3 : Finite (coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
      coker R (orbZ (addBlock h' s t') (rep R q.2))) :=
    Finite.of_injective (fun φ => (φ : coker R (orbZ (addBlock h s t) (rep R q.1)) →
      coker R (orbZ (addBlock h' s t') (rep R q.2)))) DFunLike.coe_injective
  have hs := card_and_eq_add_card
    (fun φ : coker R (orbZ (addBlock h s t) (rep R q.1)) ≃ₗ[R]
      coker R (orbZ (addBlock h' s t') (rep R q.2)) =>
      φ ∈ isoZZ R (orbZ (addBlock h s t) (rep R q.1)) (orbZ (addBlock h' s t') (rep R q.2)))
    (fun φ => InTT R (k + 1) (orbZ (addBlock h s t) (rep R q.1))
      (orbZ (addBlock h' s t') (rep R q.2)) φ)
    (fun φ => InTT R k (orbZ (addBlock h s t) (rep R q.1))
      (orbZ (addBlock h' s t') (rep R q.2)) φ)
    (fun φ hφ j hj hjn => hφ j (by omega) hjn)
  rw [hs, Nat.cast_add]
  rfl

end Formalism.FourierDecayAlt.P

end
