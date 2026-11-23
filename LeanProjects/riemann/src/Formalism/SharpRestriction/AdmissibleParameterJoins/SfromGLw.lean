import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_frame {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x : S.V) :
    S.hT x x = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr x j := by
  conv_lhs => rw [← S.frame.sum_repr x]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    HSpace.gram, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aniso_of_definite {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (h1 : S.SigOK) (h2 : S.IsDefinite) (x : S.V) (hx : x ≠ 0) :
    S.hT x x ≠ 0 := by
  intro hx0
  have key : ∀ (p q : ℕ), Formalism.UG.HasSignature (S.gram.map τ) p q → (p = 0 ∨ q = 0) → False := by
    intro p q hsig hpq
    obtain ⟨e, P, hP⟩ := hsig
    let v : Fin p ⊕ Fin q → ℂ := fun k => τ (S.frame.repr x (e.symm k))
    have hv0 : v ≠ 0 := by
      intro h
      apply hx
      apply S.frame.repr.injective
      ext i
      have := congrFun h (e i)
      simp only [v, Equiv.symm_apply_apply, Pi.zero_apply, map_eq_zero] at this
      simpa using this
    have hQ : dotProduct (star v) (Matrix.mulVec ((S.gram.map τ).reindex e e) v) = 0 := by
      have hexp : dotProduct (star v) (Matrix.mulVec ((S.gram.map τ).reindex e e) v) = τ (S.hT x x) := by
        calc dotProduct (star v) (Matrix.mulVec ((S.gram.map τ).reindex e e) v)
            = ∑ k, ∑ l, star (v k) * (((S.gram.map τ).reindex e e) k l * v l) := by
              simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
          _ = ∑ i, ∑ j, star (τ (S.frame.repr x i)) * (τ (S.gram i j) * τ (S.frame.repr x j)) := by
              refine Fintype.sum_equiv e.symm _ _ (fun k => ?_)
              refine Fintype.sum_equiv e.symm _ _ (fun l => ?_)
              simp [v, Matrix.reindex_apply]
          _ = τ (S.hT x x) := by
              rw [hT_frame]
              simp [map_sum, map_mul, hτ, Complex.star_def, mul_assoc]
      rw [hexp, hx0, map_zero]
    let w : Fin p ⊕ Fin q → ℂ := Matrix.mulVec (↑P⁻¹ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) v
    have hvw : v = Matrix.mulVec (↑P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w := by
      show v = Matrix.mulVec (↑P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Matrix.mulVec (↑P⁻¹ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) v)
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h
      apply hv0
      rw [hvw, h, Matrix.mulVec_zero]
    have hcT : Formalism.UG.cT (starRingEnd ℂ) (↑P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.conjTranspose (↑P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      ext i j
      simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
    have hQ' : dotProduct (star w) (Matrix.mulVec (Formalism.UG.Jpq p q) w) = 0 := by
      rw [← hP, hcT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.star_mulVec, ← hvw]
      exact hQ
    have hself : dotProduct (star w) w = 0 := by
      rcases hpq with hp | hq
      · subst hp
        have hJ : Formalism.UG.Jpq 0 q = -1 := by
          ext i j
          rcases i with i | i
          · exact i.elim0
          rcases j with j | j
          · exact j.elim0
          simp [Formalism.UG.Jpq, Matrix.one_apply]
        rw [hJ, Matrix.neg_mulVec, Matrix.one_mulVec] at hQ'
        simpa [dotProduct_neg] using hQ'
      · subst hq
        have hJ : Formalism.UG.Jpq p 0 = 1 := by
          ext i j
          rcases i with i | i
          · rcases j with j | j
            · simp [Formalism.UG.Jpq, Matrix.one_apply]
            · exact j.elim0
          · exact i.elim0
        rw [hJ, Matrix.one_mulVec] at hQ'
        exact hQ'
    apply hw0
    open scoped ComplexOrder in
    first
    | exact Matrix.dotProduct_star_self_eq_zero.1 hself
    | exact dotProduct_star_self_eq_zero.1 hself
  exact key _ _ (h1 τ) (by rcases h2 τ with hs | hs <;> simp [hs])

theorem wittIdx_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (h : ∀ x : S.V, x ≠ 0 → S.hT x x ≠ 0) : SchurIrreducible.wittIdx S = 0 := by
  unfold SchurIrreducible.wittIdx
  have hset : {k | ∃ W : Submodule E S.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, S.hT x y = 0} = {0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨W, rfl, hW⟩
      have hWb : W = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_bot]
        by_contra hne
        exact h x hne (hW x hx x hx)
      subst hWb
      simp
    · rintro rfl
      refine ⟨⊥, by simp, fun x hx y _ => ?_⟩
      rw [(Submodule.mem_bot E).1 hx]
      simp
  rw [hset, csSup_singleton]

end Formalism.MainNotions.J

end
