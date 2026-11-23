import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

private theorem square {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ)
    (hm : 0 < m) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω) (hτ : admitted X τ s) (u v : X.K) (P Q P' Q' : Pt X m)
    (hP : IsPt X m u v P) (hQ : IsPt X m u v Q) (hP' : IsPt X m (τ u) (τ v) P') (hQ' : IsPt X m (τ u) (τ v) Q')
    (a a' f g : X.Kˣ) (ha : Mv X m (RingEquiv.refl _) 1 P Q a) (ha' : Mv X m (RingEquiv.refl _) 1 P' Q' a')
    (hf : Mv X m τ s P P' f) (hg : Mv X m τ s Q Q' g) :
    Cgr m (f ^ (1 : ZMod m).val * a') (unU X τ a ^ (cyc m s).val * g) := by
  have hr : admitted X (RingEquiv.refl _) 1 := (admB Ω ε X).2.2.1
  have h1 : cyc m (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have A := mvComp Ω ε X m hm (RingEquiv.refl _) τ 1 s hr hτ u v P Q Q' hP hQ hQ' a g ha hg
  have B := mvComp Ω ε X m hm τ (RingEquiv.refl _) s 1 hτ hr u v P P' Q' hP hP' hQ' f a' hf ha'
  rw [mul_one] at A
  rw [one_mul, h1] at B
  exact ((mvEx Ω ε X m hm τ s hτ u v P hP).2.2.2 Q' hQ' _ _ A).1 B

theorem cmp : Cmp := by
  intro Ω _ _ _ ε X m M hm hM U V R Q F F' hRQ hF
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, hrefl, -⟩ := admB Ω ε X
  have c1 := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
  have key : ∀ x y : Row M, Ok x y → ∃ b ∈ X.Un m, Mv X m (RingEquiv.refl _) 1 (R x y) (Q x y) b := by
    intro x y hxy
    exact (mvEx Ω ε X m hm _ 1 hrefl _ _ _ (hRQ x y hxy).1).1 _ (hRQ x y hxy).2
  have triv : m = 1 → ∀ f g : X.Kˣ, Cgr m f g := by
    rintro rfl f g
    unfold Cgr
    exact ⟨g⁻¹ * f, by simp⟩
  classical
  let a : Row M → Row M → X.Kˣ := fun x y => if h : Ok x y then Classical.choose (key x y h) else 1
  have ha : ∀ x y (h : Ok x y), a x y ∈ X.Un m ∧ Mv X m (RingEquiv.refl _) 1 (R x y) (Q x y) (a x y) := by
    intro x y h
    simp only [a, dif_pos h]
    exact Classical.choose_spec (key x y h)
  have hgal : ∀ s : Gal(Ω/ℚ), galU X s = unU X (X.gal s) := fun s => rfl
  refine ⟨a, ?_, ?_⟩
  · unfold CobBy
    intro s x y hxy
    have hxy0 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hok x y hxy).2.2.1 s⁻¹
    obtain ⟨eU, eV, mR, mQ⟩ := hF s x y hxy
    have hsq := square X m hm (X.gal s) s (hadm s) _ _ _ _ (R x y) (Q x y)
      (hRQ _ _ hxy0).1 (hRQ _ _ hxy0).2 (by rw [eU, eV]; exact (hRQ x y hxy).1) (by rw [eU, eV]; exact (hRQ x y hxy).2)
      _ _ _ _ (ha _ _ hxy0).2 (ha x y hxy).2 mR mQ
    rcases eq_or_ne m 1 with h1 | h1
    · subst h1
      exact ⟨(F' s x y * tw X 1 M s a x y / a x y)⁻¹ * F s x y, by rw [pow_one, mul_inv_cancel_left]⟩
    haveI : Fact (1 < m) := ⟨by omega⟩
    rw [ZMod.val_one, pow_one] at hsq
    unfold Cgr at hsq
    obtain ⟨h, eh⟩ := hsq
    refine ⟨h, ?_⟩
    unfold tw
    rw [hgal, eq_mul_inv_of_mul_eq eh, div_eq_mul_inv]
    ac_rfl
  · intro x y hxy
    refine ⟨(ha x y hxy).1, ?_⟩
    intro τ x' y' hτ hxy' eU eV mR mQ
    rcases eq_or_ne m 1 with h1 | h1
    · exact triv h1 _ _
    haveI : Fact (1 < m) := ⟨by omega⟩
    have hsq := square X m hm τ 1 hτ (U x) (V y) (R x y) (Q x y) (R x' y') (Q x' y')
      (hRQ x y hxy).1 (hRQ x y hxy).2 (by rw [eU, eV]; exact (hRQ x' y' hxy').1) (by rw [eU, eV]; exact (hRQ x' y' hxy').2)
      _ _ 1 1 (ha x y hxy).2 (ha x' y' hxy').2 mR mQ
    simp only [c1, ZMod.val_one, pow_one, one_mul, mul_one] at hsq
    unfold Cgr at hsq ⊢
    obtain ⟨h, eh⟩ := hsq
    exact ⟨h⁻¹, by rw [eh, inv_pow, mul_inv_cancel_right]⟩

end UpperTheory.V.Z.Kato.Sym

end
