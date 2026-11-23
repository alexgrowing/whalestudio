import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ}

theorem cond_conj (g s : S.V ≃ₗ[E] S.V) {A₁ B₁ A₂ B₂ : Submodule E S.V}
    (hA : ∀ x, x ∈ A₂ ↔ g.symm x ∈ A₁) (hB : ∀ x, x ∈ B₂ ↔ g.symm x ∈ B₁) :
    (∀ y ∈ B₂, s y - y ∈ A₂) ↔ (∀ x ∈ B₁, g.symm (s (g x)) - x ∈ A₁) := by
  constructor
  · intro h x hx
    have h1 : g x ∈ B₂ := (hB _).2 (by simpa using hx)
    have := (hA _).1 (h _ h1)
    simpa [map_sub] using this
  · intro h y hy
    have h1 := h (g.symm y) ((hB y).1 hy)
    rw [hA]
    simpa [map_sub] using h1

variable {T' : E} {F₁ F₂ : LFlag S r T'} {g : S.V ≃ₗ[E] S.V}

theorem e_of_frame (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (i : Fin r) :
    F₂.fl.e i = g (F₁.fl.e i) := by
  have := hfr (Fin.castSucc i)
  simpa [frame, FlagG.fvec] using this

theorem xflag_eq_map (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (j : ℕ) :
    Xflag F₂ j = (Xflag F₁ j).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = fun i => g (F₁.fl.e i) := funext (e_of_frame hfr)
  show Submodule.span E (F₂.fl.e '' _) = (Submodule.span E (F₁.fl.e '' _)).map _
  rw [Submodule.map_span, Set.image_image, he]
  rfl

theorem xsp_eq_map (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) :
    Xsp F₂ = (Xsp F₁).map (g : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = fun i => g (F₁.fl.e i) := funext (e_of_frame hfr)
  show Submodule.span E (Set.range F₂.fl.e) = (Submodule.span E (Set.range F₁.fl.e)).map _
  rw [Submodule.map_span, ← Set.range_comp, he]
  rfl

theorem orth_mem (hfr : ∀ a, frame F₂ a = g (frame F₁ a)) (hiso : g ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (y : S.V) : y ∈ orth S (Xsp F₂) ↔ g.symm y ∈ orth S (Xsp F₁) := by
  have hi : ∀ x y, S.hT (g x) (g y) = S.hT x y := hiso
  rw [mem_orth_iff, mem_orth_iff, xsp_eq_map hfr]
  constructor
  · intro h x hx
    have := h (g x) ⟨x, hx, rfl⟩
    rw [← hi x (g.symm y)]
    simpa using this
  · rintro h _ ⟨x, hx, rfl⟩
    have := h x hx
    rw [← hi x (g.symm y)] at this
    simpa using this

theorem nlam_conj (hg : IsAutLam S Λ g) (hfr : ∀ a, frame F₂ a = g (frame F₁ a))
    (s : S.V ≃ₗ[E] S.V) : s ∈ NLam Λ F₂ ↔ g⁻¹ * s * g ∈ NLam Λ F₁ := by
  have hA : ∀ j x, x ∈ Xflag F₂ j ↔ g.symm x ∈ Xflag F₁ j := fun j x => by
    rw [xflag_eq_map hfr]
    exact Submodule.mem_map_equiv _
  have hX : ∀ x, x ∈ Xsp F₂ ↔ g.symm x ∈ Xsp F₁ := fun x => by
    rw [xsp_eq_map hfr]
    exact Submodule.mem_map_equiv _
  have hO : ∀ x, x ∈ orth S (Xsp F₂) ↔ g.symm x ∈ orth S (Xsp F₁) := orth_mem hfr hg.1
  have hAut : IsAutLam S Λ s ↔ IsAutLam S Λ (g⁻¹ * s * g) := by
    constructor
    · intro h
      exact isAutLam_mul Λ (isAutLam_mul Λ (isAutLam_inv Λ hg) h) hg
    · intro h
      have := isAutLam_mul Λ (isAutLam_mul Λ hg h) (isAutLam_inv Λ hg)
      simpa [mul_assoc] using this
  show (IsAutLam S Λ s ∧ _ ∧ _) ↔ (IsAutLam S Λ (g⁻¹ * s * g) ∧ _ ∧ _)
  rw [hAut]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · exact forall_congr' fun j => cond_conj g s (hA j) (hA (j + 1))
  · exact cond_conj g s hX hO

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
