import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem countOut_of : CountOut := by
  intro k H _ _ _ _ _ C hC E
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property C.mkQ E.subtype (Submodule.mkQ_surjective C)
  have hsec : ∀ (s : E →ₗ[k] H), C.mkQ ∘ₗ s = E.subtype → ∀ e : E, C.mkQ (s e) = e := by
    intro s hs e
    exact LinearMap.congr_fun hs e
  let S := {s : E →ₗ[k] H // C.mkQ ∘ₗ s = E.subtype}
  have hF : ∀ s : S, ¬C ≤ LinearMap.range s.1 ∧ Submodule.map C.mkQ (LinearMap.range s.1) = E := by
    intro s
    constructor
    · intro hle
      haveI : Nontrivial C := Module.nontrivial_of_finrank_eq_succ hC
      obtain ⟨c, hc⟩ := exists_ne (0 : C)
      obtain ⟨e, he⟩ := LinearMap.mem_range.1 (hle c.2)
      have h1 : C.mkQ (s.1 e) = e := hsec s.1 s.2 e
      have h2 : C.mkQ (c : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 c.2
      rw [he, h2] at h1
      have e0 : e = 0 := Subtype.ext h1.symm
      apply hc
      apply Subtype.ext
      rw [← he, e0, map_zero]
      rfl
    · rw [← LinearMap.range_comp, s.2, Submodule.range_subtype]
  let F : S → {D : Submodule k H // ¬C ≤ D ∧ Submodule.map C.mkQ D = E} :=
    fun s => ⟨LinearMap.range s.1, hF s⟩
  have hFb : Function.Bijective F := by
    constructor
    · intro s t h
      have h' : LinearMap.range s.1 = LinearMap.range t.1 := congrArg Subtype.val h
      apply Subtype.ext
      apply LinearMap.ext
      intro e
      have hm : s.1 e ∈ LinearMap.range t.1 := h' ▸ LinearMap.mem_range_self s.1 e
      obtain ⟨e', he'⟩ := LinearMap.mem_range.1 hm
      have h1 := hsec t.1 t.2 e'
      rw [he', hsec s.1 s.2 e] at h1
      have : e' = e := Subtype.ext h1.symm
      rw [← he', this]
    · rintro ⟨D, hnot, hmap⟩
      have hdisj : ∀ x ∈ D, x ∈ C → x = 0 := by
        intro x hxD hxC
        by_contra hx
        apply hnot
        intro y hy
        have hx' : (⟨x, hxC⟩ : C) ≠ 0 := fun h => hx (congrArg Subtype.val h)
        obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').1 hC ⟨y, hy⟩
        have : a • x = y := congrArg Subtype.val ha
        rw [← this]
        exact D.smul_mem a hxD
      let f : D →ₗ[k] H ⧸ C := C.mkQ ∘ₗ D.subtype
      have hf : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro d hd
        apply Subtype.ext
        exact hdisj d.1 d.2 ((Submodule.Quotient.mk_eq_zero C).1 hd)
      have hr : LinearMap.range f = E := by
        rw [LinearMap.range_comp, Submodule.range_subtype, hmap]
      let φ : D ≃ₗ[k] E := (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hr)
      have hφ : ∀ d : D, ((φ d : E) : H ⧸ C) = C.mkQ d := fun d => rfl
      let s : E →ₗ[k] H := D.subtype ∘ₗ (φ.symm : E →ₗ[k] D)
      have hs : C.mkQ ∘ₗ s = E.subtype := by
        apply LinearMap.ext
        intro e
        have h1 := hφ (φ.symm e)
        rw [LinearEquiv.apply_symm_apply] at h1
        exact h1.symm
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      show LinearMap.range s = D
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.symm), Submodule.range_subtype]
  let G : (E →ₗ[k] C) → S := fun g =>
    ⟨s0 + C.subtype ∘ₗ g, by
      apply LinearMap.ext
      intro e
      have h1 := LinearMap.congr_fun hs0 e
      have h2 : C.mkQ (g e : H) = 0 := (Submodule.Quotient.mk_eq_zero C).2 (g e).2
      simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, Submodule.subtype_apply] at h1 ⊢
      rw [h2, add_zero, h1]⟩
  have hGb : Function.Bijective G := by
    constructor
    · intro g g' h
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      have := LinearMap.congr_fun (congrArg Subtype.val h) e
      simpa [G] using this
    · rintro ⟨s, hs⟩
      have hmem : ∀ e, s e - s0 e ∈ C := by
        intro e
        apply (Submodule.Quotient.mk_eq_zero C).1
        have h1 := hsec s hs e
        have h2 := hsec s0 hs0 e
        simp only [Submodule.mkQ_apply] at h1 h2
        rw [Submodule.Quotient.mk_sub, h1, h2, sub_self]
      refine ⟨LinearMap.codRestrict C (s - s0) hmem, Subtype.ext ?_⟩
      apply LinearMap.ext
      intro e
      simp [G]
  have hcard : Nat.card (E →ₗ[k] C) = Nat.card k ^ Module.finrank k E := by
    haveI : Fintype k := Fintype.ofFinite k
    haveI : Finite (E →ₗ[k] C) := Module.finite_of_finite k
    haveI : Fintype (E →ₗ[k] C) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := E →ₗ[k] C), Nat.card_eq_fintype_card (α := k), Module.card_eq_pow_finrank (K := k) (V := E →ₗ[k] C),
      Module.finrank_linearMap k k E C, hC, mul_one]
  rw [← Nat.card_eq_of_bijective F hFb, ← Nat.card_eq_of_bijective G hGb, hcard]

end UpperTheory.Gal.crystallineComparison
