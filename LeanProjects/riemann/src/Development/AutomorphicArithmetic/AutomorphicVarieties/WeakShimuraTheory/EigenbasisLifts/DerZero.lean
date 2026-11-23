import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.derZero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (x' : R →ₐ[c.O] DualNumber (PadicAlgCl l)) (S : Set R), (∀ (N : ℕ) (a : R), ∃ b ∈ Algebra.adjoin c.O S, a - b ∈ maximalIdeal R ^ N) → (∀ a ∈ S, (x' a).snd = 0) → ∀ a, (x' a).snd = 0 := by
  intro l _ c R _ _ _ x' S hdense hS a
  have hadj : ∀ b ∈ Algebra.adjoin c.O S, (x' b).snd = 0 := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS x hx
    | algebraMap r =>
      rw [AlgHom.commutes]
      first
        | rfl
        | simp [TrivSqZeroExt.algebraMap_eq_inl']
    | add x y _ _ hx hy => rw [map_add, TrivSqZeroExt.snd_add, hx, hy, add_zero]
    | mul x y _ _ hx hy => simp [map_mul, TrivSqZeroExt.snd_mul, hx, hy]
  have hcont := ((coPt c R).2 x').2
  by_contra h
  have hpos : 0 < ‖(x' a).snd‖ := norm_pos_iff.mpr h
  obtain ⟨n, hn⟩ := hcont _ (half_pos hpos)
  obtain ⟨b, hb, hab⟩ := hdense n a
  have key := hn _ hab
  rw [map_sub, TrivSqZeroExt.snd_sub, hadj b hb, sub_zero] at key
  linarith
