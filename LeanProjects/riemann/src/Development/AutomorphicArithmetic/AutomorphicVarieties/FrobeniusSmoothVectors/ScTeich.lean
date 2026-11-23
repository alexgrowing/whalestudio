import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcCycKFacts
import Mathlib.RingTheory.Teichmuller

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := ‹CharP (ResidueField O) l›
  haveI hp : PerfectRing (ResidueField O) l := inferInstance
  haveI : PerfectRing (O ⧸ maximalIdeal O) l := hp
  let f : (O ⧸ maximalIdeal O) →* O := (Perfection.teichmuller l (maximalIdeal O)).comp
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _))
  refine ⟨f, fun x => ?_⟩
  have h := Perfection.mk_teichmuller (p := l) (I := maximalIdeal O)
    (Perfection.liftMonoidHom l (O ⧸ maximalIdeal O) (O ⧸ maximalIdeal O) (MonoidHom.id _) x)
  exact h.trans (Perfection.coeffMonoidHom_zero_liftMonoidHom l (MonoidHom.id _) x)

theorem UpperTheory.V.Fr.sc_teich :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l], Finite (ResidueField c.O) → ∃ T : (ResidueField c.O)ˣ →* (Qbar l)ˣ, Function.Injective T ∧ ∀ (u : c.Oˣ) (j : ℕ) (s : G ℚ Ω), ‖(GlobalTheory.GalOfCusp.cycBar ℚ Ω l s ^ j * T (Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹)).val - u.val.1‖ < 1 := by
  intro Ω _ _ _ l _ c _ hfin
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨τ, hτ⟩ := teich_ex l c.O
  let ι : c.O →* Qbar l := c.O.val.toRingHom.toMonoidHom
  refine ⟨Units.map (ι.comp τ), ?_, ?_⟩
  · intro x y hxy
    have h1 : ((Units.map (ι.comp τ) x).val) = (Units.map (ι.comp τ) y).val := by rw [hxy]
    have h2 : τ x.val = τ y.val := Subtype.ext h1
    apply Units.ext
    rw [← hτ x.val, ← hτ y.val, h2]
  · intro u j s
    have hω : ((omO Ω l c.O s).val : ResidueField c.O) = residue c.O (chiO ℚ Ω l c.O s).val :=
      (UpperTheory.V.X.cycKFacts Ω l (ResidueField c.O)).2 c (residue c.O) s
    have hc : (GlobalTheory.GalOfCusp.cycBar ℚ Ω l s).val = ((chiO ℚ Ω l c.O s).val : PadicAlgCl l) := rfl
    set w : (ResidueField c.O)ˣ := Units.map (residue c.O).toMonoidHom u * (omO Ω l c.O s ^ j)⁻¹
    have key : (chiO ℚ Ω l c.O s).val ^ j * τ w.val - u.val ∈ maximalIdeal c.O := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change residue c.O _ = 0
      rw [map_sub, map_mul, map_pow, hτ, ← hω]
      simp only [w, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.coe_map, MonoidHom.coe_coe]
      have hne : ((omO Ω l c.O s).val : ResidueField c.O) ^ j ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
      rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
      exact sub_self _
    have hn := ((sc_norm l c _).2.1 key)
    convert hn using 2
    simp [Units.val_mul, Units.val_pow_eq_pow_val, hc, ι]
