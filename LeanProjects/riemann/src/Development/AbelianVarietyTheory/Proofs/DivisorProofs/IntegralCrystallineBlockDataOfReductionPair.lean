import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIntegralGaloisRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftIntSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFlagLiftOfResidue

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.WachBlock

theorem integralBlock_of_blockPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  intro E Ω _ _ _ _ _ l _ n t J bot hB
  obtain ⟨r, a, ρ, χ, hat, hr, hρ, hχ, hcong⟩ := hB
  obtain ⟨LL, hζ, hτ, hrL, hρL, hχL⟩ := GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters E Ω l n a t r ρ χ hr.1 hρ (fun s => (hχ s).1)
  obtain ⟨A, hA1, hA2, hAr⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l n LL r hr.1 hrL
  obtain ⟨B, hB1, hB2, hBρ⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l a LL ρ hρ hρL
  have memLL : ∀ {m : ℕ} (X Y Z : Matrix (Fin m) (Fin m) (PadicAlgCl l)), (∀ i j, X i j ∈ LL.1) →
      (∀ i j, Y i j ∈ LL.1) → (∀ i j, Z i j ∈ LL.1) → ∀ i j, (X * Y * Z) i j ∈ LL.1 := by
    intro m X Y Z hX hY hZ i j
    simp only [Matrix.mul_apply]
    exact LL.1.sum_mem fun k _ => LL.1.mul_mem (LL.1.sum_mem fun k' _ => LL.1.mul_mem (hX _ _) (hY _ _)) (hZ _ _)
  have cj : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (x : GL (Fin m) (PadicAlgCl l)),
      (((MulAut.conj C⁻¹).toMonoidHom x : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) =
        ((C⁻¹ * x * C : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
    intro m C x
    simp [MulAut.conj_apply]
  obtain ⟨r', hr'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 n ((MulAut.conj A⁻¹).toMonoidHom.comp r) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hAr g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hA2 (hrL g) hA1 i j)
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 a ((MulAut.conj B⁻¹).toMonoidHom.comp ρ) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hBρ g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hB2 (hρL g) hB1 i j)
  choose ψ hψ using fun s => (GlobalTheory.IntDescend.descend l LL (G E Ω)).2 (χ s) (fun g => ⟨hχL s g, GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one E Ω l (χ s) (hχ s).1 g⟩)
  haveI : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hmat : ∀ g, (r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin n) (PadicAlgCl l) => ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l))) hr'
  have hmatρ : ∀ g, (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((B⁻¹ * ρ g * B : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin a) (PadicAlgCl l) => ((f g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) hρ'
  have hψv : ∀ s g, GlobalTheory.WachBlock.ofOL l LL ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) = ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    intro s g
    exact congrArg (fun f : G E Ω →* (PadicAlgCl l)ˣ => ((f g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) (hψ s)
  have hcp : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (N : Matrix (Fin m) (Fin m) (PadicAlgCl l)),
      (((C⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) * N * (C : Matrix (Fin m) (Fin m) (PadicAlgCl l))).charpoly = N.charpoly := by
    intro m C N
    simpa using Matrix.charpoly_units_conj C⁻¹ N
  have hc : ∀ g m, ((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    intro g m
    rw [GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one]
    have e : GlobalTheory.WachBlock.ofOL l LL (((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m) =
        ((r g).val.charpoly - (ρ g).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l))).coeff m := by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map,
        ← Matrix.charpoly_map, hmat, hmatρ]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hψv, Units.val_mul]
      rw [hcp, hcp]
    have h := hcong g m
    rw [← e] at h
    exact h
  obtain ⟨R, M, rs, hM0, hML, hMm, hMs, hrs, hline⟩ := GlobalTheory.integral_flag_lift_of_residue ↥(OL LL) (G E Ω) n a t r' ρ' ψ ϖ hϖ hat hc GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor
  refine ⟨LL, r', ψ, ϖ, R, M, rs, hζ, hτ, ?_, fun s => ?_, hϖ, hM0, hML, hMm, hMs, hrs, hline⟩
  · have : (Matrix.GeneralLinearGroup.map (GlobalTheory.WachBlock.ofOL l LL)).comp r' = (MulAut.conj A⁻¹).toMonoidHom.comp r := hr'
    rw [this]
    exact GlobalTheory.crysWith_conj E Ω l n r A LL _ (fun i j => ⟨hA1 i j, hA2 i j⟩) hr
  · have : (Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp (ψ s) = χ s := hψ s
    rw [this]
    exact hχ s

end GlobalTheory.WachBlock

end
