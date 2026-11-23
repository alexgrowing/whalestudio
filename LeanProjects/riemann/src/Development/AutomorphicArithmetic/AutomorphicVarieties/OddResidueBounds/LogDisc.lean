import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.logDisc :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → (discr E).natAbs ≤ N ^ Module.finrank ℚ E ∧ Module.finrank ℚ E ≤ N := by
  intro E _ _ N hN ⟨φ⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  let F := φ.fieldRange
  have e : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField φ
  have hrank : Module.finrank ℚ E = Module.finrank ℚ F := e.toLinearEquiv.finrank_eq
  have hdisc : discr E = discr F := NumberField.discr_eq_discr_of_algEquiv E e
  obtain ⟨hprod, -, -⟩ := KStar.Ram.natAbs_discr_eq_finprod_conductor (N := N) (K := CyclotomicField N ℚ) F
  obtain ⟨hcard, -⟩ := KStar.Ram.card_fieldChars (N := N) (K := CyclotomicField N ℚ) F
  constructor
  · rw [hdisc, hprod, hrank, ← hcard]
    haveI : Fintype (KStar.Ram.fieldChars N F) := Fintype.ofFinite _
    rw [finprod_eq_prod_of_fintype, Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.prod_le_pow_card _ _ _
      (fun ψ _ => Nat.le_of_dvd hN (DirichletCharacter.conductor_dvd_level _))
  · have hinj : Function.Injective φ.toLinearMap := (φ : E →+* CyclotomicField N ℚ).injective
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [IsCyclotomicExtension.finrank (CyclotomicField N ℚ)
      (Polynomial.cyclotomic.irreducible_rat hN)] at h
    exact h.trans (Nat.totient_le N)
