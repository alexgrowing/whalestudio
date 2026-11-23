import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.AU

theorem isLoc_unique_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin n) (w.adicCompletion E))),
    IsSplitAt w → π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ n π w σ σ' hw h h'
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ
  obtain ⟨σ', rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ'
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  have key : ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), U.IsLocComp w τ →
      ∃ f : τ.ρ.IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict U.V hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key σ h
  obtain ⟨f', hf'⟩ := key σ' h'
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact Quotient.sound ((GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s σ.ρ σ'.ρ U.isIrreducible_rep σ.irred σ'.irred hcomm f hf).2 f' hf')

end GlobalTheory.DefU.AU
