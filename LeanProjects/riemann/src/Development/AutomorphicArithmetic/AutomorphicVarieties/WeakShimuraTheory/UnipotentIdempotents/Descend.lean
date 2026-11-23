import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (M : Type) [Group M] (χ : G L Ω →* M), IsOpen (χ.ker : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ χ.ker) → ∃ χ' : V.frame.G₀ →* M, IsOpen (χ'.ker : Set V.frame.G₀) ∧ ∀ g, χ' (V.pr g) = χ g := by
  intro l _ L Ω _ _ _ _ _ _ s V M _ χ hopen hine
  obtain ⟨hsurj, hquot, hker⟩ := phiKer V
  have hle : V.pr.ker ≤ χ.ker := hker χ.ker (Subgroup.isClosed_of_isOpen _ hopen) hine
  let χ₀ : ↥V.η.ker →* M :=
    (QuotientGroup.lift V.pr.ker χ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm.toMonoidHom
  have hcomp : ∀ g, χ₀ (V.pr g) = χ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm (V.pr g) =
        (QuotientGroup.mk g : G L Ω ⧸ V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hpre : (V.pr : G L Ω → ↥V.η.ker) ⁻¹' (χ₀.ker : Set ↥V.η.ker) = (χ.ker : Set (G L Ω)) := by
    ext g
    simp [MonoidHom.mem_ker, hcomp]
  have hop : IsOpen (χ₀.ker : Set ↥V.η.ker) := hquot.isOpen_preimage.mp (hpre ▸ hopen)
  exact ⟨χ₀, hop, hcomp⟩
