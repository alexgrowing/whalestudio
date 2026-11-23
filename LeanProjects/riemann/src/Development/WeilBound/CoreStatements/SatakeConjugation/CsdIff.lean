import Development.WeilBound.CoreStatements.SatakeConjugation.CsdDefs

noncomputable section

open NumberField IsDedekindDomain

namespace PositivityTheory.NCmp

open GlobalTheory.CuspRep

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

abbrev cc (L : Type) [Field L] [NumberField L] [IsCMField L] : L ≃+* L := (IsCMField.complexConj L).toRingEquiv

theorem conjSrc_conjSrc (v : HeightOneSpectrum (𝓞 L)) : conjSrc (cc L) (conjSrc (cc L) v) = v := by
  have h1 := conjPl_conjSrc (cc L) v
  have h2 : GlobalTheory.Mem.Chr.ConjPl (cc L) v (conjSrc (cc L) v) := fun x => by
    have := h1 (cc L x)
    simp only [cc, AlgEquiv.coe_ringEquiv, IsCMField.complexConj_apply_apply] at this ⊢
    exact this.symm
  exact (eq_conjSrc h2).symm

def conjSrcEquiv (L : Type) [Field L] [NumberField L] [IsCMField L] : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) where
  toFun := conjSrc (cc L)
  invFun := conjSrc (cc L)
  left_inv := conjSrc_conjSrc
  right_inv := conjSrc_conjSrc

theorem sat_conj_of_isCsd (hS : SatFlip) {a : ℕ} (π : CG L a) (h : π.IsCsd) (w : HeightOneSpectrum (𝓞 L))
    (B : Multiset ℂˣ) (hB : π.HasSat w B) : π.HasSat (conjSrc (cc L) w) (B.map (·⁻¹)) := by
  induction π using Quotient.inductionOn with
  | _ π0 =>
    obtain ⟨T, hT⟩ := h
    exact hS L a π0 π0 T hT w B hB

theorem isCsd_of_sat (hS : SatFlip) (hT : ThetaTw) (hJS : GlobalTheory.Published.JacquetShalikaRigidity) {a : ℕ} (ha : 1 ≤ a)
    (π : CG L a)
    (h : ∀ᶠ w in Filter.cofinite, ∃ B, π.HasSat w B ∧ π.HasSat (conjSrc (cc L) w) (B.map (·⁻¹))) : π.IsCsd := by
  induction π using Quotient.inductionOn with
  | _ π0 =>
    obtain ⟨π', T, hT'⟩ := hT L a π0
    have hsame : ∀ᶠ u in Filter.cofinite, ∃ B, (CG.mk π0).HasSat u B ∧ (CG.mk π').HasSat u B := by
      refine (conjSrcEquiv L).surjective.le_map_cofinite (Filter.eventually_map.2 ?_)
      exact h.mono fun w ⟨B, h1, h2⟩ => ⟨B.map (·⁻¹), h2, hS L a π0 π' T hT' w B h1⟩
    have e := hJS.strong_multiplicity_one ha (CG.mk π0) (CG.mk π') hsame
    obtain ⟨S, hS'⟩ := Quotient.exact e
    refine ⟨T.trans S.symm, fun o φ => ?_⟩
    simp only [LinearEquiv.trans_apply, hT']
    apply S.injective
    rw [LinearEquiv.apply_symm_apply, hS', LinearEquiv.apply_symm_apply]

end PositivityTheory.NCmp
