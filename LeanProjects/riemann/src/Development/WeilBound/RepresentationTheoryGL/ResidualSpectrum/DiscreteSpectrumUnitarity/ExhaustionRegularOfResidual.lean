import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.ExhaustionRegularFiniteClause
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.Re

section Pair

theorem iso (H : UsedReg) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π π' : CuspSub E a} (h : IsNormalised π)
    (h' : IsNormalised π') (e : IsSpehOf V π d) (e' : IsSpehOf V π' d) : π.Iso π' :=
  Quotient.exact (eq_of_heq (Sigma.mk.inj ((H E N hN).2.2.1 V hV a d a d π π' h h' e e').2).2)

theorem isCsd_of_isSpehOf (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (hc : IsCsdGL V) {π : CuspSub E a} (hπ : IsNormalised π) (h : IsSpehOf V π d) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (iso H hN hV (GlobalTheory.ThetaPull.isNormalised_thetaSub hπ) hπ
    (GlobalTheory.ThetaPull.isSpehOf_thetaSub hV.stable hc h) h)

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

theorem isUnitarisable_of_isLocComp (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, hV, hS⟩ := (H E a ha).2.1 a P rfl hP
  have hc := (H E a ha).2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

end Local

end PositivityTheory.Rg.Rs.Re

end
