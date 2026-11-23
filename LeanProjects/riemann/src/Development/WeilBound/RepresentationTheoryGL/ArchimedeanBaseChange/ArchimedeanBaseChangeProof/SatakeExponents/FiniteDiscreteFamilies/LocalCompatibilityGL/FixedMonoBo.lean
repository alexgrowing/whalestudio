import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegral

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem isoV_symm' {V V' : Submodule ℂ (Sm E N)} (hV : IsStable V) (h : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ : Sm E N) ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

theorem isoV_trans' {U V V' : Submodule ℂ (Sm E N)} (h : SpectralAccumulation.IsoV U V) (h' : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV U V' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  exact ⟨T.trans T', fun o φ ψ e => hT' o (T φ) (T ψ) (hT o φ ψ e)⟩

def kfP (Kf : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin N) (w.adicCompletion E))) (w : HeightOneSpectrum (𝓞 E)) :
    Subgroup (GL (Fin N) (w.adicCompletion E)) :=
  by classical exact if GlobalTheory.LFun.KGL w N ≤ Kf w then GlobalTheory.LFun.KGL w N else Kf w

end

end PositivityTheory.Rg.BcB.F.F5.Bo

end
