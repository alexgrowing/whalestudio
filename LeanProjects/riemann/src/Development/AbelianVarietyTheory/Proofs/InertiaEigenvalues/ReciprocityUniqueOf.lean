import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible

open NumberField IsDedekindDomain Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TheRec

theorem recUnique_of_localConverse : LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL →
    IrreducibleAdmissibleGL → StandardFunctorsFiniteLength → RecUnique := by
  intro hEx hConv hExh hAdm hLen E Ω _ _ _ _ _ A w h rc rc' hrc hrc'
  have hComp := GlobalTheory.LocLanglands.FieldCompat.fieldCompatible GlobalTheory.globalArtinReciprocity_holds
    GlobalTheory.Published.chevalleyUnits' GlobalTheory.BrauerZero.brauerDegreeZero hEx hConv hExh (GlobalTheory.BZBridge.main hAdm hLen)
  funext x
  obtain ⟨n, c⟩ := x
  have hC := hComp E Ω A w h E Ω A w h rc' rc hrc' hrc
    (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) continuous_id
    (fun _ => rfl) n c.rep c.rep (LinearEquiv.refl ℂ _) (fun g v => by
      have hg : GeneralLinearGroup.map (RingEquiv.refl (w.adicCompletion E)).toRingHom g = g :=
        Units.ext (Matrix.ext fun _ _ => rfl)
      rw [hg]; rfl)
  obtain ⟨b, b', hb, hb', hN, hρ⟩ := hC
  have hbb : WD.mk b = WD.mk b' := WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => by
    simp only [LinearEquiv.refl_apply]; rw [hρ σ σ (fun _ => rfl)], fun v => by
    simp only [LinearEquiv.refl_apply]; rw [hN]⟩
  have hx : (⟨n, c⟩ : IrrGL (w.adicCompletion E)) = cls c.rep := congrArg (Sigma.mk _) c.cl_rep.symm
  rw [hx, ← hb, ← hb', hbb]

end GlobalTheory.TheRec
