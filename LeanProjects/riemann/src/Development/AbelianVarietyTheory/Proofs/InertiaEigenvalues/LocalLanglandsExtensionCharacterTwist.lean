import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationTwistMultisegmentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSumTwistCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpTwist_lpTwist_comm (x : WD h) (ξ η : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ)
    (hη : WeilDeligne.IsSmooth η) : (x.lpTwist ξ hξ).lpTwist η hη = (x.lpTwist η hη).lpTwist ξ hξ := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  simp only [WD.lpTwist_mk]
  exact WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => smul_comm (η σ : ℂ) (ξ σ : ℂ) (b.ρ σ v), fun v => rfl⟩

theorem hasCentralChar_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : HasCentralChar (IrrGL.ofChar χ hχ).rep χ := fun z v => by
  let φ := equivRep (IrrRep.det (Fin 1) χ hχ)
  obtain ⟨u, rfl⟩ := φ.toLinearEquiv.surjective v
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [GeneralLinearGroup.scalar]
  have h3 : (IrrRep.det (Fin 1) χ hχ).ρ (GeneralLinearGroup.scalar (Fin 1) z) u = (χ z : ℂ) • u := by
    show (χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) z)) : ℂ) • u = _
    rw [h2]
  show (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ (GeneralLinearGroup.scalar (Fin 1) z) (φ.toIntertwiningMap u) =
    _ • φ.toIntertwiningMap u
  rw [← φ.toIntertwiningMap.isIntertwining, h3, map_smul]
  rfl

end GlobalTheory.LocLanglands.ExtTwist

end
