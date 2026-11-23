import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

namespace LocalIsomorphism

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem finRep_eq_act (h : GL (Fin N) (Af E)) (φ : Sm E N) : finRep E N h φ = act (.fin h) φ := by
  rfl

end LocalIsomorphism

theorem LocIso_holds : LocIso := by
  intro E _ _ _ N V V' hV w σ hσ
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ
  obtain ⟨T, hT⟩ := hV
  refine ⟨(Submodule.subtype V').comp ((T : V →ₗ[ℂ] V').comp (f.codRestrict V hfV)), ?_, ?_, ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun h0 v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      ZeroMemClass.coe_eq_zero, LinearEquiv.coe_coe] at h1
    have h2 : f.codRestrict V hfV v = 0 := by
      simpa using (T.map_eq_zero_iff).1 h1
    simpa [LinearMap.codRestrict] using congrArg Subtype.val h2
  · intro v
    exact (T _).2
  · intro g v
    have key := hT (.fin (locGL E N w g)) (f.codRestrict V hfV v) (f.codRestrict V hfV (σ.ρ g v))
      (by simp only [LinearMap.codRestrict_apply]; rw [hfeq, LocalIsomorphism.finRep_eq_act])
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    rw [key, LocalIsomorphism.finRep_eq_act]

end PositivityTheory.Rg.BcB.F.F5.Bo

end
