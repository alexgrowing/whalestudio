import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiAboveLHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.ConjDual

theorem equiv_contra (hadm : IrreducibleAdmissibleGL) {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {π π' : CuspSub E a} (T : π.V ≃ₗ[ℂ] π'.V) (hT : ∀ o φ, T (π.op (conjOp o) φ) = π'.op o (T φ))
    (h : DualIsConj π) (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h' : π'.IsLocComp w σ') (hσ : π.IsLocComp w σ) : Nonempty (σ.ρ.Equiv (GlobalTheory.SmGL.contra σ'.ρ)) := by
  obtain ⟨B, l, -, hf, -, -⟩ := h
  obtain ⟨f, f0, hfe⟩ := hσ
  have hT' : ∀ o φ, T.symm (π'.op o φ) = π.op (conjOp o) (T.symm φ) := fun o φ =>
    T.injective (by rw [hT, T.apply_symm_apply, T.apply_symm_apply])
  refine GlobalTheory.LocDual.equiv_contra_locComp hadm E a π'.V π'.stable π'.irred w σ' σ
    (((GlobalTheory.UnitaryBC.cuspSub_iff π').2.1 w σ').2 h') (B.flip.compl₁₂ T.symm.toLinearMap f) (fun e => f0 ?_) ?_
  · refine LinearMap.ext fun v => l _ fun ψ => ?_
    have := LinearMap.congr_fun (LinearMap.congr_fun e (T ψ)) v
    simpa using this
  · intro g φ ψ v e
    obtain rfl : ψ = π'.op (.fin (locGL E a w g)) φ := Subtype.ext e
    change B (f (σ.ρ g v)) (T.symm (π'.op _ φ)) = B (f v) (T.symm φ)
    rw [hT', hfe, CuspSub.locRep_eq, hf]

theorem dualIsConj_and_locComp : AutomorphicFormsFiniteGL → IrreducibleAdmissibleGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a) (T : π.V ≃ₗ[ℂ] π'.V), (∀ o φ, T (π.op (conjOp o) φ) = π'.op o (T φ)) → DualIsConj π → DualIsConj π' ∧ ∀ (w : HeightOneSpectrum (𝓞 E)) (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))), π'.IsLocComp w σ' → (π.IsLocComp w σ ↔ Nonempty (σ.ρ.Equiv (GlobalTheory.SmGL.contra σ'.ρ))) := by
  intro hF hadm E _ _ _ a π π' T hT h
  refine ⟨?_, fun w σ σ' h' => ⟨equiv_contra hadm T hT h w σ σ' h', fun ⟨e⟩ => ?_⟩⟩
  · obtain ⟨B, l, r, hf, hc, hx⟩ := h
    have hT' : ∀ o φ, T.symm (π'.op o φ) = π.op (conjOp o) (T.symm φ) := fun o φ =>
      T.injective (by rw [hT, T.apply_symm_apply, T.apply_symm_apply])
    have hT'' : ∀ o φ, T.symm (π'.op (conjOp o) φ) = π.op o (T.symm φ) := fun o φ => by
      rw [hT', GlobalTheory.CsdBack.conjOp_involutive o]
    refine ⟨B.flip.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ hφ => ?_, fun ψ hψ => ?_,
      fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
    · refine T.symm.map_eq_zero_iff.1 (r _ fun ψ => ?_)
      simpa using hφ (T ψ)
    · refine T.symm.map_eq_zero_iff.1 (l _ fun φ => ?_)
      simpa using hψ (T φ)
    · change B (T.symm (π'.op _ ψ)) (T.symm (π'.op _ φ)) = B (T.symm ψ) (T.symm φ)
      rw [hT'', hT', hf]
    · change B (T.symm (π'.op _ ψ)) (T.symm (π'.op _ φ)) = B (T.symm ψ) (T.symm φ)
      rw [hT'', hT', hc]
    · change B (T.symm ψ) (T.symm (π'.op _ φ)) + B (T.symm (π'.op _ ψ)) (T.symm φ) = 0
      rw [hT'', hT', add_comm, hx]
  · obtain ⟨σ₀, h₀, -⟩ := LocEx.exists_isLocComp hF E a π w
    obtain ⟨e₀⟩ := equiv_contra hadm T hT h w σ₀ σ' h' h₀
    exact h₀.congr ⟨.refl _ _, fun _ _ => rfl⟩ ⟨e₀.trans e.symm⟩

end GlobalTheory.ConjDual
