import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwChiGal

open GlobalTheory.GalChar (IsGal toQ inQ block)

theorem firstTwistCharacter_eq_ladic_heckeCharacter : ∀ (D : D7) (cf : CharFrame D) (chiD : Formalism.L2.NC.NChiData D), Formalism.L2.NC.NormalizedCharacterCompatibility D chiD → (∀ x, chiD.etaT.χ x = cf.eta.1 x) → (∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x) → (∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) → ValLL0 D cf → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (i : D.ntw.Tw) (b : Bool) (ρ : GlobalTheory.Triple.Reading D.ntw i b) (j : Fin D.R.m), ∃ n, GlobalTheory.GalChar.IsGal art ρ.κ ρ.ι (GlobalTheory.Triple.blockChar cf (D.ntw.l i) j) n (D.ntw.chi1 i (j.1 + 1) b) := by
  intro D cf chiD T hEta hMu hDel hC art ha i b ρ j
  obtain ⟨χ', n, h'⟩ := GlobalTheory.Triple.exists_blockChar ha hC ρ j
  have hj1 : 1 ≤ j.1 + 1 := Nat.le_add_left 1 j.1
  have hj2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨B1, hB1⟩ := T.chi1 i (j.1 + 1) b hj1 hj2
  have hχ : ∀ x, (chiD.firstHeckeCharacter i (j.1 + 1)).χ x = (cf.mu0 j * cf.delAt (D.ntw.l i) * cf.eta⁻¹).1 x := by
    intro x
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply,
      MonoidHom.inv_apply, hMu j x, hDel i x, hEta x]
    rfl
  set χb := GlobalTheory.Triple.blockChar cf (D.ntw.l i) j with hχb
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hc1 : Continuous (inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous.comp
      (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b))
  have e : inQ ρ.κ χ' = inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (h'.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb,
      GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero] with v hv hu hl A hA σ hσ
    refine GlobalTheory.ChiLocGal.frob_any (D.nd.plOm.2 v) hA (fun σ' hσ' => ?_) hσ
    obtain ⟨α, hα, x, hx, hσx⟩ := hB1 v hv
    have hval : ((χb.val v : ℂˣ) : ℂ) = (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x)⁻¹ :=
      GlobalTheory.ChiLocGal.val_block (GlobalTheory.ChiLocGal.val_of_at hχ hα) hx
    have e1 := h'.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ'
    rw [hval, inv_inv] at e1
    apply Units.ext
    apply ρ.ι.injective
    show ρ.ι (toQ ρ.κ (χ' σ' : (D.ntw.O0 i)ˣ)) = ρ.ι (toQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ))
    rw [e1]
    show Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
      (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ)))
    rw [hσx σ' hσ']
    exact (ρ.read x).symm
  have : χ' = D.ntw.chi1 i (j.1 + 1) b := MonoidHom.ext fun g => GlobalTheory.GalChar.inQ_inj ρ.κ (DFunLike.congr_fun e g)
  exact ⟨n, this ▸ h'⟩

end GlobalTheory.TwChiGal

end
