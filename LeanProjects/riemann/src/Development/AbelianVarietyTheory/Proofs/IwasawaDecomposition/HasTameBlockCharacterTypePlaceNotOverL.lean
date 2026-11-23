import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueCoprimeConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.TameTau

theorem tauTame : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  intro _ D cf b0 b1 Sx T Sp i j b kv _ _ hl
  have hg := D.host.g_prime kv.1
  have hover := D.naut.plGw_over kv.1 kv.2
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field (E := D.host.E) (Ω := D.nd.Om) (NX.pG D kv) (D.host.g kv.1) hg
    (GlobalTheory.Proof.EigenvalueCoprimeConjugation.normV_plGw D kv.1 kv.2) (by simpa [placesOver] using hover) (T.twistBaseCoefficientRing_isAdic i) (T.chi1 i j b)
    (T.twistCharacterFamily_continuous i j b) (fun A hA σ hσ => T.twistCharacterFamily_tame i j b kv.1 _ hover hl A hA σ hσ)
  refine ⟨(Units.map (baseCoeffToFractionRing D T i).toMonoidHom).comp τ, fun x u hu => ?_⟩
  rw [MonoidHom.comp_apply, Units.coe_map, hτ x u hu]
  rfl

end GlobalTheory.TameTau
