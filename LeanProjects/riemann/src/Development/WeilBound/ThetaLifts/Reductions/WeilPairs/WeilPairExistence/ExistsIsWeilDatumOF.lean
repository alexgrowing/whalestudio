import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatH
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FixedOfMem
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IsScalarOneOfComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBaseStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.S

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isHeckeCharF_div_pow {χ η : (AF F ⊗[F] E)ˣ →* Circle} (hχ : IsHeckeCharF χ) (hη : IsHeckeCharF η) (n : ℕ) :
    IsHeckeCharF ((η ^ n)⁻¹ * χ) := by
  refine ⟨?_, fun x => ?_⟩
  · have : (((η ^ n)⁻¹ * χ : (AF F ⊗[F] E)ˣ →* Circle) : (AF F ⊗[F] E)ˣ → Circle) = fun x => (η x ^ n)⁻¹ * χ x := by
      funext x; simp
    rw [this]
    exact ((hη.1.pow n).inv).mul hχ.1
  · have h1 := hχ.2 x
    have h2 := hη.2 x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, one_pow, inv_one, mul_one]

theorem resEtaF_div_pow {χ η : (AF F ⊗[F] E)ˣ →* Circle} {n : ℕ} (hχ : ResEtaF χ n) (hη : ResEtaF η 1) :
    ResEtaF ((η ^ n)⁻¹ * χ) 0 := by
  refine ⟨hχ.1, fun e he a => ?_⟩
  have h1 := hχ.2 e he a
  have h2 := hη.2 e he a
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, pow_one, pow_zero, inv_mul_cancel]

theorem exists_isWeilDatumOF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∃ ω, Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ hLat χS χT hcS hcT rS rT
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := PositivityTheory.ThKW.exists_eta F E σ B hB
  obtain ⟨Λ, hΛ1, hΛ2⟩ := hLat
  have hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ := GlobalTheory.T.theta_function_heisenberg_invariant F E σ B hB nS nT JS JT ξ₀
  obtain ⟨w, lam, Om, hO⟩ := PositivityTheory.ThKW.latRep F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc
  obtain ⟨om, hom⟩ := PositivityTheory.ThKW.datumEta F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ Λ hΛ1 hΛ2 hc w lam Om hO η hη1 hη2 hη3 hη4
  obtain ⟨om', hom'⟩ := GlobalTheory.T.weil_datum_twist_by_hecke_characters_trivial_base F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ _ _ ((η ^ nS)⁻¹ * χS) ((η ^ nT)⁻¹ * χT) om hom
    (isHeckeCharF_div_pow hcS hη1 _) (isHeckeCharF_div_pow hcT hη1 _)
    (resEtaF_div_pow rS hη2) (resEtaF_div_pow rT hη2)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩

end PositivityTheory.ThKW.S
