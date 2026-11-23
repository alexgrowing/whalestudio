import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingGlobal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThKSocFinW

open GlobalTheory.ThKLocSS GlobalTheory.ThKSocFin

theorem socleOver_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ v : Pl F, ∀ w : Pl F, ∀ h ∈ UAt σ G.W (GlobalTheory.AdelicU.evFin F w), ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), om' (1, h) Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN v w h hh Φ hΦ
  set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hDdef
  have hD : ∀ Ψ ∈ D, om' (1, h) Ψ ∈ D := fun Ψ hΨ =>
    (GlobalTheory.T.matched_pair_theta_exists_data hK F E σ B a a' G X om om' R Rf hM).1 w h hh Ψ hΨ
  have hNf : ∀ x ∈ N, om' (1, h) x ∈ N := hN.stab.fin w h hh
  have hNg : ∀ x ∈ N, om' (1, h⁻¹) x ∈ N := hN.stab.fin w h⁻¹ (GlobalTheory.ThetaFacCompl.inv_mem_UAt _ hh)
  suffices key : socleOver (opsAt om' v) N D ≤
      (socleOver (opsAt om' v) N D).comap (om' (1, h)) from key hΦ
  refine sup_le (fun x hx => le_socleOver _ _ _ (hNf x hx)) (sSup_le ?_)
  rintro S ⟨hSD, hS⟩
  by_cases hvw : w = v
  · subst hvw
    intro x hx
    exact le_socleOver_of_simple _ hSD hS ((opStable_opsAt_iff om' w S).1 hS.2.1 h hh x hx)
  · have hfg : ∀ x, om' (1, h) (om' (1, h⁻¹) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hgf : ∀ x, om' (1, h⁻¹) (om' (1, h) x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hcomm : ∀ g ∈ UAt σ G.W (evFin F w), ∀ t ∈ opsAt om' v, ∀ x, t (om' (1, g) x) = om' (1, g) (t x) := by
      rintro g hg _ ⟨h', hh', rfl⟩ x
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
        commute_of_at hvw hg hh']
    have hS' := GlobalTheory.ThKSocFin.isSimpleOver_map (om' (1, h)) (om' (1, h⁻¹)) hfg hgf hNf hNg (hcomm h hh)
      (hcomm h⁻¹ (GlobalTheory.ThetaFacCompl.inv_mem_UAt _ hh)) hS
    have hSD' : S.map (om' (1, h)) ≤ D := by
      rintro _ ⟨y, hy, rfl⟩
      exact hD y (hSD hy)
    exact Submodule.map_le_iff_le_comap.1 (le_socleOver_of_simple _ hSD' hS')

end GlobalTheory.ThKSocFinW
