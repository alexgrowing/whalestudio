import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeminormWeylAlg
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ArchKXPr

open GlobalTheory.ArchUniq

theorem locOpInf_unif_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ s : Finset (ℕ × ℕ), ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), ∀ k ∈ KAt K (evI F),
      ∀ f : SInf F (Fin a × Fin (a + a')),
        (s.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) (locOpInf (om (k, 1)) f) ≤
          C * (s'.sup (schwartzSeminormFamily ℂ (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F) ℂ)) f := by
  intro F E _ _ _ _ _ σ hP B a a' G X om om' hT K hK s
  have hψ : IsStd B.ψ := hT.base.std
  have hW : G.M.IsWeil B.ψ X.β (X.β / X.α) om := hT.weil
  have hcK : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B a G.V (a - G.p) G.p hT.base hT.geo.hV
    have e : K = K' := by
      ext g
      rw [hK g, hK' g]
    subst e
    exact hc
  obtain ⟨M, hM⟩ := GlobalTheory.ArchKX.archActX_bound G.M _ (isCompact_KAt hcK (evI F))
  obtain ⟨s', C, hC⟩ := GlobalTheory.ArchKX.unif_bound F B.ψ hψ (Fin a × Fin (a + a')) M s
  refine ⟨s', C, fun k hk f => ?_⟩
  have hkU : k ∈ UAt σ G.V (evI F) := hk.2
  have hex : ∀ f : SInf F (Fin a × Fin (a + a')), ∃ f₁ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (k, 1)) f f₁ :=
    GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om
      hT.base.cm hT.base.std hT.weil k hkU
  have hlin : IsLinearMap ℂ ⇑(om (k, 1)) := (om (k, 1)).isLinear
  let A : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    { toFun := locOpInf (om (k, 1))
      map_add' := fun f g => by simpa using locOpInf_lin hlin hex 1 1 f g
      map_smul' := fun c f => by simpa using locOpInf_lin hlin hex c 0 f f }
  let L := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX G.M k)
  let N := IsLinearMap.mk' _ (GlobalTheory.ArchKX.isLinearMap_archActX G.M k⁻¹)
  have hLN : ∀ v, L (N v) = v := GlobalTheory.ArchKX.archActX_inv G.M k
  have hN : ∀ v, ‖N v‖ ≤ M * ‖v‖ := hM k⁻¹ (inv_mem hk)
  have h2 : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 := fun f =>
    (GlobalTheory.ArchKX.lintegral_acts_eq_volume G.M B.ψ X.β (X.β / X.α) om hW k f (A f) (acts_locOpInf (hex f))).le
  have hI : ∀ v (f f' : SInf F (Fin a × Fin (a + a'))), ⇑f' = schrF (trP F (Fin a × Fin (a + a'))) v ⇑f →
      ⇑(A f') = schrF (trP F (Fin a × Fin (a + a'))) (L v) ⇑(A f) := fun v f f' h =>
    GlobalTheory.ArchKX.locOpInf_schrF G.M B.ψ X.β (X.β / X.α) om hψ hW k hkU hex v f f' h
  exact hC A L N hLN hN h2 hI f

end GlobalTheory.ArchKXPr
