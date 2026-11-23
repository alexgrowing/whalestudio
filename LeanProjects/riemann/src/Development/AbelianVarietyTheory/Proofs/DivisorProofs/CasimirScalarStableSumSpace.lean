import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirScalar_stableSumSpace : BuildY := by
  intro n ε H _ _ σ D E hσ hD c hc L hLf hLK
  have hE : IsGlRep E := hD.glRep
  have hLk : IsKStableSub ε E L :=
    isKStableSub_of_kStable hσ hD L hLf fun k hk v hv => ⟨sigD hD hk v, hLK k hk v hv, rfl⟩
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDop
  let Y0 : Submodule ℂ (TensorProduct ℂ D (Fock n)) := tensFock L ⊓ physicalSubspace ε
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0, diagE ε (eT E) cpT cmT a b x ∈ Y0 :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hLk hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have hD2 : ∀ y ∈ Y0, Dop (Dop y) ∈ Y0 := by
    intro y hy
    have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
    rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
    have hcas : casimir (eT (n := n) E) y = c • y := by
      rw [TRGap.casimir_eT]
      exact map_eq_smul_of_tensFock (fun v _ => hc v) hy.1
    have hmem : (2 : ℂ) • Dop (Dop y) ∈ Y0 := by
      rw [hDop, h2]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        LinearMap.sum_apply]
      rw [hcas]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
      simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
        hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
    have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
    rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
  have hG0 : ∀ z ∈ Y0, gradT z ∈ Y0 := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  have hW0 : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0, wK hD hk y ∈ Y0 :=
    fun k hk y hy => ⟨wK_tensFock hD hk (fun x hx => hLK k hk x hx) hy.1, wK_physSub hD hk hy.2⟩
  have hfd0 : FiniteDimensional ℂ Y0 := by
    haveI := tensorFock_finiteDimensional (n := n) hLf
    exact Submodule.finiteDimensional_of_le inf_le_left
  refine ⟨Y0 ⊔ Y0.map Dop, inferInstance, le_sup_left, sup_le inf_le_right ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact dD_physSub E hy.2
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    show Dop (y0 + Dop x) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩) (Submodule.mem_sup_left (hD2 x hx))
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hDop, gradT_D]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hG0 y0 hy0))
      (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG0 x hx), by rw [map_neg]⟩)
  · intro k hk y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hDop, wK_D hσ hD hk]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hW0 k hk y0 hy0))
      (Submodule.mem_sup_right ⟨_, hW0 k hk x hx, rfl⟩)

end GlobalTheory.PsCo.PcEF
