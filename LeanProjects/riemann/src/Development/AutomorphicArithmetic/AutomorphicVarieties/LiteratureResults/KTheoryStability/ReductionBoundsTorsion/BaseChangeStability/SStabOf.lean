import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.BaseChangeStability.BaseChangeBijective

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sStab_of : SChain → SBridge → SStab := by
  intro hC hB R _ _ k n n' h hn
  obtain ⟨θ, hsurj, hker, hnat⟩ := hB k
  have := StabilizationIso.isIso_stab R (k + 1) n (by omega) n' h
  obtain ⟨hinj, hsur⟩ := StabilizationIso.baseChange_bijective (grpHMap (stab R n n' h) (k + 1))
  have hcyc : ∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsCyc (cmap (stab R n n' h) (k + 1) z) :=
    fun z hz => by
      unfold IsCyc at hz ⊢
      rw [hC.2.1, hz, map_zero]
  refine ⟨fun z hz hb => ?_, fun z' hz' => ?_⟩
  · have e := hnat _ _ (stab R n n' h) ⟨z, LinearMap.mem_ker.2 hz⟩
      ⟨_, LinearMap.mem_ker.2 (hcyc z hz)⟩ rfl
    rw [(hker _ _).2 hb] at e
    refine (hker _ ⟨z, LinearMap.mem_ker.2 hz⟩).1 (hinj ?_)
    rw [← e, map_zero]
  · obtain ⟨y, hy⟩ := hsur (θ _ ⟨z', LinearMap.mem_ker.2 hz'⟩)
    obtain ⟨w, rfl⟩ := hsurj _ y
    refine ⟨w.1, LinearMap.mem_ker.1 w.2, ?_⟩
    have e := hnat _ _ (stab R n n' h) w ⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ rfl
    exact (hker _ (⟨_, LinearMap.mem_ker.2 (hcyc w.1 (LinearMap.mem_ker.1 w.2))⟩ -
      ⟨z', LinearMap.mem_ker.2 hz'⟩)).1 (by rw [map_sub, e, hy, sub_self])

end PositivityTheory.KB

end
