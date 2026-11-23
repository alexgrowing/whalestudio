import Formalism.WeaklyAdmissibleFiltrations.DpcrisStable
import Formalism.CoboundaryTransfers.WachBridges

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem liftGal : LiftGal := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V V' _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ L L' F A D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bw M W₀ W₁ W₂ S cl₁ cl₂ eW e δ R a k u hL1 hL2 hNat hInt hW hQ hk ha hδ hR hZ hZu hgr hφ
  have hLift := Formalism.CoboundaryTransfers.lift_wach O A Bw M D₀ D₁ D₂ W₀ W₁ W₂ S e hW hQ δ R a k u hk ha hδ hR hZ
    hZu hgr hφ
  refine Formalism.CoboundaryTransfers.finiteClassesLift_holds O A Bw M D₀ D₁ D₂ W₀ W₁ W₂ S (LatticeCohomology L) (LatticeCohomology L') cl₁ cl₂
    (latticeFiniteCohomology PD L) (latticeFiniteCohomology PD L') F.H1map eW _ hNat ?_ hInt hLift
  intro pr hc
  rw [← hL1.2]
  exact ⟨pr, W₁.cocycle_mem_Zf hc, rfl⟩

end Formalism.WeaklyAdmissibleFiltrations
