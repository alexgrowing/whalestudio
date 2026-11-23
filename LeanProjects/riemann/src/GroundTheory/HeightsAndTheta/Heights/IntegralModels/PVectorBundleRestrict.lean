import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem IsBasisOn.restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) {V : X.Opens} (hVU : V ≤ U) :
    IsBasisOn M V (fun i => (M.presheaf.map (homOfLE hVU).op).hom (s i)) := by
  intro W hWV
  have key : (fun r : Fin n → Γ(X, W) =>
      ∑ i, r i • (M.presheaf.map (homOfLE hWV).op).hom
        ((M.presheaf.map (homOfLE hVU).op).hom (s i))) =
      (fun r : Fin n → Γ(X, W) =>
        ∑ i, r i • (M.presheaf.map (homOfLE (hWV.trans hVU)).op).hom (s i)) := by
    funext r
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show _ = (M.presheaf.map ((homOfLE hVU).op ≫ (homOfLE hWV).op)).hom (s i)
    rw [Functor.map_comp]
    rfl
  rw [key]
  exact hs W (hWV.trans hVU)

theorem IsBasisOn.restrictImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, f ''ᵁ U)} (hs : IsBasisOn M (f ''ᵁ U) s) :
    IsBasisOn (M.restrict f) U (fun i => (M.restrictAppIso f U).inv.hom (s i)) := by
  intro W hWU
  let e : Γ(X, W) ≃+* Γ(Y, f ''ᵁ W) := ((f.appIso W).commRingCatIsoToRingEquiv).symm
  have hb := (hs (f ''ᵁ W) (Scheme.Hom.image_mono f hWU)).comp
    (Equiv.piCongrRight fun _ : Fin n => e.toEquiv).bijective
  exact hb

theorem VectorBundleRestrict.proof : VectorBundleRestrict.Statement := by
  intro X Y f _ E hE
  refine IsVectorBundle.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app E) ?_
  intro x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE (f.base x)
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have hle : f ''ᵁ V ≤ U := (Scheme.Hom.image_mono f hVU).trans (f.image_preimage_le U)
  exact ⟨V, hV, hxV, n, _, (hs.restrict hle).restrictImage f⟩

end

end GroundTheory.Heights₂.Heights.Model
