import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem IsBasisOn.image_of_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {W : Y.Opens} {n : ℕ} {s : Fin n → Γ(M.restrict f, W)}
    (hs : IsBasisOn (M.restrict f) W s) :
    IsBasisOn M (f ''ᵁ W) (fun i => (M.restrictAppIso f W).hom (s i)) := by
  intro V h
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, f ''ᵁ V' = V :=
    ⟨f ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact h.trans (f.image_le_opensRange W)⟩
  have hV' : V' ≤ W := by
    rw [← f.preimage_image_eq V', ← f.preimage_image_eq W]
    exact f.preimage_mono h
  have key : (fun r : Fin n → Γ(X, f ''ᵁ V') =>
      ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))) =
      (fun r' : Fin n → Γ(Y, V') =>
        ∑ i, r' i • ((M.restrict f).presheaf.map (homOfLE hV').op).hom (s i)) ∘
        (fun r i => (f.appIso V').hom.hom (r i)) := by
    funext r
    simp only [Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ((f.appIso V').inv.hom ((f.appIso V').hom.hom (r i)) : Γ(X, f ''ᵁ V')) •
      (M.presheaf.map (homOfLE h).op).hom ((M.restrictAppIso f W).hom (s i))
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [key]
  refine (hs V' hV').comp ?_
  exact (Equiv.piCongrRight fun _ => (f.appIso V').commRingCatIsoToRingEquiv.toEquiv).bijective

theorem VectorBundleLocal.proof : VectorBundleLocal.Statement := by
  intro X ι U hU E hE x
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have hR : IsVectorBundle (E.restrict (U i).ι) :=
    (hE i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app E).symm
  obtain ⟨W, hWa, hyW, n, s, hs⟩ := hR ⟨x, hxi⟩
  exact ⟨(U i).ι ''ᵁ W, hWa.image_of_isOpenImmersion (U i).ι, ⟨⟨x, hxi⟩, hyW, rfl⟩, n, _,
    hs.image_of_restrict (U i).ι E⟩

end

end GroundTheory.Heights₂.Heights.Model
