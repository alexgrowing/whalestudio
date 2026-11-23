import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf.OpenPf

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) : GlobalTheory.EtC.AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hq : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← hq, Polynomial.eval_map]
  have h2 := Polynomial.eval₂_at_apply (p := p.map e.symm.toRingHom) e.toRingHom a
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h2 ha ⊢
  rw [h2, ha, map_zero]

theorem openNbhdIC : OpenNbhdIC := by
  intro Z U hZ hU
  have : IsIntegral Z := hZ.1
  have : Nonempty U := hU.to_subtype
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have hV' : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hne : ((U.ι ''ᵁ V : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨U.ι x, x, hx, rfl⟩
  exact aic_of_equiv (U.ι.appIso V).commRingCatIsoToRingEquiv (hZ.2 _ hV' hne)

end LateralTheory.E.NormPf.OpenPf

end
