import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.HostPlacesWeight

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq Os Ks O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing Os] [IsDomain Os] [IsDiscreteValuationRing Os] [Field Ks] [Algebra Os Ks]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ιs : Qq →+* Ks} {σ : Qq ≃+* Qq} {js : W →+* Os} {ws : Os}

structure ExtOf (Os Ks O Kf : Type) [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] where
  φ : Os →+* O
  φK : Ks →+* Kf
  comm : ∀ x : Os, φK (algebraMap Os Ks x) = algebraMap O Kf (φ x)
  fin : φ.Finite
  frac : IsFractionRing O Kf
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O

theorem setting_ext (h : UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws) (X : ExtOf Os Ks O Kf) :
    HidaSetting p n' W Qq O Kf (X.φK.comp ιs) σ (X.φ.comp js) (X.φ ws) where
  prime := h.1.prime
  five_le := h.1.five_le
  two_le := h.1.two_le
  even := h.1.even
  frac_alt := h.1.frac_alt
  frac_O := X.frac
  p_unif := h.1.p_unif
  res_card := h.1.res_card
  eq_sum_herm_smul_frame_of_inW := h.1.eq_sum_herm_smul_frame_of_inW
  frob := h.1.frob
  period := h.1.period
  ι_comp := by
    intro x
    simp only [RingHom.comp_apply]
    rw [h.1.ι_comp, X.comm]
  finite := X.fin.comp h.1.finite
  complete_O := X.complete
  w_sq := by rw [← map_pow, h.1.w_sq, map_natCast]

theorem stdSub_placesConst (h : UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws) (X : ExtOf Os Ks O Kf) (nV m r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v))
    (v : Fin (placesConst (setting_ext h X) nV m r lam0 dom).nV) :
    ∃ (Os' Ks' : Type) (_ : CommRing Os') (_ : IsDomain Os') (_ : IsDiscreteValuationRing Os') (_ : Field Ks')
      (_ : Algebra Os' Ks') (ιs' : (placesConst (setting_ext h X) nV m r lam0 dom).Qq v →+* Ks')
      (js' : (placesConst (setting_ext h X) nV m r lam0 dom).W v →+* Os') (ws' : Os')
      (φ : Os' →+* O) (φK : Ks' →+* Kf),
      (∀ x : Os', φK (algebraMap Os' Ks' x) = algebraMap O Kf (φ x)) ∧ φ.Finite ∧
      UnramifiedQuadraticSetting p ((placesConst (setting_ext h X) nV m r lam0 dom).n' v)
        ((placesConst (setting_ext h X) nV m r lam0 dom).W v) ((placesConst (setting_ext h X) nV m r lam0 dom).Qq v)
        Os' Ks' ιs' ((placesConst (setting_ext h X) nV m r lam0 dom).σ v) js' ws' ∧
      φK.comp ιs' = (placesConst (setting_ext h X) nV m r lam0 dom).ι v ∧
      φ.comp js' = (placesConst (setting_ext h X) nV m r lam0 dom).j v ∧
      φ ws' = (placesConst (setting_ext h X) nV m r lam0 dom).w :=
  ⟨Os, Ks, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ιs, js, ws, X.φ, X.φK,
    X.comm, X.fin, h, rfl, rfl, rfl⟩

end Formalism.L2.G
