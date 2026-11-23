import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.StdSubPlacesConst
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable {p n' : ℕ} [hp : Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem settingStd_iso (hD : HidaSetting p n' W Qq O Kf ι σ j w) (eW : WQ p n' ≃+* W) (eQ : QQ p n' ≃+* Qq)
    (heq : ∀ x, eQ (algebraMap (WQ p n') (QQ p n') x) = algebraMap W Qq (eW x)) :
    UnramifiedQuadraticSetting p n' W Qq (OO p n') (KO p n') ((iota p n').comp (eQ.symm : Qq →+* QQ p n')) σ
      ((jO p n').comp (eW.symm : W →+* WQ p n')) (wU p n') := by
  obtain ⟨hS, hirr, hcard, hsq⟩ := settingStd p n' hD.five_le hD.two_le hD.even
  refine ⟨?_, hirr, hcard, hsq⟩
  exact
    { prime := hD.prime, five_le := hD.five_le, two_le := hD.two_le, even := hD.even, frac_alt := hD.frac_alt,
      frac_O := hS.frac_O, p_unif := hD.p_unif, res_card := hD.res_card, eq_sum_herm_smul_frame_of_inW := hD.eq_sum_herm_smul_frame_of_inW,
      frob := hD.frob, period := hD.period,
      ι_comp := fun x => by
        have h1 := hS.ι_comp (eW.symm x)
        have h2 := heq (eW.symm x)
        simp only [RingEquiv.apply_symm_apply] at h2
        simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
        rw [← h2, RingEquiv.symm_apply_apply, h1],
      finite := hS.finite.comp (RingHom.Finite.of_surjective _ eW.symm.surjective),
      complete_O := hS.complete_O,
      w_sq := hS.w_sq }

theorem stdSub_of_iso (hD : HidaSetting p n' W Qq O Kf ι σ j w) (eW : WQ p n' ≃+* W) (eQ : QQ p n' ≃+* Qq)
    (heq : ∀ x, eQ (algebraMap (WQ p n') (QQ p n') x) = algebraMap W Qq (eW x))
    (X : ExtOf (OO p n') (KO p n') O Kf)
    (hι : ∀ y, ι (eQ y) = X.φK (iota p n' y)) (hj : ∀ x, j (eW x) = X.φ (jO p n' x)) (hw : X.φ (wU p n') = w) :
    ∃ (Os Ks : Type) (_ : CommRing Os) (_ : IsDomain Os) (_ : IsDiscreteValuationRing Os) (_ : Field Ks)
      (_ : Algebra Os Ks) (ιs : Qq →+* Ks) (js : W →+* Os) (ws : Os) (φ : Os →+* O) (φK : Ks →+* Kf),
      (∀ x : Os, φK (algebraMap Os Ks x) = algebraMap O Kf (φ x)) ∧ φ.Finite ∧
      UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws ∧ φK.comp ιs = ι ∧ φ.comp js = j ∧ φ ws = w := by
  refine ⟨OO p n', KO p n', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (iota p n').comp (eQ.symm : Qq →+* QQ p n'), (jO p n').comp (eW.symm : W →+* WQ p n'), wU p n', X.φ, X.φK,
    X.comm, X.fin, settingStd_iso hD eW eQ heq, ?_, ?_, hw⟩
  · ext y
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← hι, RingEquiv.apply_symm_apply]
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← hj, RingEquiv.apply_symm_apply]

end Formalism.L2.G
