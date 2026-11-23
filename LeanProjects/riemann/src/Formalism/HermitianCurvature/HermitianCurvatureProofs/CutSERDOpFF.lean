import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem level_zero_inter_big_cell_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Q.Glev k r 0 ∩ JF.Om k r z z' = Q.Glev k r 0 ∩ Q.OmPlus k r z z' := by
  ext g
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.1, h2⟩

theorem ffl_om_eq (k r : ℕ) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) :
    Q.FFl k r z z' π π' 0 (JF.Om k r z z') = Q.FFl k r z z' π π' 0 (Q.OmPlus k r z z') := by
  unfold Q.FFl Q.SmoothLev Q.LeftEq Q.RightEq
  simp only [level_zero_inter_big_cell_eq]

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS in
theorem radial_operator_function_field : RDOpFF := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hSm hC J hJ
  rw [ffl_om_eq] at hJ ⊢
  have hDom : Q.IsDom k r D.z D.z' 0 (Q.OmPlus k r D.z D.z') :=
    Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus D.z_mem D.z'_mem
  have hPos : ∀ g ∈ Q.OmPlus k r D.z D.z', g ∈ B.GV k r → g ∈ B.GPos D := fun g hg hgG => ⟨hgG, hg.2⟩
  have hG' := germ_operators_holds k r Wp Wq Θ
  have hsupp : ∀ f' : B.Mat k r → (Wq →L[ℂ] Wp), tsupport f' ⊆ Q.OmPlus k r D.z D.z' →
      B.SuppIn (B.GPos D) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hC p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine equivariant_operators_holds extension_locality_holds _ _ _ _ D (Q.OmPlus k r D.z D.z') (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (smooth_operators_holds _ _ _ _ D Θ _ hDom.1 hPos hSm f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact adjoint_commutation_holds _ _ _ _ D Θ hSm hC f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutSE
