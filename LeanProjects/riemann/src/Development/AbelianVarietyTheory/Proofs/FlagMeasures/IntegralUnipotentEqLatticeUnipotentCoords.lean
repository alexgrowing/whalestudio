import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreservedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometrySubOneOrthogonalLeCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreservedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatricesStatement

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem nO_eq_nLam_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  intro D X θ C u
  have key : ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
      ((GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ↔
        n ∈ Formalism.MainNotions.S.Lat.NLam (VS D).L0 (lf D (X.Fu u))) := by
    intro n γ hγ
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).1 h1, (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).1 h4⟩, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).1 h2,
        (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).1 h3⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).2 h1, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).2 h2, (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).2 h3⟩,
        (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).2 h4⟩
  refine ⟨fun γ hγ => ?_, fun s hs => ?_⟩
  · obtain ⟨n, hn⟩ := exists_equiv X γ hγ.1.1
    have hnL := (key n γ hn).1 hγ
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hnL.1.1
    exact ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hnL⟩,
      GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hn)⟩
  · obtain ⟨x, n, hx, rfl, hnL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    obtain ⟨γ, hγ⟩ := exists_mat X n
    exact ⟨γ, (key n γ hγ).2 hnL, GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hγ)⟩

end GlobalTheory.CovDomGrp
