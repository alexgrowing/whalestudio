import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem polMapSt : PolMapSt := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ m b σ r ν hβ hβ' hO htw hσ hP hP' hr
  obtain ⟨π, hπ, hj⟩ := GlobalTheory.T.polarization_transfer_base_change E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' φ m b σ r ν hβ hβ' hO htw hσ hP hP' hr
  obtain ⟨mu, hmu⟩ := exists_sabMap_extending GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H _ _ O _
    (GlobalTheory.FiniteStable.twist σ hσ Z.oF.t) β _ _ O' _ Z'.oF.t β' (GlobalTheory.FiniteStable.twistCpt σ hσ (ofModel Z)) (ofModel Z') r
    ⟨ν.cm, ν.cart, ν.base, ν.act, ν.lin⟩ π hβ' hO Z'.oF.proper hj
  have hBD := GlobalTheory.T.polarization_transfer_with_function E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' φ σ r ν hβ hβ' hO htw hσ hP.1 hP'.1 π hj
  let mu' : TwMap σ Z'.t Z.t π := ⟨mu.cm, mu.cart, mu.base, mu.act, mu.lin⟩
  exact ⟨π, hπ, mu', GlobalTheory.T.polarization_base_change_models E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' m b σ π hπ mu' hP.2 hP'.2 hBD, hj, hmu,
    hBD⟩

end GlobalTheory.TorRef
