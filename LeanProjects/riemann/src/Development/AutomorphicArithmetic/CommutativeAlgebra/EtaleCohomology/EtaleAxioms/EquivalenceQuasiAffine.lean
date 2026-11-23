import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsOrthogonalIdempotentsIsDomainOfEtale
import Development.EtaleCohomology.EtaleSheaves.AcycQAPf
import Development.EtaleCohomology.EtaleSheaves.CoverPf
import Development.EtaleCohomology.EtaleSheaves.PrimMapComp
import Development.EtaleCohomology.EtaleSheaves.DescentPf
import Development.EtaleCohomology.EtaleSheaves.DomOpenPf
import Development.EtaleCohomology.EtaleSheaves.EmptyVan2
import Development.EtaleCohomology.EtaleSheaves.EqvQAPf
import Development.EtaleCohomology.EtaleSheaves.EtAICPf
import Development.EtaleCohomology.EtaleSheaves.EtLiftPf
import Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf
import Development.EtaleCohomology.EtaleSheaves.FinOpenPf
import Development.EtaleCohomology.EtaleSheaves.GlueOf
import Development.EtaleCohomology.EtaleSheaves.LocallyConstantH0
import Development.EtaleCohomology.EtaleSheaves.LCBijPf
import Development.EtaleCohomology.EtaleSheaves.LCGoodPf
import Development.EtaleCohomology.EtaleSheaves.LCMapPf
import Development.EtaleCohomology.EtaleSheaves.LCSplitPf
import Development.EtaleCohomology.EtaleSheaves.LCSurjPf
import Development.EtaleCohomology.EtaleSheaves.LeafMVVanishPf
import Development.EtaleCohomology.EtaleSheaves.LocDiagPf
import Development.EtaleCohomology.EtaleSheaves.LocFormPf
import Development.EtaleCohomology.EtaleSheaves.LocSHPf
import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
import Development.EtaleCohomology.EtaleSheaves.PiecesPf
import Development.EtaleCohomology.EtaleSheaves.ProjFPf
import Development.EtaleCohomology.EtaleSheaves.ProjGPf
import Development.EtaleCohomology.EtaleSheaves.QAClosedPf
import Development.EtaleCohomology.EtaleSheaves.StdCoverPf
import Development.EtaleCohomology.EtaleSheaves.StdPBPf
import Development.EtaleCohomology.EtaleSheaves.TorEtPf
import Development.EtaleCohomology.EtaleSheaves.TorSecPf
import Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
import Development.EtaleCohomology.EtaleSheaves.ZarLocalPf

namespace UpperTheory.Et.QuasiAffineEquivalence

theorem a0 : LateralTheory.E.t_E1Cut.QAClosed := LateralTheory.E.QAClosedPf.QAClosed_of
theorem a1 : LateralTheory.E.ZarLocalPf.LocSH := LateralTheory.E.LocSHPf.LocSH_of
theorem a2 : LateralTheory.E.ZarLocalPf.LocDiag := LateralTheory.E.LocDiagPf.LocDiag_of
theorem a3 : LateralTheory.E.t_E1Cut.ZarLocal := LateralTheory.E.ZarLocalPf.ZarLocal_of a1 a2
theorem a4 : LateralTheory.E.MVPf.MVSpc := LateralTheory.E.LeafMVVanishPf.mvSpc
theorem a5 : LateralTheory.E.MVPf.StdCover := LateralTheory.E.MVPf.StdCover_of
theorem a6 : LateralTheory.E.MVPf.StdPB := LateralTheory.E.MVPf.StdPB_of
theorem a7 : LateralTheory.E.t_E1Cut.MV := LateralTheory.E.t_E1Cut.MV_of a4 a5 a6
theorem a8 : LateralTheory.E.LocallyConstantH0.LCMap := LateralTheory.E.LCMapPf.LCMap_of
theorem a9 : LateralTheory.E.LCBijPf.TwGenNZAC := LateralTheory.E.TwGenNZACPf.TwGenNZAC_of
theorem a10 : LateralTheory.E.LCSurjPf.LocForm := LateralTheory.E.LocFormPf.LocForm_of
theorem a11 : LateralTheory.E.LCSurjPf.Descent := LateralTheory.E.DescentPf.Descent_of a9
theorem a12 : LateralTheory.E.LCBijPf.LCSurj := LateralTheory.E.LCSurjPf.LCSurj_of a10 a11
theorem a13 : LateralTheory.E.LocallyConstantH0.LCBij := LateralTheory.E.LCBijPf.LCBij_of a9 a12
theorem a14 : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := LateralTheory.E.LocallyConstantH0.localConstant_H0 a8 a13
theorem a15 : LateralTheory.E.t_E1Cut.EtLift := LateralTheory.E.EtLiftPf.EtLift_of
theorem a16 : LateralTheory.E.EtAICPf.Split := fun T C _ _ _ _ _ h => UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale T C h
theorem a17 : LateralTheory.E.EtAICPf.DomOpen := LateralTheory.E.DomOpenPf.DomOpen_of
theorem a18 : LateralTheory.E.t_E1Cut.EtAIC := LateralTheory.E.EtAICPf.EtAIC_of a16 a17
theorem a19 : LateralTheory.E.FinEtSectionPf.Pieces := LateralTheory.E.PiecesPf.Pieces_of a15 a18
theorem a20 : LateralTheory.E.FinEtSectionPf.FinOpen := LateralTheory.E.FinOpenPf.FinOpen_of
theorem a21 : LateralTheory.E.FinEtSectionPf.Glue := LateralTheory.E.Gluing₂.Glue_of a15 a18
theorem a22 : LateralTheory.E.t_E1Cut.FinEtSection := LateralTheory.E.FinEtSectionPf.FinEtSection_of a15 a18 a19 a20 a21
theorem a23 : LateralTheory.E.TorEtPf.ProjF := LateralTheory.E.ProjFPf.projF
theorem a24 : LateralTheory.E.TorEtPf.ProjG := LateralTheory.E.ProjGPf.ProjG_of
theorem a25 : LateralTheory.E.LCSplitPf.TorEt := LateralTheory.E.TorEtPf.TorEt_of_proj a23 a24
theorem a26 : LateralTheory.E.LCSplitPf.TorSec := LateralTheory.E.TorSecPf.TorSec_of
theorem a27 : LateralTheory.E.t_E1Cut.LCSplit := LateralTheory.E.LCSplitPf.LCSplit_of_tor a22 a25 a26
theorem a28 : LateralTheory.E.AcycQAPf.Deg0 := LateralTheory.E.Deg0Pf.Deg0_of
theorem a29 : LateralTheory.E.CoverPf.EmptyVan := LateralTheory.E.EmptyVan₂.EmptyVan_of
theorem a30 : LateralTheory.E.AcycQAPf.Cover := LateralTheory.E.CoverPf.Cover_of a29
theorem a31 : LateralTheory.E.t_E1Cut.AcycQA := LateralTheory.E.AcycQAPf.AcycQA_of a0 a3 a7 a14 a27 a28 a30
theorem a32 : LateralTheory.E.t_E1Cut.LCGood := LateralTheory.E.LCGoodPf.LCGood_of
theorem a33 : LateralTheory.E.t_E1Cut.EqvQA := LateralTheory.E.t_E1Cut.EqvQA_of a31 a0 a14 a32

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.EqvQA := a33

end UpperTheory.Et.QuasiAffineEquivalence
