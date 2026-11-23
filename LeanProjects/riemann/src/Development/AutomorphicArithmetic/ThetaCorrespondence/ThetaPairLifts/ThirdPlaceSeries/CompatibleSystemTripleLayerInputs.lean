import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlaceDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalLocTripleWithLocalization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemTripleLayerEigenvalues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadTwWithLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tripleLayer_inputs_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL)
    (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hP hL)) (_root_.GlobalTheory.T.compatibleSystem_tripleLayer_eigenvalues_alt hP hS hL))
    fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨⟨G, -, -, -⟩, hpar⟩, heigH⟩ := h
  have hcf : HEq (TC.cf w.I w.l Z) (cfL c.a.nt.L c.a.nt.cf) := heq_cf_of_pack c.a.nt.pack
  obtain ⟨eig, heig⟩ := exists_heq_of_eq (F := fun D : D7 => ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) c.a.nt.eq.symm
    c.a.nt.eig
  obtain ⟨θ, hθ⟩ := exists_heq_of_eq (F := fun D : D7 => ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    c.a.nt.eq.symm c.a.nt.θ
  obtain ⟨Rw, hRw, ⟨Bs⟩, hloc⟩ := _root_.GlobalTheory.RowTriple.Lay.sideB_built_alt hL (w.D Z) c.a.nt.toNBuilt c.a.all.chiD.psi c.a.all.chi.psi (TC.cf w.I w.l Z) hcf
    c.a.Pq c.a.Pq_eq.symm _ c.row.S_eq.symm c.row.hecke.hL c.row.hL_eq.symm
    eig heig θ hθ
  obtain ⟨Sb, hSb, hET⟩ := heigH _ c.row.hecke.hL eig θ c.row.S_eq.symm c.row.hL_eq.symm heig hθ
  obtain ⟨hT, hO⟩ := hET Rw hRw
  have hR : ∀ a, ReadTw (withLoc c.a.nt.L) a := _root_.GlobalTheory.RowTriple.Lay.readTw_withLoc_alt hL _ c.a.nt.toNBuilt
  rw [← c.a.nt.eq] at hR
  exact ⟨TC.cf w.I w.l Z, Rw, c.a.nt.low, c.a.Pq, _, c.row.hecke.hL, eig, θ, Bs, Sb, hSb,
    _root_.GlobalTheory.RowTriple.Lay.isKsForm_of_built_heq hL (w.D Z) c.a.nt.toNBuilt _ c.row.S_eq c.a.ratIn.ks, hT, hO, hpar Rw hRw,
    _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all G.triple, hloc, hR⟩
end GlobalTheory.RowTriple.Lay
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | exact _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt <;> assumption)
end
end
