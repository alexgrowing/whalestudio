import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem isSF_ssetF_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  intro v
  have hQ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).1
  have hS : R.Sb = R.Pg := hW.allPl
  unfold SsetF
  rw [hQ, hS]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h⟩

set_option maxHeartbeats 1000000 in

theorem prt_le_hPart_of_carries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → (Y.Ish.prt : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0))) π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polE (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hc
  obtain ⟨hC, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hR R.toRealDat
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    rw [hμ]; exact isSF_ssetF_base R F hP.char hC
  have hinj := GlobalTheory.AdjPart.adjoint_injective_on_part R
    ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hR D) hH.ok hP.char hH.aux.ex hS hinj p c hc
  have hpart := (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 (s := 1) hH.ok.ok2 hC _ hSF' c (RealDat.polE (A := A3.A) p.1.1)).1
    fun P hP => (hlab P hP).1
  rw [Y.prtE π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart R.toRealDat F.lv2 (s := 1) hC hS _ hSF' Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ _ c hE true U hU
  exact hpart x hx

end GlobalTheory.Mem.R3
