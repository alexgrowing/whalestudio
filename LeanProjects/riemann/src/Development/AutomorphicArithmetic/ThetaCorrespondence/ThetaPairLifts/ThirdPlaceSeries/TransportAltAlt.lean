import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenOccurrenceWithLocalData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc
set_option maxHeartbeats 4000000 in
theorem parIn_loc_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (_root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩
set_option maxHeartbeats 4000000 in
theorem transport_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Sb : Finset (PlE D'.host)) (hS0 : ∀ i, Sb ⊆ D'.ntw.S0 i)
    (e : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (he : HEq nt.eig e)
    (S' : RatDat D'.ntw) (hS : HEq (ratL nt.L nt.S) S')
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S'.WL j)) (hh : HEq nt.hL hL')
    (θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq nt.θ θ')
    (Rw0 : RowSide D') (hR0 : HEq Rw0.locR nt.A.row.locR)
    (hT : GlobalTheory.TwInputs.EigTrue D' cf' Rw0 Sb e) (hO : GlobalTheory.TwInputs.EigOcc D' S' θ' hL' Sb e) :
    ∃ Sb : Finset (PlE nt.D.host), (∀ i, Sb ⊆ (withLoc nt.L).ntw.S0 i) ∧
      (∀ Rw : RowSide (withLoc nt.L), HEq Rw.locR nt.A.row.locR →
        GlobalTheory.TwInputs.EigTrue (withLoc nt.L) (cfL nt.L nt.cf) Rw Sb nt.eig) ∧
      GlobalTheory.TwInputs.EigOcc (withLoc nt.L) ({ nt.S with } : RatDat (withLoc nt.L).ntw) nt.θ nt.hL Sb nt.eig := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have e1 : ratL L S = S' := eq_of_heq hS
  subst e1
  have e2 : hk = hL' := eq_of_heq hh
  subst e2
  have e3 : θ = θ' := eq_of_heq hθ
  subst e3
  have e4 : eig = e := eq_of_heq he
  subst e4
  refine ⟨Sb, hS0, fun Rw hRw => ?_, hO⟩
  have e5 : Rw.locR = Rw0.locR := (eq_of_heq hRw).trans (eq_of_heq hR0).symm
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [e5]
  exact hT
end GlobalTheory.GalLoc.EigLoc
namespace GlobalTheory.GalLoc.EigLoc
end GlobalTheory.GalLoc.EigLoc
end
