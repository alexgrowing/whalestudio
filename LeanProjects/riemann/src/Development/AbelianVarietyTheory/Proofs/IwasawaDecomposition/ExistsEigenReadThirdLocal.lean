import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_divX (Z : RationalReadingWithoutCongruence R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : Nonempty (DivX D) := by
  obtain ⟨G, V, -⟩ := GlobalTheory.PointGeometry.exists_geo D.what₂.LL
  exact ⟨GlobalTheory.provisionalDivX D G V (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) fun k =>
    ⟨mjH_noEta Z k, jM_noEta Z k, mjH_good_noEta Z hH k, jM_basis_noEta Z hH k, jM_lat_noEta Z hP hH k,
      mjLat_sub_noEta Z hP hH k, MjModel.jM_metric_all_noEta Z hH k⟩⟩

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.A.fam.base.Ix := by
  obtain ⟨p⟩ := GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ (hH.ok.ok2.what₂ A3.A.μ0).comm p.2⟩

end GlobalTheory.HeightCounting.Up.ThirdIdx

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

theorem exists_divX_eigIdx_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∃ (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd), Nonempty (E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m _ _ s r _
  letI : Algebra (↥m.z.core.Q.c.F) (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.what₂.LL := m.z.alg
  have hX : Nonempty (DivX (GlobalTheory.HeightCounting.Fin3.DL x L)) := nonempty_divX (Y := r.Y) r.Z m.z.pins m.intersectionNumber_baseChange
  rw [GlobalTheory.HeightCounting.Fin3.DL_eq] at hX
  obtain ⟨Xd⟩ := hX
  obtain ⟨c⟩ := nonempty_ix m.intersectionNumber_baseChange
  exact ⟨Xd, GlobalTheory.eigIdxFiniteTypes _ _, ⟨fun _ => c⟩⟩

end GlobalTheory.HeightCounting.Up.ThirdIdx

end
