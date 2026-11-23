import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_read_of_divDef3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (Sp : SPer (F.Dc (R.toCx3 F).zs)) (C : ColData (F.Dc (R.toCx3 F).zs) Sp ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → ∃ Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0), HEq Rd.wU I.wU ∧ HEq Rd.eNu I.eNu ∧ HEq Rd.eRR I.eRR ∧ (∀ y, HEq (Rd.jV y) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd F.cr ∧ Rd.NuTie ∧ (DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → Rd.RRTie F.cr) ∧ ((∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → Rd.DcPt) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk S0 p0 Sp C NuC I h
  obtain ⟨Rd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_read_of_matrix_tie D (R.toCx3 F) F.fc F.cr (I.tup A3.A.μ0) h.tup.mu0 h.tup.v0 (I.jA A3.A.μ0)
      (rH D A3.A F.P1 F.ψ1 A3.A.μ0) (rE D A3.A F.P1 F.ψ1 A3.A.μ0) (rV0 D A3.A F.P1 F.ψ1 A3.A.μ0) I.wU I.eNu I.eRR
      (h.sharp.forms A3.A.μ0) (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A n hOk.ok2 F.P1 F.ψ1 A3.A.μ0) (h.sharp.iota A3.A.μ0)
      (fun u => ⟨_, h.cols.Nu u⟩)
  exact ⟨Rd, h1, h2, h3, h4, h5, h6, h7, fun hR => h8 ⟨_, hR.sharpRR⟩, h9⟩

end GlobalTheory.Mem.SJ
