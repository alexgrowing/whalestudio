import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPairStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000
end GlobalTheory.MovedHomLat
open GlobalTheory.MovedHomLat in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MovedDict.moved_lattice_action_compat : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x]
    let N := ch.S.N
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.grid (i + 1) j)) := ((y * N.u (.grid (i + 1) j) : FinPt ch.G (.grid (i + 1) j)) : Formalism.L2.Theta.GA D _)
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.grid i j)) := ((x * N.u (.grid i j) : FinPt ch.G (.grid i j)) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (negSp (ch.G.V (.grid (i + 1) j))) (ch.G.V (.grid i j)) (negGA _ ky) kx
      (colLat (N.fr (.grid (i + 1) j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid (i + 1) j)) ky) (colLat (N.fr (.grid (i + 1) j))))
      (colLat (N.fr (.grid i j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid i j)) kx) (colLat (N.fr (.grid i j))))
      (fwd (ch.G.V (.grid (i + 1) j)) ky _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.grid i j)) kx _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.grid (i + 1) j)) ky _)
      (bwd (ch.G.V (.grid i j)) kx _)
    exact H
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y]
    let N := ch.S.N
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.top j)) := ((x * N.u (.top j) : FinPt ch.G (.top j)) : Formalism.L2.Theta.GA D _)
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.top (j + 1))) := ((y * N.u (.top (j + 1)) : FinPt ch.G (.top (j + 1))) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) kx ky
      (colLat (N.fr (.top j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top j)) kx) (colLat (N.fr (.top j))))
      (colLat (N.fr (.top (j + 1))))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top (j + 1))) ky) (colLat (N.fr (.top (j + 1)))))
      (fwd (ch.G.V (.top j)) kx _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.top (j + 1))) ky _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.top j)) kx _)
      (bwd (ch.G.V (.top (j + 1))) ky _)
    exact H
  | mu t i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_lattice_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_lattice_action_compat | exact _root_.GlobalTheory.MovedDict.moved_lattice_action_compat | (intros; apply _root_.GlobalTheory.MovedDict.moved_lattice_action_compat <;> assumption)
end
