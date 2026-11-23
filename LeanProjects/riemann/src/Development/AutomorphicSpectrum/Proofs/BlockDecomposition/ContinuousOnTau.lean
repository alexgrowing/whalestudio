import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitOfRetract
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNMapAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnipotentBlockFamily
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSymplecticFormSqNegOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerDiagonalOfUpperTriangularBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellConditionsOfSmulEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulNBlockInr

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mem_cell_iff {e : AE D} (hee : e * e = e) (g : G D p) : g ∈ cell e ↔ InCell e g :=
  isUnit_mix_iff hee (cB g)

theorem continuous_cB : Continuous (cB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem continuous_dB : Continuous (dB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem cell_eq {e : AE D} (hee : e * e = e) :
    cell e = (fun g : G D p => (cB g).det) ⁻¹' {z : AE D | IsUnit (1 - e + e * z)} := by
  ext g
  change IsUnit _ ↔ IsUnit _
  rw [det_mix_one hee]

open Classical in

def tau (e : AE D) (g : G D p) : hermS D p e := if h : ∃ x, IsB e g x then h.choose else 0

theorem isB_tau {e : AE D} {g : G D p} (h : ∃ x, IsB e g x) : IsB e g (tau e g) := by
  rw [tau, dif_pos h]
  exact h.choose_spec

theorem tau_eq {e : AE D} {g : G D p} {x : hermS D p e} (h : IsB e g x) : tau e g = x :=
  isB_unique (isB_tau ⟨x, h⟩) h

theorem tau_formula {e : AE D} (hee : e * e = e) {g : G D p} {x : hermS D p e} (hu : g ∈ cell e) (h : IsB e g x) :
    Ring.inverse (1 - e + e * (cB g).det) • (((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g)) = x.1.1 := by
  have hu' : IsUnit (1 - e + e * (cB g).det) := by
    have := hu
    rw [cell_eq hee] at this
    exact this
  exact mix_solve hee hu' x.2 h.2

theorem continuousOn_tau {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (hee : e * e = e) (hce : cA D e = e) :
    ContinuousOn (tau e : G D p → hermS D p e) (cell e) := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hd : Continuous fun g : G D p => (cB g).det := continuous_cB.matrix_det
  have h1 : ContinuousOn (fun g : G D p => Ring.inverse (1 - e + e * (cB g).det)) (cell e) := by
    refine (unit_AE he).2.comp hd.continuousOn ?_
    intro g hg
    rw [cell_eq hee] at hg
    exact hg
  have h2 : Continuous fun g : G D p => ((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g) := by
    refine Continuous.matrix_mul (Continuous.matrix_adjugate ?_) (continuous_dB.const_smul e)
    exact continuous_const.add (continuous_cB.const_smul e)
  have h3 : ContinuousOn (fun g : G D p => ((tau e g).1.1 : Mx D p p)) (cell e) := by
    refine (h1.smul h2.continuousOn).congr fun g hg => ?_
    have hB : IsB e g (tau e g) := isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
    exact (tau_formula hee hg hB).symm
  have i1 : Topology.IsInducing (Subtype.val : hermS D p e → hermA D p) := Topology.IsInducing.subtypeVal
  have i2 : Topology.IsInducing (Subtype.val : hermA D p → Mx D p p) := Topology.IsInducing.subtypeVal
  exact (i2.comp i1).continuousOn_iff.2 h3

theorem cellAlg : IdemEx → CellAlg := by
  intro hI D p nb hnb w hw S e he
  obtain ⟨hee, hce⟩ := (hI D S).2 e he
  have hex : ∀ g ∈ cell (p := p) e, IsB e g (tau e g) := fun g hg =>
    isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
  have hcell : ∀ {g : G D p} {x : hermS D p e}, IsB e g x → g ∈ cell e := fun h => (mem_cell_iff hee _).2 h.1
  refine ⟨tau e, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, continuousOn_tau he hee hce, (continuous_nb hnb).comp continuous_subtype_val,
      fun x y => isNMap_add hnb x.1 y.1⟩
    · rw [cell_eq hee]
      exact (unit_AE he).1.preimage (continuous_cB.matrix_det (R := AE D))
    · intro q hq x hx
      have h := (LeftCell.isB_left hq (tau e x)).2 (hex x hx)
      exact ⟨hcell h, (tau_eq h)⟩
    · intro y x hx
      have h := (isB_mul_nb hnb y (tau e x)).2 (hex x hx)
      exact ⟨hcell h, tau_eq h⟩
  · intro g hg u hu
    exact hcell ((isB_mul_right_iff he hu (tau e g)).2 (hex g hg))
  · intro g hg
    have h := hex g hg
    change (e • cB g) * _ = _
    rw [smul_mul_assoc]
    have h2 : cB g * (tau e g).1.1 = e • dB g := h.2
    rw [h2, smul_smul, hee]

end GlobalTheory.CompanionTheory.CellTop
