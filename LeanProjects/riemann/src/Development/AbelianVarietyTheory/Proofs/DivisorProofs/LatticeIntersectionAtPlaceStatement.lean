import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_intersection_at_place : LatIoAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.latIoAt | exact GlobalTheory.BigOn.Exp.SerBase.latIoAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.latIoAt <;> assumption)
