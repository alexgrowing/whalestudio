import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThreeLeSplitAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparisonStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Pdv

theorem rowAt_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (AtAll fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) := by
  intro hA hG hD hI Bd Q Lk ker hE
  choose x0 hx0 using GlobalTheory.ShapeUniform.shape_uniform
  refine ⟨fun κ D O c b => x0 κ.eps ≤ O.L.sc.x ∧ StdTie D O (ker D O c b), ?_, ?_⟩
  · have h1 : RowE Q Lk (fun κ D O _ _ => x0 κ.eps ≤ O.L.sc.x) := by
      unfold RowE EvP
      refine ParEv.of_all fun κ _ => ⟨x0 κ.eps, fun K hk hx β _ c b _ => ?_⟩
      show x0 κ.eps ≤ β.p.L.sc.x
      rw [β.sc]
      exact hx
    exact (h1.and hE).mono fun _ _ _ H => H
  · intro 𝒜 σ s eps Fm hc x hx i
    obtain ⟨κ, hl, _, ht⟩ := s Fm hc
    obtain ⟨_, h0, hst⟩ := ht x hx i
    have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
    have hge : x0 eps ≤ x := by
      have h0' : x0 κ.eps ≤ (Fm.L x i).sc.x := h0
      rw [hl.eps_eq, hxx] at h0'
      exact h0'
    have hsh := hx0 eps Fm x hge hx i
    have hsb : 3 ≤ (Fm.D x i).host.splitBound :=
      (hsh (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) (ker _ _ _ (σ Fm hc x hx i)).ent (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0))).2.2
    exact GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison hA hG hD hI (Fm.D x i) (objAt Fm x hx i) (ker _ _ _ (σ Fm hc x hx i)) hst hsb
      Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge (fun Ee => ⟨(hsh Ee).1, (hsh Ee).2.1⟩)

end GlobalTheory.Pdv
