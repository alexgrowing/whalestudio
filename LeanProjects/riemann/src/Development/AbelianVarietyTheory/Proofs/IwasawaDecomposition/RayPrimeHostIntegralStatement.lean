import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimeHostIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_prime_host_integral : PrN → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  first | exact @GlobalTheory.ElemAtStates.elem_all | exact GlobalTheory.ElemAtStates.elem_all | (intros; apply GlobalTheory.ElemAtStates.elem_all <;> assumption)
