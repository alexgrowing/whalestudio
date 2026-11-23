import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_midAt_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g z, MidAt I hi b P g z ∧ LiftsInv I κ P g := by
  intro B X I hOk u a i hi b κ P
  have hL := hOk.idx_ok a
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi _).symm⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hm : κ.2.1.1 ⟨P.1, hP⟩ ∈ ((I.idx a).levG i al ⟨P.1, hP⟩).H := κ.2.1.2 ⟨P.1, hP⟩ trivial
    obtain ⟨g, hg, hred⟩ := (hL.grpG i al ⟨P.1, hP⟩ _).1 (inv_mem hm)
    obtain ⟨z, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P _ g).2 hg
    exact ⟨g, z, hz, hL.int i al P hg, fun _ => hred, fun h => absurd hP (Q_notMem_of_ok hOk a _ h)⟩
  · have hP' : P.1 ∈ I.Q a := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    have hm : κ.2.2.1 ⟨P.1, hP'⟩ ∈ ((I.idx a).levQ i al ⟨P.1, hP'⟩).H := κ.2.2.2 ⟨P.1, hP'⟩ trivial
    have h3 := inv_mem hm
    rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
    obtain ⟨z, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P _ _).2 h3
    exact ⟨_, z, hz, ((κ.2.2.1 ⟨P.1, hP'⟩)⁻¹).2, fun h => absurd h hP, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.AdT
