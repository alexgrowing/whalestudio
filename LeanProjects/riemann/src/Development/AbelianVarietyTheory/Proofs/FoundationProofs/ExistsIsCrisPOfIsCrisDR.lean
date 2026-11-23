import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FundSeq

def OntoAt (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι →
    (∀ u : Per.Bcris l, ∃ x : Per.Bcris l, ι x ∈ Per.FilD l 0 ∧ x - Per.φB l x = u) ∧
    (∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ ι b - w ∈ Per.FilD l 0)

theorem pair_onto {B D : Type} [AddCommGroup B] [AddCommGroup D] (φ : B →+ B) (ι : B →+ D) (F : Set D)
    (h1 : ∀ u, ∃ x, x - φ x = u) (h2 : ∀ w, ∃ b, φ b = b ∧ ι b - w ∈ F) (u : B) (w : D) :
    ∃ x y, y ∈ F ∧ x - φ x = u ∧ ι x - y = w := by
  obtain ⟨x0, hx0⟩ := h1 u
  obtain ⟨b, hb, hF⟩ := h2 (w - ι x0)
  refine ⟨x0 + b, _, hF, ?_, ?_⟩
  · rw [map_add, hb, ← hx0]; abel
  · rw [map_add]; abel

variable {l : ℕ} [Fact l.Prime]

theorem exists_restrict_aCris_bdRPlus {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j ∧ ∀ x : Per.Acris l,
      ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x) := by
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι h
  exact ⟨j, ⟨h2, h3⟩, h1⟩

theorem eq_core_of_isCrisDR {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) (C : Core l) :
    ι = C.ι := by
  obtain ⟨j, hj, hι⟩ := exists_restrict_aCris_bdRPlus h
  have e : j = C.j := (crisP_unique_equivariant l C.j C.j_cris).1 j hj
  refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
  rw [hι, C.ι_j, e]

theorem ontoAt_of_core (C : Core l) (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : OntoAt l := by
  intro ι hι
  rw [eq_core_of_isCrisDR hι C]
  refine ⟨fun u => ?_, h2⟩
  obtain ⟨x, y, hy, hx, hxy⟩ := pair_onto (Per.φB l).toAddMonoidHom C.ι.toAddMonoidHom
    (Per.FilD l 0 : Set (Per.BdR l)) h1 h2 u 0
  exact ⟨x, (sub_eq_zero.1 hxy : C.ι x = y) ▸ hy, hx⟩

theorem pair_onto_of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (h : OntoAt l)
    (K : FinExt l) (u : P.R.B) (w : P.R.BdR) :
    ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧ x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w := by
  obtain ⟨h1, h2⟩ := h _ T.incl
  have H := pair_onto (P.φB : P.R.B →+* P.R.B).toAddMonoidHom
    (P.ιB : P.R.B →+* P.R.BdR).toAddMonoidHom ((P.PD K).Fil 0 : Set P.R.BdR) (fun u => ?_) (fun w => ?_) u w
  · obtain ⟨x, y, hy, hx, hxy⟩ := H
    exact ⟨x, y, hy, by rw [P.PD_φ]; exact hx, by rw [P.PD_ι]; exact hxy⟩
  · obtain ⟨x, -, hx⟩ := h1 (T.eB u)
    obtain ⟨x, rfl⟩ := T.eB.surjective x
    refine ⟨x, T.eB.injective ?_⟩
    rw [← hx, map_sub, ← T.frob]
    rfl
  · obtain ⟨b, hb, hF⟩ := h2 (T.eD w)
    obtain ⟨b, rfl⟩ := T.eB.surjective b
    refine ⟨b, T.eB.injective ((T.frob b).trans hb), (T.fil K 0 _).2 ?_⟩
    have e : T.eB.symm.toRingHom (T.eB b) = b := T.eB.symm_apply_apply b
    rw [RingHom.comp_apply, e] at hF
    rw [map_sub]
    exact hF

theorem surjective_half_of_onto (h : ∀ (l : ℕ) [Fact l.Prime], OntoAt l) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  fun l _ K u w => pair_onto_of_tied (D.locT l) (h l) K u w

end GlobalTheory.FundSeq
