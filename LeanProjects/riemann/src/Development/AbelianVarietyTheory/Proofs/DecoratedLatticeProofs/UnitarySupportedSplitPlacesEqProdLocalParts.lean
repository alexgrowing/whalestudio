import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitDecomp

open GlobalTheory.SplitCut GlobalTheory.FinPl

variable {D : D7}

theorem real_idem_mul (y : AE D) (hy : infPart D y = 0) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => ?_
  have h1 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := by
    rw [← GlobalTheory.InfZeroFinSum.repr_map_id (Module.finBasis D.host.F D.host.E) (fstA D.host.F) y k]
    have : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y = 0 := hy
    rw [this, map_zero, Finsupp.zero_apply]
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, h1, mul_zero, map_zero]
  · rw [map_mul, map_zero]
    exact zero_mul _

theorem entry_memAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in

theorem prod_of_grpAt : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  intro D V n k _ _ _ _ q hv g hg
  set E : Fin n → AE D := fun i => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (q i).v) with hEdef
  have hE : ∀ i, (q i).e + cA D (q i).e = E i := fun i => by
    obtain ⟨ε, hε, h⟩ := (q i).above
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ i, E i * E i = E i := fun i => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ i, cA D (E i) = E i := fun i => cA_algebraMap _
  have hEo : ∀ i i', i ≠ i' → E i * E i' = 0 := fun i i' hii => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hii (hv h)), map_zero]
  choose h hh using fun i => cut_exists V g (E i) (hEE i) (hEc i)
  set M := mt V g with hM
  refine ⟨h, fun i a b => ?_, ?_⟩
  · rw [hE i, hh i]
    exact idempotent_mul_cut_sub_one_entry _ (hEE i) M a b
  · apply mt_injective
    rw [mt_list_prod V h E M hh hEo _ (List.nodup_finRange n)]
    have hsum : ((List.finRange n).map E).sum = ∑ i, E i := (Fin.sum_univ_def E).symm
    rw [hsum]
    refine exists_widePullback_of_iteratedLine _ M fun a b => ?_
    have hm := entry_memAt V _ g hg a b
    unfold idAt at hm
    obtain ⟨hinf, hoff⟩ := Ideal.mem_inf.mp hm
    rw [Ideal.mem_iInf] at hoff
    have h1 := key (fun i => (q i).v) hv ((M - 1) a b) (fun u hu =>
      (RingHom.mem_ker).mp (hoff ⟨u, fun ⟨i, hi⟩ => hu ⟨i, hi.symm⟩⟩))
    rw [map_sub, map_sub, map_one, map_sum] at h1
    have h2 := real_idem_mul ((M - 1) a b) ((RingHom.mem_ker).mp hinf)
    have h3 : (1 - ∑ i, E i) = (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) - ∑ i, E i) +
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) := by ring
    rw [h3, add_mul, h1, h2, add_zero]

end GlobalTheory.SplitDecomp
