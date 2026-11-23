import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ind_eq_sum_reps {L' L : COSub k d} {S : Finset (Fin d → k)} (h : L'.sub ≤ L.sub) (hS : IsReps L' L S)
    (c : Fin d → k) (a : V) : ind L c a = ∑ s ∈ S, ind L' (c + s) a := by
  classical
  refine Subtype.ext (funext fun y => ?_)
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  show (ind L c a).1 y = ∑ s ∈ S, (ind L' (c + s) a).1 y
  simp only [ind_apply]
  have e : ∀ s, y - (c + s) = y - c - s := fun s => by abel
  simp only [e]
  by_cases hy : y - c ∈ L.sub
  · obtain ⟨s, ⟨hs, hys⟩, hu⟩ := hS.2 _ hy
    rw [if_pos hy, Finset.sum_eq_single s, if_pos hys]
    · intro t ht hts
      exact if_neg fun hm => hts (hu t ⟨ht, hm⟩)
    · exact fun hn => (hn hs).elim
  · rw [if_neg hy]
    refine (Finset.sum_eq_zero fun s hs => if_neg fun hm => hy ?_).symm
    simpa using L.sub.add_mem (h hm) (hS.1 s hs)

theorem mL_refine (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L' L : COSub k d) (S : Finset (Fin d → k))
    (h : L'.sub ≤ L.sub) (hS : IsReps L' L S) (x : Fin d → k) (a : V) (a' : V') :
    mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  classical
  have h1 : ∀ y, y ∈ L.sub → ∃ s, s ∈ S ∧ y - s ∈ L'.sub := fun y hy => (hS.2 y hy).exists
  choose! rep hrepS hrep using h1
  have uniq : ∀ y ∈ L.sub, ∀ s ∈ S, y - s ∈ L'.sub → rep y = s := fun y hy s hs hys =>
    (hS.2 y hy).unique ⟨hrepS y hy, hrep y hy⟩ ⟨hs, hys⟩
  have hshift : ∀ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' = ∑ s ∈ S, mL B L' (x + s) a a' := by
    intro t ht
    have htL := hS.1 t ht
    have hm : ∀ s ∈ S, s - t ∈ L.sub := fun s hs => L.sub.sub_mem (hS.1 s hs) htL
    have hp : ∀ s ∈ S, s + t ∈ L.sub := fun s hs => L.sub.add_mem (hS.1 s hs) htL
    refine Finset.sum_nbij' (fun s => rep (s - t)) (fun s => rep (s + t)) (fun s hs => hrepS _ (hm s hs))
      (fun s hs => hrepS _ (hp s hs)) (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
    · refine uniq _ (L.sub.add_mem (hS.1 _ (hrepS _ (hm s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hm s hs))
      have e : rep (s - t) + t - s = -(s - t - rep (s - t)) := by abel
      rwa [e]
    · refine uniq _ (L.sub.sub_mem (hS.1 _ (hrepS _ (hp s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hp s hs))
      have e : rep (s + t) - t - s = -(s + t - rep (s + t)) := by abel
      rwa [e]
    · have e : x + s - t = x + rep (s - t) + (s - t - rep (s - t)) := by abel
      rw [e, mL_add_mem B L' _ (hrep _ (hm s hs))]
  calc mL B L x a a'
      = B (∑ s ∈ S, ind L' (x + s) a) (∑ t ∈ S, ind L' (0 + t) a') := by
        rw [mL, ← ind_eq_sum_reps h hS, ← ind_eq_sum_reps h hS]
    _ = ∑ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' := by
        simp only [map_sum, LinearMap.sum_apply, B_ind_ind B hT, zero_add]
    _ = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
        rw [Finset.sum_congr rfl hshift, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.BZCore

end
