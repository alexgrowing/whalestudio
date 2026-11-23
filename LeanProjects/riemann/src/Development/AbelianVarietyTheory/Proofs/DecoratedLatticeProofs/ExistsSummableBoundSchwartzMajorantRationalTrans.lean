import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTop
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Unf.MajLoc

theorem exists_compact_sub {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (K Q : Set G)
    (hK : IsCompact K) (hQ : IsCompact Q) : ∃ K' : Set G, IsCompact K' ∧ ∀ k ∈ K, ∀ x ∈ Q, k - x ∈ K' :=
  ⟨_, (hK.prod hQ).image continuous_sub, fun k hk x hx => ⟨(k, x), ⟨hk, hx⟩, rfl⟩⟩

theorem summable_of_tsum_ne_top {α β : Type*} (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) (h : (∑' y, ENNReal.ofReal (f y)) ≠ ⊤)
    (e : α → β) (he : Function.Injective e) : Summable fun a => f (e a) :=
  ((ENNReal.summable_toReal h).congr fun y => ENNReal.toReal_ofReal (hf y)).comp_injective he

theorem inv_pow_le {a c R : ℝ} (N : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (h : c ≤ a + R) :
    ((1 + a) ^ N)⁻¹ ≤ (1 + R) ^ N * ((1 + c) ^ N)⁻¹ := by
  have hle : 1 + c ≤ (1 + R) * (1 + a) := by nlinarith [mul_nonneg ha hR]
  have hA : 0 < (1 + a) ^ N := by positivity
  have hB : 0 < (1 + c) ^ N := by positivity
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle N

theorem realSize_neg {D : D7} (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : realSize θ (-x) = realSize θ x := by
  unfold realSize
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (-x) i j = -compAt θ τ x i j := by
    show θ τ (infPart D (-x i j)) = -θ τ (infPart D (x i j))
    rw [RingHom.map_neg (infPart D), RingHom.map_neg (θ τ)]
  rw [this, norm_neg]

theorem maj_add_le {D : D7} (θ : InfFam D) {m n : ℕ} (K K' : Set (Mx D m n)) (N : ℕ) (x y : Mx D m n) (R : ℝ)
    (hR : 0 ≤ R) (hx : realSize θ x ≤ R) (hK : ∀ k ∈ K, k - x ∈ K') :
    maj θ K N (x + y) ≤ (1 + R) ^ N * maj θ K' N y := by
  by_cases hb : InBox K (x + y)
  · have hb' : InBox K' y := by
      obtain ⟨k, hk, hkx⟩ := hb
      refine ⟨k - x, hK k hk, ?_⟩
      have : y - (k - x) = x + y - k := by abel
      rw [this]; exact hkx
    unfold maj
    rw [if_pos hb, if_pos hb']
    have hadd := GlobalTheory.MajSum.realSize_add_le θ (x + y) (-x)
    have e2 : x + y + -x = y := by abel
    rw [e2, realSize_neg] at hadd
    exact inv_pow_le N (realSize_nonneg θ _) (realSize_nonneg θ _) hR (by linarith)
  · have e0 : maj θ K N (x + y) = 0 := by
      unfold maj
      rw [if_neg hb]
    rw [e0]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N _)

theorem summable_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n),
    IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  intro D θ hθ m n
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ m n
  refine ⟨N, fun K Q hK hQ => ?_⟩
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) := GlobalTheory.Unf.MajMeas.continuous_realSize hθ
  obtain ⟨K', hK', hKK⟩ := @exists_compact_sub (Mx D m n) _ _ (lattice_Mx D m n).1 K Q hK hQ
  obtain ⟨R, hR⟩ := (hQ.image hcont).bddAbove
  have hs : Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => maj θ K' N (rat ξ) :=
    summable_of_tsum_ne_top (fun y : ratMx D m n => maj θ K' N y) (fun y => maj_nonneg θ K' N y) (hN K' hK')
      (fun ξ => ⟨rat ξ, rat_mem ξ⟩) fun a b h => rat_injective (congrArg Subtype.val h)
  exact ⟨fun ξ => (1 + max R 0) ^ N * maj θ K' N (rat ξ), hs.mul_left _, fun x hx ξ =>
    maj_add_le θ K K' N x (rat ξ) (max R 0) (le_max_right _ _) ((hR ⟨x, hx, rfl⟩).trans (le_max_left _ _))
      fun k hk => hKK k hk x hx⟩

end GlobalTheory.Unf.MajLoc

end
