import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagSOfSDiagAt

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.RowsConc
namespace GlobalTheory.Core.Diag

def shareL (D : D7) (L C c : ℝ) : ℝ :=
  8 * Real.exp (-(C * (D.R.m : ℝ) ^ 5 * D.R.f * L)) + 6 * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))

def corankP (D : D7) (u : D.what₂.Word) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH))

def rankOn (D : D7) (u : D.what₂.Word) (M : Submodule ℂ (D.s.Cu u)) : ℕ :=
  Module.finrank ℂ (M.map (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH))

def ShareAt (D : D7) (u : D.what₂.Word) (e : ℝ) : Prop :=
  GlobalTheory.Core.Rk.hsDev D u ≤ e * (D.duS u : ℝ) ∧ (corankP D u : ℝ) ≤ e * (D.duS u : ℝ) ∧
    ∀ M : Submodule ℂ (D.s.Cu u), (Module.finrank ℂ M : ℝ) - e * (D.duS u : ℝ) ≤ (rankOn D u M : ℝ)

def FullAt (D : D7) (u : D.what₂.Word) (L C c : ℝ) : Prop :=
  SDiagAt D u (gamL D L C) c ∧ (GlobalTheory.Core.Rk.Small D u L C → ShareAt D u (shareL D L C c))

def SDiagFull (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ Cl₀ : ℝ, ∀ C' Cl : ℝ, 8 ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, FullAt D u L CD c

def SDiagCor (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, FullAt D u L CD c

def SDiagW (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → 1 ≤ C0 → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D L CD) c

def SDiagWU (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C0 : ℝ, 1 ≤ C0 → ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), TrueS D → GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT → StandingNumericalData D C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D L CD) c

def HypInh : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueS D ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, GlobalTheory.Core.Rk.Small D u L C

theorem corankP_le_hsDev (D : D7) (u : D.what₂.Word) : (corankP D u : ℝ) ≤ GlobalTheory.Core.Rk.hsDev D u := by
  unfold corankP GlobalTheory.Core.Rk.hsDev
  set N := LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → D.s.Cu u := fun i => (b i : D.s.Cu u)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.sum_norm_sq_le_hsNormSq (Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) v hv
  have hterm : ∀ i, ‖(Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) (v i)‖ ^ 2 = 1 := by
    intro i
    have hP : D.s.Pu u (v i) = 0 := LinearMap.mem_ker.1 (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [Kmat, hP, hn]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at h
  simpa using h

theorem finrank_le_rankOn_add (D : D7) (u : D.what₂.Word) (M : Submodule ℂ (D.s.Cu u)) :
    Module.finrank ℂ M ≤ rankOn D u M + corankP D u := by
  unfold rankOn corankP
  set P := (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)
  have h := LinearMap.finrank_range_add_finrank_ker (P.domRestrict M)
  rw [LinearMap.range_domRestrict] at h
  have h2 : Module.finrank ℂ (LinearMap.ker (P.domRestrict M)) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    rw [← Submodule.finrank_map_subtype_eq M]
    refine Submodule.finrank_mono ?_
    rintro x ⟨y, hy, rfl⟩
    exact hy
  omega

theorem shareAt_iff {D : D7} {u : D.what₂.Word} {e : ℝ} : ShareAt D u e ↔ GlobalTheory.Core.Rk.DiagS D u e := by
  unfold ShareAt GlobalTheory.Core.Rk.DiagS
  rw [GlobalTheory.Core.Rk.d0_eq]
  refine ⟨fun h => h.1, fun h => ⟨h, (corankP_le_hsDev D u).trans h, fun M => ?_⟩⟩
  have h1 : (Module.finrank ℂ M : ℝ) ≤ (rankOn D u M : ℝ) + (corankP D u : ℝ) := by
    exact_mod_cast finrank_le_rankOn_add D u M
  have h2 := (corankP_le_hsDev D u).trans h
  linarith

theorem fullAt_of {D : D7} {u : D.what₂.Word} {L C c : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hc : c ≤ 1)
    (h : SDiagAt D u (gamL D L C) c) : FullAt D u L C c := by
  refine ⟨h, fun hf => shareAt_iff.2 ?_⟩
  have hG : 1 ≤ gamL D L C := Real.one_le_exp (by positivity)
  have e1 : 8 / gamL D L C = 8 * Real.exp (-(C * (D.R.m : ℝ) ^ 5 * D.R.f * L)) := by
    unfold gamL; rw [Real.exp_neg, div_eq_mul_inv]
  unfold GlobalTheory.Core.Rk.Small at hf
  rw [GlobalTheory.Core.Rk.d0_eq] at hf
  have e2 : Real.exp (-(2 * C * GlobalTheory.Core.Rk.mfL D L)) * gamL D L C ^ 2 = 1 := by
    unfold gamL GlobalTheory.Core.Rk.mfL; rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_one_iff]; push_cast; ring
  have := GlobalTheory.Core.Rk.diagS_of_sDiagAt D u _ c hG hc h (by
    calc (D.duS u : ℝ) * gamL D L C ^ 2
        ≤ D.what₂.Dstar * Real.exp (-(2 * C * GlobalTheory.Core.Rk.mfL D L)) * gamL D L C ^ 2 :=
          mul_le_mul_of_nonneg_right hf (by positivity)
      _ = D.what₂.Dstar := by rw [mul_assoc, e2, mul_one])
  rw [e1] at this
  exact this

theorem ShareAt.pu_ne_zero {D : D7} {u : D.what₂.Word} {e : ℝ} (h : ShareAt D u e) (he : e < 1) (hd : 0 < D.duS u) :
    D.s.Pu u ≠ 0 := by
  intro h0
  have h1 := h.2.2 ⊤
  have h2 : rankOn D u ⊤ = 0 := by unfold rankOn; rw [h0]; simp
  have h3 : Module.finrank ℂ (⊤ : Submodule ℂ (D.s.Cu u)) = D.duS u := by
    rw [finrank_top, ← GlobalTheory.Core.Rk.d0_eq]; rfl
  rw [h2, h3] at h1
  have : (0 : ℝ) < D.duS u := by exact_mod_cast hd
  push_cast at h1
  nlinarith

theorem shareL_lt_one {D : D7} {L C' Cl Cg cb Cu cT CT C c : ℝ} (h : GlobalTheory.Core.Deg.HypL D L C' Cl Cg cb Cu cT CT)
    (h8 : 8 ≤ C') (hC : 1 ≤ C) (hc : 1 / 2 ≤ c) : shareL D L C c < 1 := by
  obtain ⟨hL, hk, hmf, -⟩ := h
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have h5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hm 5)
  have hy : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by
    have : (32 : ℝ) * 1 * 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by gcongr
    linarith
  have hk' : (256 : ℝ) ≤ D.R.k := by nlinarith
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have a1 : 32 ≤ C * (D.R.m : ℝ) ^ 5 * D.R.f * L := by nlinarith
  have a2 : 32 ≤ c * D.R.k * D.R.f * Real.log D.R.k := by
    have : (1 / 2 : ℝ) * 256 * 1 * 1 ≤ c * D.R.k * D.R.f * Real.log D.R.k := by gcongr
    linarith
  have b : Real.exp (-32) ≤ 1 / 33 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (32 : ℝ)])
  have b1 := Real.exp_le_exp.2 (neg_le_neg a1)
  have b2 := Real.exp_le_exp.2 (neg_le_neg a2)
  unfold shareL
  linarith

example {D : D7} {u : D.what₂.Word} {L C' Cl Cg cb Cu cT CT C : ℝ} (h : HD D L C' Cl Cg cb Cu cT CT) (h8 : 8 ≤ C')
    (hC : 1 ≤ C) (hf : GlobalTheory.Core.Rk.Small D u L C) (h0 : D.s.Pu u = 0) : ¬ FullAt D u L C (1 / 2) := fun H =>
  (H.2 hf).pu_ne_zero (shareL_lt_one h.1 h8 hC le_rfl) (h.2.1.2.2.2.2.2.2.2.2.2.1 u) h0

example {D : D7} {u : D.what₂.Word} {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hK : Kmat D.s u u = ContinuousLinearMap.id ℂ (D.s.Cu u)) : FullAt D u L C (1 / 2) := by
  refine fullAt_of hL hC (by norm_num) ?_
  have hD : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos
  have hG : 0 < gamL D L C := Real.exp_pos _
  unfold SDiagAt GlobalTheory.Core.Rk.hsDev
  rw [hK, sub_self, GlobalTheory.hsNormSq_eq_sum_stdBasis]
  simp only [zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]
  positivity

example (D : D7) (L : ℝ) : shareL D L 0 0 = 14 := by simp [shareL]; norm_num

example (D : D7) (u : D.what₂.Word) : rankOn D u ⊥ = 0 := by simp [rankOn]

end GlobalTheory.Core.Diag
