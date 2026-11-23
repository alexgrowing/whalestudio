import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

noncomputable section

namespace GlobalTheory.ShellPiece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_le_one_of_mem {t : k} (h : t ∈ 𝒪[k]) : valuation k t ≤ 1 := h

theorem diagGL_mem_KO {a : ℕ} (c : Fin a → kˣ) (hc : ∀ j, valuation k (c j : k) = 1) :
    diagGL c ∈ KO k (Fin a) := by
  rw [mem_KO_iff]
  refine ⟨fun r s => ?_, fun r s => ?_⟩
  · show valuation k ((diagGL c).val r s) ≤ 1
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (hc r).le
    · simp
  · show valuation k (((diagGL c)⁻¹ : GL (Fin a) k).val r s) ≤ 1
    rw [show ((diagGL c)⁻¹ : GL (Fin a) k).val = diagonal fun j => (((c j)⁻¹ : kˣ) : k) from rfl, diagonal_apply]
    split_ifs
    · simp [hc r]
    · simp

end GlobalTheory.ShellPiece

open GlobalTheory.ShellPiece in

theorem GlobalTheory.ShellPiece.setIntegral_coset_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ → ∀ (ν : kˣ →* ℂˣ) (a : ℕ) (μ : Measure (GL (Fin a) k))
    [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ) (M : ℤ), IsPeriodic ϖ M φ →
    ∀ (n : Fin a → ℤ) (i : Fin a), M ≤ n i → ∀ u : kˣ, valuation k (u : k) = 1 → ν u ≠ 1 →
    ∀ x ∈ KO k (Fin a), ∀ z : ℂ,
      ∫ g in {g : GL (Fin a) k | (x * diagGL (fun i => ϖ ^ n i))⁻¹ * g ∈ KO k (Fin a)},
        φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ ϖ hϖ ν a μ _ φ M hφ n i hi u hu hν x hx z
  set d : GL (Fin a) k := diagGL (fun j => ϖ ^ n j) with hd
  set D : GL (Fin a) k := diagGL (Pi.mulSingle i u) with hD
  have hDK : D ∈ KO k (Fin a) := diagGL_mem_KO _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hu
    · simp [Pi.mulSingle_eq_of_ne h]
  have hcomm : Commute d D := Units.ext (by simp [hd, hD, diagonal_mul_diagonal, mul_comm])
  set k0 := x * D * x⁻¹ with hk0
  have hk0K : k0 ∈ KO k (Fin a) := mul_mem (mul_mem hx hDK) (inv_mem hx)
  set S := {g : GL (Fin a) k | (x * d)⁻¹ * g ∈ KO k (Fin a)} with hS
  have key : ∀ g, (x * d)⁻¹ * (k0 * g) = D * ((x * d)⁻¹ * g) := fun g => by
    have h1 : d⁻¹ * D = D * d⁻¹ := (hcomm.inv_left).eq
    calc (x * d)⁻¹ * (k0 * g) = d⁻¹ * D * (x⁻¹ * g) := by rw [hk0]; group
      _ = D * d⁻¹ * (x⁻¹ * g) := by rw [h1]
      _ = D * ((x * d)⁻¹ * g) := by group
  have hpre : (fun g => k0 * g) ⁻¹' S = S := by
    ext g
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, key]
    exact Subgroup.mul_mem_cancel_left _ hDK
  have hdetD : gdet D = u := by
    rw [hD, gdet, det_diagGL]
    simp
  have hdetk0 : gdet k0 = u := by
    rw [hk0, gdet_mul, gdet_mul, hdetD, mul_comm (gdet x), mul_assoc, ← gdet_mul, mul_inv_cancel]
    simp

  have hϖ1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have hpow : valuation k ((ϖ ^ n i : kˣ) : k) ≤ valuation k ((ϖ ^ M : kˣ) : k) := by
    have e : ϖ ^ n i = ϖ ^ M * ϖ ^ (n i - M).toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← _root_.zpow_add]; congr 1; ring
    rw [e, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow]
    exact mul_le_of_le_one_right' (pow_le_one₀ zero_le hϖ1)
  have hu1 : valuation k ((u : k) - 1) ≤ 1 :=
    ((valuation k).map_sub _ _).trans (max_le hu.le (by simp))
  have hZ : ∀ y ∈ KO k (Fin a), x.val * ((D.val - 1) * d.val) * y.val ∈ scaledInt ϖ a M := by
    intro y hy r s
    have e1 : (D.val - 1) * d.val = diagonal fun j => ((((Pi.mulSingle i u : Fin a → kˣ) j : kˣ) : k) - 1) * ((ϖ ^ n j : kˣ) : k) := by
      rw [hD, hd, diagGL_val, diagGL_val]
      ext p q
      by_cases hpq : p = q
      · subst hpq; simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
      · simp [Matrix.mul_apply, diagonal_apply, Matrix.sub_apply, Matrix.one_apply, hpq]
    rw [e1, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [mul_diagonal, Pi.mulSingle_eq_same, map_mul, map_mul, map_mul]
      have hx1 := val_le_one_of_mem ((mem_KO_iff x).1 hx |>.1 r i)
      have hy1 := val_le_one_of_mem ((mem_KO_iff y).1 hy |>.1 i s)
      calc _ ≤ 1 * (1 * valuation k ((ϖ ^ n i : kˣ) : k)) * 1 := by gcongr
        _ ≤ _ := by simpa using hpow
    · intro j _ hj
      simp [mul_diagonal, Pi.mulSingle_eq_of_ne hj]
    · simp
  have hF : ∀ g ∈ S, φ (k0 * g).val * (ν (gdet (k0 * g)) : ℂ) * apow (gdet (k0 * g)) z =
      (ν u : ℂ) * (φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    intro g hg
    set y := (x * d)⁻¹ * g with hy
    have hyK : y ∈ KO k (Fin a) := hg
    have hg' : g = x * d * y := by rw [hy]; group
    have hv : (k0 * g).val = g.val + x.val * ((D.val - 1) * d.val) * y.val := by
      have : k0 * g = x * D * d * y := by rw [hg', hk0]; group
      rw [this, hg']
      simp only [Units.val_mul]
      noncomm_ring
    rw [hv, hφ _ _ (hZ y hyK), gdet_mul, hdetk0, map_mul, Units.val_mul, apow_mul,
      apow_of_valuation_eq_one hu]
    ring
  have hSm : MeasurableSet S :=
    (isOpen_KO.preimage (continuous_const.mul continuous_id)).measurableSet
  have h := (measurePreserving_mul_left μ k0).setIntegral_preimage_emb (measurableEmbedding_mulLeft k0)
    (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) S
  rw [hpre, setIntegral_congr_fun hSm (fun g hg => hF g hg), integral_const_mul] at h
  have hne : (ν u : ℂ) - 1 ≠ 0 := sub_ne_zero.2 fun e => hν (Units.val_eq_one.1 e)
  have h2 : ((ν u : ℂ) - 1) * ∫ g in S, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
    rw [sub_mul, h]; ring
  exact (mul_eq_zero.1 h2).resolve_left hne

end
