import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS.Lat

open GlobalTheory.CompanionTheory.WS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_ball_iff {n : ℤ} {x : F} :
    x ∈ valBall F n ↔ normalizedValuation F x ≤ WithZero.exp (-n) := Iff.rfl

theorem mem_int_iff {a : F} : a ∈ 𝒪[F] ↔ normalizedValuation F a ≤ 1 := by
  have h := @mem_valBall_zero_iff F _ _ _ _ a
  rw [mem_ball_iff] at h
  simpa using h.symm

theorem val_unif : normalizedValuation F (unifUnit F : F) = WithZero.exp (-1 : ℤ) := by
  have h := @ord_unifUnit F _ _ _ _
  have h0 : normalizedValuation F (unifUnit F : F) ≠ 0 := by
    simp
  have hl : WithZero.log (normalizedValuation F (unifUnit F : F)) = -1 := by
    unfold ord at h
    omega
  rw [← hl, WithZero.exp_log h0]

theorem val_zpow (n : ℤ) :
    normalizedValuation F (((unifUnit F ^ n : Fˣ)) : F) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, val_unif, ← WithZero.exp_zsmul]
  simp

theorem mul_inv_le_one_iff {a b : F} (hb : b ≠ 0) :
    normalizedValuation F (a * b⁻¹) ≤ 1 ↔ normalizedValuation F a ≤ normalizedValuation F b := by
  rw [map_mul, map_inv₀, ← div_eq_mul_inv]
  exact div_le_one₀ (zero_lt_iff.2 (by simpa using hb))

theorem rowAct_mul (g h : GL (Fin 2) F) (v : F × F) :
    rowAct (g * h) v = rowAct h (rowAct g v) := by
  simp only [rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem exists_of_mem (n : ℤ) (x : F × F) (hx : x ∈ Ln F n) :
    ∃ h : GL (Fin 2) F, spanSet n x = rowAct h ⁻¹' Ln F 0 := by
  obtain ⟨p, hp, hwp⟩ : ∃ p : F, p ≠ 0 ∧ normalizedValuation F p = WithZero.exp (-n) :=
    ⟨_, Units.ne_zero _, val_zpow n⟩
  have hdet : (!![p⁻¹, 0; 0, p⁻¹] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using hp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  ext ⟨v₁, v₂⟩
  have hact : rowAct (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) (v₁, v₂)
      = (v₁ * p⁻¹, v₂ * p⁻¹) := by
    simp [rowAct, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hball : ∀ y : F, y * p⁻¹ ∈ valBall F 0 ↔ y ∈ valBall F n := fun y => by
    rw [mem_ball_iff, mem_ball_iff, ← hwp]
    simpa using mul_inv_le_one_iff hp
  simp only [Set.mem_preimage, hact, Ln, spanSet, Set.mem_setOf_eq, hball]
  constructor
  · rintro ⟨a, ha, h₁, h₂⟩
    have hax : ∀ y ∈ valBall F n, a * y ∈ valBall F n := fun y hy => by
      rw [mem_ball_iff, map_mul]
      exact mul_le_of_le_one_left' (mem_int_iff.1 ha) |>.trans hy
    have e₁ := add_mem h₁ (hax _ hx.1)
    have e₂ := add_mem h₂ (hax _ hx.2)
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, sub_add_cancel] at e₁ e₂
    exact ⟨e₁, e₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨0, zero_mem _, by simpa using h₁, by simpa using h₂⟩

theorem exists_of_lt (n : ℤ) (x₁ x₂ : F)
    (h21 : normalizedValuation F x₂ ≤ normalizedValuation F x₁)
    (hn : WithZero.exp (-n) < normalizedValuation F x₁) :
    ∃ h : GL (Fin 2) F, spanSet n (x₁, x₂) = rowAct h ⁻¹' Ln F 0 := by
  have hx : x₁ ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨p, hp, hwp⟩ : ∃ p : F, p ≠ 0 ∧ normalizedValuation F p = WithZero.exp (-n) :=
    ⟨_, Units.ne_zero _, val_zpow n⟩
  have hdet : (!![x₁⁻¹, -(x₂ * x₁⁻¹ * p⁻¹); 0, p⁻¹] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using ⟨hx, hp⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
  ext ⟨v₁, v₂⟩
  have hact : rowAct (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) (v₁, v₂)
      = (v₁ * x₁⁻¹, (v₂ - v₁ * x₁⁻¹ * x₂) * p⁻¹) := by
    simp only [rowAct, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    ext
    · simp
    · simp
      ring
  have hq : normalizedValuation F (x₂ * x₁⁻¹) ≤ 1 := (mul_inv_le_one_iff hx).2 h21
  have hball : ∀ y : F, y * p⁻¹ ∈ valBall F 0 ↔ y ∈ valBall F n := fun y => by
    rw [mem_ball_iff, mem_ball_iff, ← hwp]
    simpa using mul_inv_le_one_iff hp
  simp only [Set.mem_preimage, hact, Ln, spanSet, Set.mem_setOf_eq, hball]
  constructor
  · rintro ⟨a, ha, h₁, h₂⟩
    simp only [Prod.mk_sub_mk, Prod.smul_mk, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd] at h₁ h₂
    have he : normalizedValuation F ((v₁ - a * x₁) * x₁⁻¹) ≤ 1 :=
      (mul_inv_le_one_iff hx).2 ((mem_ball_iff.1 h₁).trans hn.le)
    have hv : v₁ * x₁⁻¹ = a + (v₁ - a * x₁) * x₁⁻¹ := by
      field_simp
      ring
    have hw : v₂ - v₁ * x₁⁻¹ * x₂ = (v₂ - a * x₂) - (v₁ - a * x₁) * (x₂ * x₁⁻¹) := by
      field_simp
      ring
    refine ⟨?_, ?_⟩
    · rw [mem_ball_iff, hv]
      simpa using Valuation.map_add_le _ (mem_int_iff.1 ha) he
    · rw [hw]
      refine sub_mem h₂ ?_
      rw [mem_ball_iff, map_mul]
      exact (mul_le_of_le_one_right' hq).trans h₁
  · rintro ⟨h₁, h₂⟩
    refine ⟨v₁ * x₁⁻¹, mem_int_iff.2 ?_, ?_, ?_⟩
    · rw [mem_ball_iff] at h₁
      simpa using h₁
    · have : v₁ - v₁ * x₁⁻¹ * x₁ = 0 := by
        field_simp
        ring
      simpa [this] using zero_mem (valBall F n)
    · simpa [mul_comm, mul_assoc, mul_left_comm] using h₂

end GlobalTheory.CompanionTheory.WS.Lat

namespace GlobalTheory.CompanionTheory.WS

theorem spanSet_eq_preimage_Ln (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) :
    ∃ h : GL (Fin 2) F, spanSet n x = rowAct h ⁻¹' Ln F 0 := by
  by_cases hx : x ∈ Ln F n
  · exact Lat.exists_of_mem n x hx
  have hx' : ¬ (normalizedValuation F x.1 ≤ WithZero.exp (-n) ∧
      normalizedValuation F x.2 ≤ WithZero.exp (-n)) := hx
  rcases le_total (normalizedValuation F x.2) (normalizedValuation F x.1) with h | h
  · have hn : WithZero.exp (-n) < normalizedValuation F x.1 := by
      by_contra hc
      have hc' := not_lt.1 hc
      exact hx' ⟨hc', h.trans hc'⟩
    exact Lat.exists_of_lt n x.1 x.2 h hn
  · have hn : WithZero.exp (-n) < normalizedValuation F x.2 := by
      by_contra hc
      have hc' := not_lt.1 hc
      exact hx' ⟨h.trans hc', hc'⟩
    obtain ⟨g, hg⟩ := Lat.exists_of_lt n x.2 x.1 h hn
    have hdet : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet * g, ?_⟩
    ext ⟨v₁, v₂⟩
    have hact : rowAct (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) (v₁, v₂) = (v₂, v₁) := by
      simp [rowAct, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    have hm : rowAct g (v₂, v₁) ∈ Ln F 0 ↔ (v₂, v₁) ∈ spanSet n (x.2, x.1) := by
      rw [hg]
      rfl
    rw [Set.mem_preimage, Lat.rowAct_mul, hact, hm]
    simp only [spanSet, Ln, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
      Prod.smul_snd]
    constructor
    · rintro ⟨a, ha, h₁, h₂⟩
      exact ⟨a, ha, h₂, h₁⟩
    · rintro ⟨a, ha, h₁, h₂⟩
      exact ⟨a, ha, h₂, h₁⟩

end GlobalTheory.CompanionTheory.WS
