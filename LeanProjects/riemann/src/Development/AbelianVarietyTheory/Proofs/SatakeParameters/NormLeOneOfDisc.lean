import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.ThLoc.ModelThree

theorem norm_add_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_sub_le_max' {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_lt {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K} (hlt : ‖α‖ < ‖β‖)
    (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  have hb : 0 < ‖β‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have h1 : ‖α ^ 2 - α * β‖ < ‖β ^ 2‖ := by
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
    · rw [norm_pow, norm_pow]; exact pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
    · rw [norm_mul, norm_pow, sq]; exact mul_lt_mul_of_pos_right hlt hb
  have h2 : ‖β ^ 2 + (α ^ 2 - α * β)‖ = ‖β ^ 2‖ := norm_add_of_lt h1
  have h3 : α ^ 2 - α * β + β ^ 2 = β ^ 2 + (α ^ 2 - α * β) := by ring
  rw [h3, h2, norm_pow] at hN
  have h4 : ‖β‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact ⟨(hlt.trans_le h4).le, h4⟩

theorem norm_le_one_of_disc {K : Type} [NormedField K] [IsUltrametricDist K] {α β : K}
    (h : ‖α * β * (α - β)‖ = 1) (hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1) : ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  rcases lt_trichotomy ‖α‖ ‖β‖ with hlt | heq | hgt
  · exact norm_le_one_of_lt hlt hN
  · have hc : ‖α - β‖ ≤ ‖α‖ := by
      refine (norm_sub_le_max' _ _).trans ?_
      rw [heq, max_self]
    rcases hc.lt_or_eq with hc | hc
    · have h1 : ‖(α - β) ^ 2‖ < ‖α * β‖ := by
        rw [norm_pow, norm_mul, ← heq, ← sq]
        exact pow_lt_pow_left₀ hc (norm_nonneg _) (by norm_num)
      have h2 : ‖α * β + (α - β) ^ 2‖ = ‖α * β‖ := norm_add_of_lt h1
      have h3 : α ^ 2 - α * β + β ^ 2 = α * β + (α - β) ^ 2 := by ring
      rw [h3, h2, norm_mul, ← heq] at hN
      have h4 : ‖α‖ ≤ 1 := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨h4, heq ▸ h4⟩
    · rw [norm_mul, norm_mul, hc, ← heq] at h
      have h4 : ‖α‖ ^ 3 = 1 := by rw [← h]; ring
      have h5 : ‖α‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
      exact ⟨h5.le, (heq ▸ h5).le⟩
  · have hN' : ‖β ^ 2 - β * α + α ^ 2‖ ≤ 1 := by
      have : β ^ 2 - β * α + α ^ 2 = α ^ 2 - α * β + β ^ 2 := by ring
      rw [this]; exact hN
    exact (norm_le_one_of_lt hgt hN').symm

theorem exists_roots {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (g2 g3 : K) :
    ∃ α β : K, 16 * (α ^ 2 - α * β + β ^ 2) = 12 * g2 ∧
      64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) = 216 * g3 := by
  let f : Polynomial K := Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C g2 * Polynomial.X - Polynomial.C g3
  have hdeg : f.degree ≠ 0 := by
    have h3 : f.natDegree = 3 := by
      simp only [f]
      compute_degree!
    intro h
    have h0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.2 h.le
    omega
  obtain ⟨e, he⟩ := IsAlgClosed.exists_root f hdeg
  have he' : 4 * e ^ 3 - g2 * e - g3 = 0 := by simpa [f, Polynomial.IsRoot] using he
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (g2 - 3 * e ^ 2) (n := 2) (by norm_num)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨(-3 * e + s) / 2, (-3 * e - s) / 2, ?_, ?_⟩
  · field_simp
    linear_combination (48 : K) * hs
  · have e1 : g3 = 4 * e ^ 3 - g2 * e := by linear_combination -he'
    rw [e1]
    field_simp
    linear_combination (-1728 * e : K) * hs

def twoTorsionModel {K : Type} [Field K] (α β : K) : WeierstrassCurve K := ⟨0, -(α + β), 0, α * β, 0⟩

theorem c₄_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₄ = 16 * (α ^ 2 - α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, twoTorsionModel]
  ring

theorem c₆_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).c₆ = 64 * (α + β) ^ 3 - 288 * (α + β) * (α * β) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, twoTorsionModel]
  ring

theorem Δ_model {K : Type} [Field K] (α β : K) :
    (twoTorsionModel α β).Δ = 16 * (α * β * (α - β)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, twoTorsionModel]
  ring

theorem norm_two : ‖(2 : ℂ_[3])‖ = 1 := by
  have e : (2 : ℂ_[3]) = algebraMap ℚ_[3] ℂ_[3] ((2 : ℕ) : ℚ_[3]) := by rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  norm_num

theorem exists_model (g2 g3 : ℂ_[3]) (hΔ : g2 ^ 3 - 27 * g3 ^ 2 = 1) (hj : ‖1728 * g2 ^ 3‖ ≤ 1) :
    ∃ W : WeierstrassCurve ℂ_[3], Formalism.L2.Th1.A.g₂ W = g2 ∧ Formalism.L2.Th1.A.g₃ W = g3 ∧ IntCurve W := by
  obtain ⟨α, β, h4, h6⟩ := exists_roots g2 g3
  have c4 : (twoTorsionModel α β).c₄ = 12 * g2 := by rw [c₄_model, h4]
  have c6 : (twoTorsionModel α β).c₆ = 216 * g3 := by rw [c₆_model, h6]
  have hD : (twoTorsionModel α β).Δ = 1 := by
    have hc := (twoTorsionModel α β).c_relation
    rw [c4, c6] at hc
    have : (1728 : ℂ_[3]) * (twoTorsionModel α β).Δ = 1728 * (g2 ^ 3 - 27 * g3 ^ 2) := by
      linear_combination hc
    exact (mul_left_cancel₀ (by norm_num) this).trans hΔ
  have n16 : ‖(16 : ℂ_[3])‖ = 1 := by
    have : (16 : ℂ_[3]) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, norm_two, one_pow]
  have hprod : ‖α * β * (α - β)‖ = 1 := by
    have h1 := congrArg norm hD
    rw [Δ_model, norm_mul, n16, one_mul, norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hN : ‖α ^ 2 - α * β + β ^ 2‖ ≤ 1 := by
    have e : (16 * (α ^ 2 - α * β + β ^ 2)) ^ 3 = 1728 * g2 ^ 3 := by rw [h4]; ring
    have h1 : ‖(16 * (α ^ 2 - α * β + β ^ 2)) ^ 3‖ ≤ 1 := by rw [e]; exact hj
    rw [norm_pow, norm_mul, n16, one_mul] at h1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨ha, hb⟩ := norm_le_one_of_disc hprod hN
  refine ⟨twoTorsionModel α β, ?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.A.g₂
    rw [c4]; field_simp
  · unfold Formalism.L2.Th1.A.g₃
    rw [c6]; field_simp
  · refine ⟨by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_, by simp [twoTorsionModel], ?_⟩
    · simp only [twoTorsionModel, norm_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    · simp only [twoTorsionModel, norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) hb
    · rw [hD, norm_one]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_iota_le_one (ι : ℂ ≃+* ℂ_[3]) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι x‖ ≤ 1 := by
  obtain ⟨f, hf, hr⟩ := hx
  refine norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  have h := congrArg (ι : ℂ →+* ℂ_[3]) hr
  rw [map_zero, Polynomial.hom_eval₂] at h
  have e : (@algebraMap ℤ ℂ_[3] _ _ (Ring.toIntAlgebra ℂ_[3])) = (ι : ℂ →+* ℂ_[3]).comp (algebraMap ℤ ℂ) :=
    Subsingleton.elim _ _
  rw [e]
  exact h

theorem goodModelThree : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[3], ∃ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hL ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
    obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) L hL'
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    rw [← e2, ← e3]
    exact h
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d L :=
    Formalism.L2.Th1.F.hasCMByScale D.host.d _ lam hlam (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ D.host.d ha hd hok.1
      (Formalism.L2.Th1.H.CmData.odd_b a₀ b₀ c₀ D.host.d hok.1 hok.2.2.1))
  have hd8 := hok.2.2.1
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv L) :=
    hIn.jInt D.host.d L hok.2.2.2.prime.squarefree (by omega) hcm
  have hj' : Formalism.L2.Th1.CM.jInv L = 1728 * L.g₂ ^ 3 := by
    unfold Formalism.L2.Th1.CM.jInv
    rw [hdisc, div_one]
  rw [hj'] at hj
  have hn := norm_iota_le_one ι hj
  have hΔ : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
    have := congrArg ι hdisc
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using this
  have hn' : ‖1728 * ι L.g₂ ^ 3‖ ≤ 1 := by
    simpa only [map_mul, map_pow, map_ofNat] using hn
  obtain ⟨W, h2, h3, hW⟩ := exists_model _ _ hΔ hn'
  exact ⟨W, ⟨h2, h3⟩, hW⟩

end GlobalTheory.ThLoc.ModelThree
