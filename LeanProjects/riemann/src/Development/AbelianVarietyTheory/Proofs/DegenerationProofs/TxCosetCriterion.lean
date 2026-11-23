import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionTwistTsumNormGe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTermStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CosetCrit

theorem posDef_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) : q.PosDef := by
  intro x hx
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • x := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually_gt_atTop 0
  obtain ⟨k, hk⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul] at hk
  have : (0 : ℝ) ≤ ((k * k : ℤ) : ℝ) := by exact_mod_cast mul_self_nonneg k
  nlinarith [not_lt.1 h]

theorem tendsto_class {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (y : X) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun χ => q (y + m • χ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have h1 : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (by exact_mod_cast hm : (m : ℤ) ≠ 0) h1
  exact hq.comp hinj.tendsto_cofinite

theorem exists_char_pow {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    (t : Multiplicative X →* Cˣ) {k : ℕ} (hk : 0 < k) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hroot : ∀ u : Cˣ, ∃ v : Cˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using hroot
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive Cˣ :=
    e.constr ℤ fun i => Additive.ofMul (r (t (Multiplicative.ofAdd (e i))))
  have hf : k • f = (MonoidHom.toAdditiveRight t).toIntLinearMap := e.ext fun i => by
    simp only [f, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] in

theorem norm_txT_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) := by
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)

omit [CompleteSpace C] [IsAlgClosed C] in

theorem norm_tx_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Real.exp_pos _).le fun χ => ?_
  refine (norm_txT_le hI hm p χ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_right (h₀ χ) (by positivity)

omit [IsUltrametricDist C] [CompleteSpace C] in

theorem exists_lift {n g : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (j : ℕ) {t : N.A} (ht : t ^ n = 1) :
    ∃ γ : N.Gt, γ ^ n ^ (j + 1) = 1 ∧ γ.b ^ n ^ j = t := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn hT j
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨γ₀, rfl⟩ := h1 t
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ₀ ^ n)).2 (by rw [NumD.Gt.pow_b, ht])
  obtain ⟨s', rfl⟩ := exists_char_pow s hn0
  obtain ⟨γ, hγ⟩ := h2 (γ₀ * (N.tor s')⁻¹)
  refine ⟨γ, ?_, ?_⟩
  · rw [pow_succ, pow_mul, hγ, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
  · rw [← NumD.Gt.pow_b, hγ]
    simp

theorem exists_norm_tx_ge (hI : N.Int q) {n g : ℕ} (hp : n.Prime) (ho : Odd n) (hn : ‖(n : C)‖ = 1)
    (hT : N.Tors n g) {j : ℕ} (hj : 1 ≤ j) (p : N.QT ((n ^ j) ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ)) :
    ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      Real.exp (-(q (p.1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤ ‖N.tx (n ^ j) (p * h)‖ := by
  have hn0 : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hm : Odd (n ^ j) := ho.pow
  have hm0 : 0 < n ^ j := hm.pos
  have hP := posDef_of_tendsto hI.pos
  have hQ : ∀ γ : N.Gt, γ ^ n ^ (j + 1) = 1 → (1, γ) ∈ N.QT ((n ^ j) ^ 2) := fun γ hγ => by
    obtain ⟨c, hc⟩ : n ^ (j + 1) ∣ (n ^ j) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow n (by omega)
    rw [NumD.mem_QT, hc, pow_mul, hγ, one_pow]
    exact N.io_zero.symm
  obtain ⟨t, ht, hth⟩ := hT.good (N.c χ₀ * p.1.2.b ^ n ^ j)
  obtain ⟨γ, hγ, hγb⟩ := exists_lift hn0 hT j ht
  set p₁ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ), hQ γ hγ⟩ with hp₁
  have hy : p₁.1.1 = p.1.1 := mul_one _
  have hb : p₁.1.2 = p.1.2 * γ := rfl
  haveI : NeZero (n : C) := ⟨hn0⟩
  haveI : NeZero n := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C n
  have hr : ∀ x : ℝ, Real.exp (-1) ^ x = Real.exp (-x) := fun x => by
    rw [← Real.exp_mul, neg_one_mul]
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨s, hs, hle⟩ := GlobalTheory.exists_torsion_twist_tsum_norm_ge C N.X n ζ hp.pos hn hζ
    (N.txT (n ^ j) p₁) (fun χ => q (p.1.1.toAdd + n ^ j • χ) / ((n ^ j : ℕ) : ℝ) ^ 2) (Real.exp (-1))
    (Real.exp_pos _) (by simpa using Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num))
    ((tendsto_class hI.pos _ hm0.ne').atTop_div_const hsq)
    (fun χ => by rw [hr, ← hy]; exact norm_txT_le hI hm p₁ χ) χ₀
    (by rw [hr, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 _ hm p₁ χ₀, hy, hb, NumD.Gt.mul_b, mul_pow, hγb, ← mul_assoc, hth,
          mul_one])
    (fun μ hμ => by
      refine div_lt_div_of_pos_right ?_ hsq
      have := GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero hP (N := ((n ^ j : ℕ) : ℤ)) (n := (n : ℤ))
        (a := p.1.1.toAdd + n ^ j • χ₀) (by exact_mod_cast hm0.ne') (by exact_mod_cast hp.two_le)
        (fun w => by rw [natCast_zsmul, add_assoc, ← smul_add]; exact h₀ _) hμ
      rwa [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul, add_assoc, ← smul_add] at this)
  obtain ⟨s', rfl⟩ := exists_char_pow s hm0
  have hs' : s' ^ n ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hs]
  have hγ' : (γ * N.tor s') ^ n ^ (j + 1) = 1 := by
    rw [mul_pow, hγ, ← N.tor_pow, hs', N.tor_one, mul_one]
  refine ⟨⟨(1, γ * N.tor s'), hQ _ hγ'⟩, rfl, hγ', ?_⟩
  set p₂ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ * N.tor s'), hQ _ hγ'⟩ with hp₂
  have hone : ∀ x, ‖(s' x : C)‖ = 1 := fun x => by
    have h1 : ‖(s' x : C)‖ ^ n ^ (j + 1) = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hs', MonoidHom.one_apply,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hterm : ∀ χ, N.txT (n ^ j) p₂ χ =
      ((s' p₁.1.1 : C) ^ (((n ^ j) ^ 2 - 1) / 2) * (s' p₁.1.1 : C)) *
        (N.txT (n ^ j) p₁ χ * ((s' ^ n ^ j) (Multiplicative.ofAdd χ) : C)) := fun χ => by
    rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (n ^ j) hm p₁ p₂ χ).2 s' ((mul_one _).trans hy.symm) (mul_assoc _ _ _).symm,
      ofAdd_add, ofAdd_nsmul, map_mul, map_pow, ofAdd_toAdd, MonoidHom.pow_apply]
    push_cast
    ring
  rw [NumD.tx, funext hterm, tsum_mul_left, norm_mul, norm_mul, norm_pow, hone, one_pow, one_mul, one_mul,
    ← hr]
  exact hle

end GlobalTheory.CosetCrit

theorem GlobalTheory.tx_coset_criterion : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  intro C _ _ _ _ N q hI n g hp ho hn hT j hj
  have hm : Odd (n ^ j) := ho.pow
  have hP := GlobalTheory.CosetCrit.posDef_of_tendsto hI.pos
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by have := hm.pos; positivity
  have hmin : ∀ p : N.QT ((n ^ j) ^ 2), ∃ χ₀, ∀ χ,
      q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ) := fun p =>
    (GlobalTheory.CosetCrit.tendsto_class hI.pos _ hm.pos.ne').exists_forall_le
  have h1 : ∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 := fun p => by
    obtain ⟨χ₀, h₀⟩ := hmin p
    refine (GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
    exact div_nonneg (hP.nonneg _) hsq.le
  refine ⟨fun p => ⟨h1 p, fun h => ?_⟩, fun p hp1 => ?_, fun p => ?_⟩
  · obtain ⟨χ₀, h₀⟩ := hmin p
    have h2 := GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀
    rw [h, Real.one_le_exp_iff, neg_nonneg] at h2
    refine ⟨-χ₀, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    by_contra h3
    exact (div_pos (hP _ h3) hsq).not_ge h2
  · obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p (χ₀ := 0) (fun χ => by
      rw [hp1, toAdd_one, smul_zero, add_zero, map_zero]
      exact hP.nonneg _)
    refine ⟨h, ha, hb, le_antisymm (h1 _) ?_⟩
    simpa [hp1] using hc
  · obtain ⟨χ₀, h₀⟩ := hmin p
    obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p h₀
    exact ⟨h, ha, hb, norm_pos_iff.1 ((Real.exp_pos _).trans_le hc)⟩
