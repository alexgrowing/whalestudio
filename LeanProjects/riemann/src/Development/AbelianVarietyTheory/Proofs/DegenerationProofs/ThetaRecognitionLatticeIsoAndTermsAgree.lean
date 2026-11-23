import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMatchingExistsRightTorusTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationSeriesTermsNestStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTermStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem txT_tendsto {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hq : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : Tendsto (N.txT m p) cofinite (𝓝 0) := by
  have h0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine squeeze_zero_norm (a := fun χ => Real.exp (-q χ)) (fun χ => ?_)
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq.pos))
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 m hm p χ, hp, toAdd_one, zero_add, ← natCast_zsmul, QuadraticMap.map_smul]
  have : (((m : ℤ) * (m : ℤ)) • q χ) / (m : ℝ) ^ 2 = q χ := by
    rw [zsmul_eq_mul]; push_cast; field_simp
  rw [this]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hq.th _)

theorem exists_txT_ne {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by
  obtain ⟨t, ht, hx⟩ := hT.good (N.c x)
  obtain ⟨b, rfl⟩ := hT.div t
  obtain ⟨γ, rfl⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT 0).1 b
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ ^ (n ^ 1) ^ 2)).2 (by rw [NumD.Gt.pow_b, pow_one, sq, pow_mul, ht])
  obtain ⟨s, rfl⟩ := exists_char_pow (k := (n ^ 1) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')) s
  refine ⟨⟨(1, γ * (N.tor s)⁻¹), ?_⟩, rfl, ?_⟩
  · rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
    exact N.io_zero.symm
  · rw [← norm_ne_zero_iff, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 _ hn.pow]
    refine mul_ne_zero (Real.exp_pos _).ne' ?_
    simp [hx]

theorem tx_twist {C : Type} [NormedField C] {N : NumD C} {M m : ℕ} (hM : Odd M) (hm : Odd m)
    (p : N.QT (m ^ 2)) (P : N.QT ((M * m) ^ 2)) (hp : p.1.1 = 1) (hP : P.1.1 = 1) (h : p.1.2 = P.1.2 ^ M)
    (s : Multiplicative N.X →* Cˣ) (hs : s ^ (M * m) ^ 2 = 1) :
    N.tx (M * m) (P * N.qTor s hs) = ∑' β, N.txT m p β * ((s ^ (M * m)) (Multiplicative.ofAdd β) : C) := by
  refine tsum_congr fun β => ?_
  rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (M * m) (hM.mul hm) P (P * N.qTor s hs) β).2 s (mul_one _) rfl,
    GlobalTheory.T.degenerationSeriesTerms_nest C N M m hM hm P p (by rw [hP, hp, one_pow]) h, hP, map_one, one_pow, one_mul, toAdd_one, zero_add,
    ofAdd_nsmul, map_pow, mul_comm]
  rfl

section
variable {C : Type} [NormedField C] [IsAlgClosed C] {N N' : NumD C} {n g : ℕ} (μ : Match N N' n)

theorem tx_eq {m : ℕ} (hm : ∃ j, m = n ^ j) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r _ p p') :
    N'.tx m p' = μ.c₀ * N.tx m p := by
  obtain ⟨j, rfl⟩ := hm
  exact μ.tx j p p' h

theorem twisted_eq (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (hA : μ.A) (i j : ℕ)
    {p : N.QT ((n ^ j) ^ 2)} {p' : N'.QT ((n ^ j) ^ 2)} (h : μ.r _ p p') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1)
    {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ i = 1} {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ i = 1}
    (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    ∑' β, N'.txT (n ^ j) p' β * (t' (Multiplicative.ofAdd β) : C) =
      μ.c₀ * ∑' β, N.txT (n ^ j) p β * (t (Multiplicative.ofAdd β) : C) := by
  have h0 : ∀ a, n ^ a ≠ 0 := fun a => pow_ne_zero _ hn.pos.ne'
  have hL0 : n ^ i * n ^ j ≠ 0 := mul_ne_zero (h0 _) (h0 _)
  have hL : ∃ a, (n ^ i * n ^ j) ^ 2 = n ^ a := ⟨(i + j) * 2, by ring⟩
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT i).2.1 p.1.2
  have hp1 : p.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N.mem_QT.1 p.2, hp]; exact N.io_zero
  have hp1' : p'.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N'.mem_QT.1 p'.2, hp']; exact N'.io_zero
  let P : N.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, γ), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = n ^ i * ((n ^ j) ^ 2 * n ^ i) by ring, pow_mul, hγ, pow_mul, hp1, one_pow]
    exact N.io_zero.symm⟩
  obtain ⟨P', hPP, hP'⟩ := tot_G μ hA hL P rfl
  let Q' : N'.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, p'.1.2), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = (n ^ j) ^ 2 * (n ^ i) ^ 2 by ring, pow_mul, hp1', one_pow]
    exact N'.io_zero.symm⟩
  have h1 : μ.r _ (P ^ n ^ i) Q' :=
    (r_incl μ (p := p) (p' := p') (q := P ^ n ^ i) (q' := Q') ((n ^ i) ^ 2) (by ring) (pow_ne_zero _ (h0 i)) (by rw [hp, one_pow]; exact one_pow _) hγ
      (by rw [hp', one_pow]) rfl).1 h
  have h2 : Q' = P' ^ n ^ i := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h1 (r_pow μ hL hPP _))
    (by change 1 = P'.1.1 ^ n ^ i; rw [hP', one_pow])
  have h3 : p'.1.2 = P'.1.2 ^ n ^ i := congrArg (fun q : N'.QT _ => q.1.2) h2
  obtain ⟨s, rfl⟩ := exists_char_pow hL0 t
  have hs : s ^ (n ^ i * n ^ j) ^ 2 = 1 := by rw [sq, pow_mul, pow_mul _ (n ^ i), ht, one_pow]
  obtain ⟨s', hs', hss⟩ := thetaMatching_exists_right_torus_torsion μ hA hL s hs
  have ht'' : t' ^ (n ^ i * n ^ j) ^ 2 = 1 := by
    rw [show (n ^ i * n ^ j) ^ 2 = n ^ i * (n ^ i * (n ^ j) ^ 2) by ring, pow_mul, ht', one_pow]
  have h4 : μ.r _ (N.qTor s hs ^ (n ^ i * n ^ j)) (N'.qTor t' ht'') :=
    (r_incl μ (p := N.qTor _ ht) (p' := N'.qTor t' ht') (q := N.qTor s hs ^ (n ^ i * n ^ j))
      (q' := N'.qTor t' ht'') (n ^ i * (n ^ j) ^ 2) (by ring) (mul_ne_zero (h0 i) (pow_ne_zero _ (h0 j)))
      ((one_pow _).trans (one_pow _).symm) (N.tor_pow _ _).symm (one_pow _).symm rfl).1 e
  have h5 := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h4 (r_pow μ hL hss _)) (one_pow _).symm
  have h6 : t' = s' ^ (n ^ i * n ^ j) :=
    N'.tor_injective ((congrArg (fun q : N'.QT _ => q.1.2) h5).trans (N'.tor_pow _ _).symm)
  rw [h6, ← tx_twist hn.pow hn.pow p P hp rfl hγ.symm s hs, ← tx_twist hn.pow hn.pow p' P' hp' hP' h3 s' hs']
  exact tx_eq μ ⟨i + j, (pow_add _ _ _).symm⟩ (μ.mul _ _ _ _ _ hPP hss)
end

theorem main : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  intro C _ _ _ _ N N' q q' n g g' hpr hn hn1 hq hq' hT hT' μ hA
  have hC : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  have hn0 := hpr.ne_zero
  have key : ∀ i j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)), μ.r _ p p' → p.1.1 = 1 → p'.1.1 = 1 →
      ∀ α α', Cl μ i α α' →
      ∑' z, N'.txT (n ^ j) p' (α' + n ^ i • z) = μ.c₀ * ∑' z, N.txT (n ^ j) p (α + n ^ i • z) := by
    intro i j p p' h hp hp' α α' hα
    obtain ⟨E, hE, hr⟩ := exists_torus_bij μ hn0 hA ⟨i, rfl⟩
    exact class_sum_eq (by rw [Nat.cast_pow, norm_pow, hn1, one_pow]) _ _ (txT_tendsto hq hn.pow p hp)
      (txT_tendsto hq' hn.pow p' hp') _ α α' E hE (fun t => hα.tor μ (hr t))
      fun t => twisted_eq μ hn hC hT hA i j h hp hp' (hr t)
  have tot : ∀ j x, ∃ x', Cl μ j x x' := fun j x => by
    obtain ⟨p, hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT j).2.2.1 x
    obtain ⟨p', h⟩ := μ.tot j p
    exact ⟨_, p, p', h, hp, rfl⟩
  have cotot : ∀ j x', ∃ x, Cl μ j x x' := fun j x' => by
    obtain ⟨p', hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' hC hT' j).2.2.1 x'
    obtain ⟨p, h⟩ := μ.cotot j p'
    exact ⟨_, p, p', h, rfl, hp⟩
  have hL : ∃ a, (n ^ 1) ^ 2 = n ^ a := ⟨2, by ring⟩
  have hf : ∀ x, ∃ x', ∀ j, Cl μ j x x' := fun x => by
    choose α hα using fun j => tot j x
    obtain ⟨p, hp, hx⟩ := exists_txT_ne hq hn hC hT x
    obtain ⟨p', h, hp'⟩ := tot_G μ hA hL p hp
    obtain ⟨x', hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
      μ.c₀ x α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).1 ⟨0, by simp⟩)
      fun i => key i 1 p p' h hp hp' _ _ (hα i)).2 (mul_ne_zero μ.c₀_ne hx)
    refine ⟨x', fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ 0 z
  have hg : ∀ x', ∃ x, ∀ j, Cl μ j x x' := fun x' => by
    choose α hα using fun j => cotot j x'
    obtain ⟨p', hp', hx⟩ := exists_txT_ne hq' hn hC hT' x'
    obtain ⟨p, h, hp⟩ := cotot_G μ hA hL p' hp'
    obtain ⟨x, hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq' hn.pow p' hp') (txT_tendsto hq hn.pow p hp)
      μ.c₀⁻¹ x' α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).2 ⟨0, by simp⟩)
      fun i => by rw [key i 1 p p' h hp hp' _ _ (hα i), inv_mul_cancel_left₀ μ.c₀_ne]).2
      (mul_ne_zero (inv_ne_zero μ.c₀_ne) hx)
    refine ⟨x, fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ z 0
  obtain ⟨e, he, -⟩ := existsUnique_addEquiv_of_compatible_congr N.X N'.X n hpr.two_le (Cl μ) tot cotot
    (fun _ _ _ _ _ h h' => h.add μ h') (fun _ _ _ _ _ h h' => h.cong μ hA h') (fun _ _ _ _ _ h => h.shift μ _ _) hf hg
  refine ⟨e, fun j p p' h => ((he j _).cong μ hA ⟨p, p', h, rfl, rfl⟩).1 ⟨0, by simp⟩, fun j p p' h hp hp' χ => ?_⟩
  exact (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
    μ.c₀ χ (fun _ => e χ) (fun j => ⟨0, by simp⟩) fun i => key i j p p' h hp hp' _ _ (he i χ)).1 _
    fun j => ⟨0, by simp⟩

end GlobalTheory.MatchTerm
