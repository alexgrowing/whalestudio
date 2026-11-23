import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistAdmissible
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearityStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceInvariantNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalMatrixMoveAdmissibleUniformLevelStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.TwistBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

theorem abs_norm_eq (h : IsType Ψ) (t : E) :
    |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ τ : Ψ, ‖τ.1 t‖ ^ 2 := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ t
  have h3 : ∏ σ : E →+* ℂ, σ t = ∏ σ : E →ₐ[ℚ] ℂ, σ t :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl
  have h1 : |((Algebra.norm ℚ t : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ t‖ := by
    rw [← norm_prod, h3, ← h2, eq_ratCast, Complex.norm_ratCast]
  rw [h1, Finset.prod_coe_sort Ψ fun τ => ‖τ t‖ ^ 2, ← Finset.prod_mul_prod_compl Ψ,
    Finset.prod_pow, sq]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa using (h a).1 ha
  · intro a ha
    have := h a
    simp only [Finset.mem_compl] at ha
    tauto
  · intro a _; exact star_star a
  · intro a _; exact star_star a
  · intro a _; simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem isSB_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨s, hs, -, h1, h2⟩ := hΛ.2.2
  refine ⟨s * R, Nat.mul_pos hs h.pos.2, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_smul]
    exact (Base.mem_stdL _).1 (h1 _ (h.supp Λ hΛ x hx a)) k
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact h.per Λ hΛ x _ fun a => h2 _ ((Base.mem_stdL _).2 fun k => hy k a)

theorem bounded_of_adm {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M h.pos.1).1
  have h1 : ∀ c : Cls E n M, ∃ B : ℝ, ∀ x, ‖φ (Quot.out c).1 x‖ ≤ B := fun c => by
    obtain ⟨S, hS, hl⟩ := isSB_of_adm h (Quot.out c).2
    exact (ip_self_nonneg_and_bounds E _ _ S _ hS hl).2.2.2.2.1
  choose b hb using h1
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun Λ hΛ x => ?_⟩
  set c : Cls E n M := Quot.mk _ ⟨Λ, hΛ⟩ with hc
  obtain ⟨g, hg, hm⟩ := (Base.cls_eq_iff ⟨Λ, hΛ⟩ (Quot.out c)).1 (Quot.out_eq c).symm
  rw [← h.equiv g hg Λ hΛ _ (Quot.out c).2 hm x]
  exact ((hb c _).trans (hB ⟨c, rfl⟩)).trans (le_max_left _ _)

theorem det_ccT (a : Matrix (Fin N) (Fin N) E) : (ccT a).det = cc a.det := by
  rw [ccT, Matrix.det_transpose]
  exact ((IsCMField.complexConj E).toRingEquiv.toRingHom.map_det a).symm

theorem diag_mem_UU {a d : Matrix (Fin N) (Fin N) E} (h : ccT a * d = 1) :
    Matrix.fromBlocks a 0 0 d ∈ UU E N := by
  have h' : ccT d * a = 1 := by
    have := congrArg ccT h
    rwa [Base.ccT_mul, Base.ccT_ccT, Base.ccT_one] at this
  have e : ccT (Matrix.fromBlocks a 0 0 d : M2 E N) = Matrix.fromBlocks (ccT a) 0 0 (ccT d) := by
    ext (i | i) (j | j) <;> simp [ccT, cc]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h, h']

theorem exists_moved (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {φ : Fam E n N} (hφ : ∀ Λ ∈ Vset E n M, IsSB (φ Λ)) {a : Matrix (Fin N) (Fin N) E}
    (ha : a.det ≠ 0) (hψ : ∀ Λ ∈ Vset E n M, IsSB fun x => φ Λ (x * a))
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : ∃ Z' ∈ Hn Ψ N,
      swd Ψ M (fun Λ x => φ Λ (x * a)) Z' 0 0 = swd Ψ M φ Z 0 0 ∧
        detIm Z' = |((Algebra.norm ℚ a.det : ℚ) : ℝ)| * detIm Z := by
  have ha' : (ccT a).det ≠ 0 := by
    rw [det_ccT]; simpa [cc] using ha
  set d := (ccT a)⁻¹ with hd
  have had : ccT a * d = 1 := Matrix.mul_nonsing_inv _ ha'.isUnit
  have hdet : cc a.det * d.det = 1 := by rw [← det_ccT, ← Matrix.det_mul, had, Matrix.det_one]
  have hd0 : d.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  set γ : M2 E N := Matrix.fromBlocks a 0 0 d with hγ
  have hU : γ ∈ UU E N := diag_mem_UU had
  obtain ⟨-, hZ', hIm, -⟩ := (unitary_act_halfSpace E Ψ N γ hU).2 Z hZ
  have hden : ∀ τ, (hDen Ψ γ Z τ).det = τ.1 d.det := fun τ => by
    simp only [hDen, hγ, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.map_zero _ (map_zero τ.1), Matrix.zero_mul, zero_add]
    exact (τ.1.map_det d).symm
  set k : ℂ := ∏ τ : Ψ, τ.1 d.det ^ n with hk
  have hk0 : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by simpa using hd0)
  have hfac : hFac Ψ γ Z (0 : CM Ψ n N) 0 = k := by
    have h : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
    simp only [hFac, hden, h, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, hk]
  refine ⟨_, hZ', ?_, ?_⟩
  · have h1 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M φ hM hφ Z hZ).1 γ hU
    have h2 := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (fun Λ x => φ Λ (x * a)) hM hψ _ hZ').2.2.2.1 k
    apply mul_left_cancel₀ hk0
    rw [← h2, ← hfac, ← h1, hfac]
    refine Base.classSum_congr fun Λ hΛ => ?_
    have : weil Ψ γ (φ Λ) = (k • fun Λ x => φ Λ (x * a) : Fam E n N) Λ := by
      funext x
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn (φ Λ) (hφ Λ hΛ)).1 γ hU rfl x]
      simp [hγ, chiH, hk]
    simp only [this]
  · rw [← hIm, abs_norm_eq hΨ, mul_left_comm, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one, mul_one]
    intro τ _
    rw [hden, ← mul_pow, ← Complex.norm_conj (τ.1 a.det), ← Base.map_cc, ← norm_mul, ← map_mul,
      hdet]
    simp

omit [NumberField E] [IsCMField E] in

theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1.le

end GlobalTheory.SW.TwistBound

namespace GlobalTheory.SW

open TwistBound in

theorem twist_swd_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → ∀ (M R : ℕ) (φ : Fam E n (N + 1)), admitted M R φ → ∃ C : ℝ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) → ∀ Z ∈ Hn Ψ (N + 1), gidx 𝔛 ^ ((n : ℝ) / 2) * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ hφ
  obtain ⟨B, hB0, hB⟩ := bounded_of_adm hφ
  obtain ⟨c, C₁, -, h1⟩ := GlobalTheory.T.exists_rational_matrix_move_admissible_uniform_level E (N + 1)
  obtain ⟨C₂, h2⟩ := GlobalTheory.T.siegelWeil_difference_invariant_norm_bounded E Ψ hΨ n N hn hN hSW M (R * c)
  refine ⟨max C₁ 0 ^ ((n : ℝ) / 2) * (C₂ * B), fun 𝔛 hfg hag Z hZ => ?_⟩
  obtain ⟨a, ha, hidx, hadm⟩ := h1 n M R φ 𝔛 hφ hfg hag
  obtain ⟨-, -, -, hpos, ⟨R', hR'⟩, -⟩ := twist_admissible E n (N + 1) M R φ 𝔛 hφ hfg hag
  obtain ⟨Z', hZ', e1, e2⟩ := exists_moved hΨ hn hN hφ.pos.1 (fun Λ hΛ => isSB_of_adm hR' hΛ) ha
    (fun Λ hΛ => isSB_of_adm hadm hΛ) hZ
  have h3 := h2 _ hadm B (fun Λ hΛ x => by
    unfold twist
    split_ifs
    · exact hB Λ hΛ _
    · simpa using hB0) Z' hZ'
  have hD := detIm_nonneg hZ
  replace h3 : ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z' ^ ((n : ℝ) / 2) ≤ C₂ * B := by
    rw [← e1]; exact h3
  rw [e2, Real.mul_rpow (abs_nonneg _) hD] at h3
  have h4 : gidx 𝔛 ^ ((n : ℝ) / 2) ≤
      max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) := by
    rw [← Real.mul_rpow (le_max_right _ _) (abs_nonneg _)]
    exact Real.rpow_le_rpow hpos.le
      (hidx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
  have h5 : 0 ≤ max C₁ 0 ^ ((n : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  calc _ ≤ (max C₁ 0 ^ ((n : ℝ) / 2) * |((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2)) *
        ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) := by gcongr
    _ = max C₁ 0 ^ ((n : ℝ) / 2) * (‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ *
        (|((Algebra.norm ℚ a.det : ℚ) : ℝ)| ^ ((n : ℝ) / 2) * detIm Z ^ ((n : ℝ) / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 h5

end GlobalTheory.SW
