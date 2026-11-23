import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaEisensteinConvergeBoundedStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCuspsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleLatticeFamilyHermitianWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatSwdStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SwdTendstoZeroAtCuspsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHighStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearityStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace InvBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem exists_int_sum_type (hΨ : IsType Ψ) {t : E} (ht : IsIntegral ℤ t) (hc : cc t = t) :
    ∃ k : ℤ, ∑ τ : Ψ, τ.1 (2 * t) = k := by
  have h1 : IsIntegral ℤ (Algebra.trace ℚ E t) := Algebra.isIntegral_trace ht
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  refine ⟨k, ?_⟩
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := t)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ σ : E →+* ℂ, σ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom _ _) _ _ fun _ => rfl).symm
  have h4 : ∑ σ ∈ Ψᶜ, σ t = ∑ σ ∈ Ψ, σ t := by
    refine Finset.sum_bij' (fun σ _ => ComplexEmbedding.conjugate σ)
      (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      by_contra h
      exact (Finset.mem_compl.1 hσ) ((hΨ σ).2 h)
    · intro σ hσ
      exact Finset.mem_compl.2 ((hΨ σ).1 hσ)
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _
      have := Base.map_cc σ t
      rw [hc] at this
      simpa using this
  rw [h3, ← Finset.sum_add_sum_compl Ψ, h4, ← hk] at h2
  rw [Finset.sum_coe_sort Ψ (fun τ => τ (2 * t))]
  simp only [map_mul, map_ofNat, ← Finset.mul_sum]
  rw [two_mul, ← h2]
  simp

theorem chiH_eq_one (hΨ : IsType Ψ) (R : ℕ) {y : Matrix (Fin N) (Fin N) E} (hy : IntM y)
    (hc : ccT y = y) {x : Matrix (Fin n) (Fin N) E} (hx : IntM ((R : E) • x)) :
    chiH Ψ (((2 * R ^ 2 : ℕ) : E) • y) x = 1 := by
  set u := (R : E) • x with hu
  have e : (x * (((2 * R ^ 2 : ℕ) : E) • y) * ccT x).trace = 2 * (u * y * ccT u).trace := by
    have : ccT u = (R : E) • ccT x := by
      ext i j; simp [hu, ccT, cc]
    rw [this, hu]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    push_cast; ring
  have hi : IsIntegral ℤ (u * y * ccT u).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun b _ =>
      (IsIntegral.sum _ fun a _ => (hx k a).mul (hy a b)).mul (Base.isIntegral_cc (hx k b))
  have hr : cc (u * y * ccT u).trace = (u * y * ccT u).trace := by
    have h1 : ccT (u * y * ccT u) = u * y * ccT u := by
      rw [Base.ccT_mul, Base.ccT_mul, Base.ccT_ccT, hc, Matrix.mul_assoc]
    have h2 : ∀ w : Matrix (Fin n) (Fin n) E, cc w.trace = (ccT w).trace := fun w => by
      simp [Matrix.trace, ccT, cc]
    rw [h2, h1]
  obtain ⟨k, hk⟩ := exists_int_sum_type hΨ hi hr
  rw [chiH, e, hk, mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem exists_common_level {M R : ℕ} (hM : 0 < M) (hR : 0 < R) :
    ∃ R₀ : ℕ, 0 < R₀ ∧ ∀ φ : Fam E n N, admitted M R φ → ∀ c : Cls E n M,
      HasLevel R₀ (φ (Quot.out c).1) := by
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  choose s hs _ h1 h2 using fun c : Cls E n M => (Quot.out c).2.2.2
  refine ⟨(∏ c, s c) * R, Nat.mul_pos (Finset.prod_pos fun c _ => hs c) hR, fun φ hφ c => ?_⟩
  obtain ⟨m, hm⟩ : s c ∣ ∏ c, s c := Finset.dvd_prod_of_mem _ (Finset.mem_univ c)
  rw [hm]
  constructor
  · intro x hx k a
    have := Base.nat_smul_mem _ m (h1 c _ (hφ.supp _ (Quot.out c).2 x hx a))
    have := (Base.mem_stdL _).1 this k
    convert this using 1
    simp; ring
  · intro x y hy
    have := hφ.per _ (Quot.out c).2 x (((s c * m : ℕ) : E) • y) fun a => by
      have := Base.nat_smul_mem _ m (h2 c (yᵀ a) ((Base.mem_stdL _).2 fun k => hy k a))
      convert this using 1
      ext k; simp; ring
    rw [← this, smul_smul]
    congr 3
    push_cast; ring

omit [IsCMField E] in

theorem differentiableOn_of_isHeat {D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ} (hD : IsHeat Ψ D) :
    DifferentiableOn ℂ (fun Z : CF Ψ N N => D Z 0 0) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} := by
  have g : Differentiable ℂ (fun Z : CF Ψ N N => ((Z, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N)) :=
    differentiable_id.prodMk (differentiable_const _)
  have := DifferentiableOn.comp (s := {Z : CF Ψ N N | (Z : CM Ψ N N) ∈ Hn Ψ N}) hD.1
    g.differentiableOn fun Z hZ => hZ
  exact this

theorem bound_high (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * (N + 1) < n) (hS : SWAt Ψ n N)
    (M R : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ (N + 1) δ,
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  haveI : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  haveI := Fintype.ofFinite (Cls E n M)
  obtain ⟨R₀, hR₀, hL⟩ := exists_common_level (E := E) (n := n) (N := N + 1) hM hR
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded E Ψ hΨ n (N + 1) hn hN R₀ (δ / 4) hR₀ (by positivity)
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.decay_of_vanishing_at_cusps' E Ψ hΨ (N + 1) (2 * R₀ ^ 2) δ ((n : ℝ) / 2) (Nat.succ_pos N)
    (by positivity) hδ (by positivity)
  obtain ⟨R', C', -, hsb⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn 1 R one_pos hR
  refine ⟨C₂ * ((∑ c : Cls E n M, ‖(wt M (Quot.out c).1 : ℂ)‖) * (2 * C₁)),
    fun φ hφ B hB Z hZ => ?_⟩
  have hSB : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := fun Λ hΛ =>
    (hsb M Λ hΛ 1 Base.one_mem_UU (fun i j => by
      by_cases h : i = j <;> simp [h, isIntegral_one, isIntegral_zero])
      (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1
  rw [mul_assoc]
  refine hC₂ (fun Z => swd Ψ M φ Z 0 0) _ ?_ ?_ ?_ ?_ Z hZ
  · exact differentiableOn_of_isHeat (GlobalTheory.T.isHeat_swd_of_adm E Ψ hΨ n (N + 1) hn hN M R φ hφ)
  · intro y hy hc W hW
    have h := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM hSB W hW).2.1
      (((2 * R₀ ^ 2 : ℕ) : E) • y) (by
        conv_rhs => rw [← hc]
        ext i j; simp [ccT, cc])
    change swd Ψ M φ _ 0 0 = swd Ψ M φ W 0 0
    rw [← h]
    unfold swd classSum
    refine finsum_congr fun c => ?_
    have : (fun x => chiH Ψ (((2 * R₀ ^ 2 : ℕ) : E) • y) x * φ (Quot.out c).1 x) =
        φ (Quot.out c).1 := by
      funext x
      by_cases hx : φ (Quot.out c).1 x = 0
      · rw [hx, mul_zero]
      · rw [chiH_eq_one hΨ R₀ hy hc ((hL φ hφ c).1 x hx), one_mul]
    simp only [this]
  · intro W hW
    unfold swd classSum
    rw [finsum_eq_sum_of_fintype, mul_assoc, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨-, h1, h2⟩ := hC₁ _ (hL φ hφ c) B (hB _ (Quot.out c).2) W hW
    refine (norm_sub_le _ _).trans ?_
    linarith
  · exact GlobalTheory.T.tendsto_swd_pushZ_atTop_zero E Ψ hΨ n N hn hN hS M R φ hφ

theorem detIm_nonneg {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 ≤ detIm Z :=
  Finset.prod_nonneg fun τ _ => (Complex.le_def.1 (hZ τ).det_pos.le).1

end InvBound

theorem swd_invariant_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N →
    ∀ M R : ℕ, ∃ C : ℝ, ∀ φ : Fam E n (N + 1), admitted M R φ → ∀ B : ℝ,
      (∀ Λ ∈ Vset E n M, ∀ x, ‖φ Λ x‖ ≤ B) → ∀ Z ∈ Hn Ψ (N + 1),
        ‖swd Ψ M φ Z 0 0‖ * detIm Z ^ ((n : ℝ) / 2) ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn hN hS M R
  by_cases hMR : 0 < M ∧ 0 < R
  swap
  · exact ⟨0, fun φ hφ => (hMR hφ.pos).elim⟩
  obtain ⟨hM, hR⟩ := hMR
  obtain ⟨c, δ, hc, hδ, hred⟩ := GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high E Ψ hΨ (N + 1)
  obtain ⟨R', hadm⟩ := GlobalTheory.T.admissibleLatticeFamily_hermitianWeilAction E Ψ hΨ n (N + 1) hn c R hc
  obtain ⟨R'', C₁, -, hlev⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n (N + 1) hn c R hc hR
  obtain ⟨C₂, hC₂⟩ := InvBound.bound_high hΨ hn hN hS M R' hδ
  refine ⟨C₂ * C₁, fun φ hφ B hB Z hZ => ?_⟩
  obtain ⟨γ, hγ, hd, hW⟩ := hred Z hZ
  have hl := fun Λ hΛ => hlev M Λ hΛ γ hγ hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩
  have h := hC₂ _ (hadm M φ hφ γ hγ hd) (C₁ * B) (fun Λ hΛ => (hl Λ hΛ).2.2 B (hB Λ hΛ)) _ hW
  rw [(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n (N + 1) hn hN M φ hM (fun Λ hΛ => (hl Λ hΛ).1) Z hZ).1 γ hγ] at h
  obtain ⟨-, hH, hdet, -⟩ := (unitary_act_halfSpace E Ψ (N + 1) γ hγ).2 Z hZ
  have hf : ‖hFac Ψ γ Z (0 : CM Ψ n (N + 1)) 0‖ =
      (∏ τ, ‖(hDen Ψ γ Z τ).det‖ ^ 2) ^ ((n : ℝ) / 2) := by
    have h0 : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n (N + 1)) τ k = 0 := fun _ _ => rfl
    rw [← Real.finset_prod_rpow _ _ fun _ _ => by positivity]
    simp only [hFac, h0, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      mul_one, norm_prod, norm_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast; ring
  rw [← hdet, Real.mul_rpow (InvBound.detIm_nonneg hH) (Finset.prod_nonneg fun _ _ => by positivity),
    ← hf, mul_assoc C₂]
  rw [norm_mul] at h
  refine le_of_eq_of_le ?_ h
  ring

end GlobalTheory.SW
