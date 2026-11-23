import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_smul_eq_zero_of_isFiniteLength {R : Type} [CommRing R] (r : R)
    (hr : ∀ b : R, IsUnit (1 - b * r)) (M : Type) [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ n : ℕ, ∀ m : M, r ^ n • m = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun m => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    have hS : ∀ q : M ⧸ N, r • q = 0 := by
      intro q
      by_contra hq
      have htop : (R ∙ (r • q)) = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by rwa [Submodule.span_singleton_eq_bot])
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : q ∈ R ∙ (r • q))
      have h1 : (1 - b * r) • q = 0 := by rw [sub_smul, one_smul, mul_smul, hb, sub_self]
      have h2 : q = 0 := (hr b).smul_eq_zero.1 h1
      exact hq (by rw [h2, smul_zero])
    refine ⟨n + 1, fun m => ?_⟩
    have hm : r • m ∈ N := by
      have := hS (N.mkQ m)
      rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have := hn ⟨_, hm⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem isUnit_one_sub_mul_l (b : A O K) : IsUnit (1 - b * (l : A O K)) := by
  set f : A O K := 1 - b * (l : A O K)
  set g := (equivA O K).symm f
  have hg : equivA O K g = f := AlgEquiv.apply_symm_apply _ _
  suffices IsUnit g by simpa [hg] using this.map (equivA O K)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h0 : algebraMap O K (constantCoeff g) = 1 - constantCoeff (b : K⟦X⟧) * l := by
    calc algebraMap O K (constantCoeff g) = constantCoeff ((equivA O K g : A O K) : K⟦X⟧) := by
          rw [coe_equivA, ← coeff_zero_eq_constantCoeff_apply (map _ g), coeff_map,
            coeff_zero_eq_constantCoeff_apply]
      _ = 1 - constantCoeff (b : K⟦X⟧) * l := by
          rw [hg]
          simp only [f, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul,
            map_sub, map_one, map_mul]
          congr 2
  have hlt : ‖constantCoeff (b : K⟦X⟧) * (l : K)‖ < 1 := by
    rw [norm_mul]
    have hb : ‖constantCoeff (b : K⟦X⟧)‖ ≤ 1 := by
      simpa using (mem_A.1 b.2) 0
    calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_l_lt_one (K := K) l
  have hn : ‖algebraMap O K (constantCoeff g)‖ = 1 := by
    rw [h0, sub_eq_add_neg, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlt.ne), norm_neg, norm_one, max_eq_right hlt.le]
  have hne : algebraMap O K (constantCoeff g) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (algebraMap O K (constantCoeff g))⁻¹).2
    (by rw [norm_inv, hn, inv_one])
  refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (K := K) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ hne, map_one]

theorem exists_l_pow_smul_eq_app_of_isFiniteLength_coker (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ]
    [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ)
    (G : GlobalTheory.BK.Hom Q T) :
    IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]

end GlobalTheory.BK
