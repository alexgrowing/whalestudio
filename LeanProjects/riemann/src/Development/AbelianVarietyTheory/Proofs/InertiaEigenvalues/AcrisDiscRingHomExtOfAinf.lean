import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.AcrisDiscExt

theorem isUnit_natCast_of {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R)
    (hu : IsUnit (l : R)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : R) := by
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have h : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm
  have h' := h.map f
  rw [map_natCast] at h'
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hu.pow v).mul h'

theorem norm_l_disc_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖((l : ℕ) : Disc l u ρ)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have e : ((l : ℕ) : Disc l u ρ) = ofPre l u ρ (algebraMap A (PreDisc l u ρ) ((l : A) ^ 1 * u ^ 0) *
      IsLocalization.Away.invSelf (l : A) ^ 0) := by
    simp
  rw [e, norm_ofPre]
  refine gauge_le l u ρ (inv_pos.2 hl0) (Submodule.subset_span ⟨1, 0, 0, ?_, rfl⟩)
  rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']

theorem norm_pow_mul_le (l : ℕ) [Fact l.Prime] {K : FinExt l} (bk : BK K) (w : bk.DA bk.ρ₀) (r : ℕ) :
    ‖((l : ℕ) : bk.DA bk.ρ₀) ^ r * w‖ ≤ (l : ℝ)⁻¹ ^ r * ‖w‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_l_disc_le l _ _) ih (norm_nonneg _) (by positivity))

theorem acris_disc_ext : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  intro l hl K bk γ γ' h hγ hγ'

  have h0 : ∀ s : Per.Acris0 l,
      γ (algebraMap (Per.Acris0 l) (Per.Acris l) s) = γ' (algebraMap (Per.Acris0 l) (Per.Acris l) s) := by
    intro s
    obtain ⟨n, a, hn⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
    have e : s * ((l : ℕ) : Per.Acris0 l) ^ n = algebraMap (Per.Ainf l) (Per.Acris0 l) a :=
      Subtype.ext (by simpa using hn)
    have e' := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e
    rw [map_mul, map_pow, map_natCast, ← GlobalTheory.RingIface.tower l] at e'
    have e1 := congrArg γ e'
    have e2 := congrArg γ' e'
    rw [map_mul, map_pow, map_natCast] at e1 e2
    refine ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow n).mul_right_cancel ?_
    exact e1.trans ((h a).trans e2.symm)
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)
  ext x
  have hb : ∀ r : ℕ, ‖γ x - γ' x‖ ≤ 2 * (l : ℝ)⁻¹ ^ r := by
    intro r
    obtain ⟨s, z, rfl⟩ := (acris_basic l).2.2.1 x r
    have hs := h0 s
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hs, add_sub_add_left_eq_sub,
      ← mul_sub]
    have hw : ‖γ z - γ' z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hγ z, hγ' z])
    refine (norm_pow_mul_le l bk (γ z - γ' z) r).trans ?_
    exact mul_comm ((l : ℝ)⁻¹ ^ r) _ ▸ mul_le_mul_of_nonneg_left hw (by positivity)
  have ht : Filter.Tendsto (fun r : ℕ => 2 * (l : ℝ)⁻¹ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hl1).const_mul 2
  have hz : ‖γ x - γ' x‖ ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hz)

end GlobalTheory.AcrisDiscExt
