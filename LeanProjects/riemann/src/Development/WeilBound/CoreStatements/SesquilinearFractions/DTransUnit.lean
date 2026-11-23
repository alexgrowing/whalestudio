import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDualStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLeStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt
import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem transition_matrix_unique {I : Type} [Fintype I] [DecidableEq I] (e : I → D.La) (he : LinearIndependent (𝓞 E) e)
    (C : Matrix I I E) (hC : ∀ m y, ∑ n, C m n * sesq D (e n) y = 0) : C = 0 := by
  classical
  ext m k
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image (C m))
  choose u hu using fun n => hc (C m n) (Finset.mem_image_of_mem (C m) (Finset.mem_univ n))
  have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero c
  have huv : ∀ n, (u n : E) = (c : 𝓞 E) * C m n := fun n => by
    rw [show ((u n : 𝓞 E) : E) = algebraMap (𝓞 E) E (u n) from rfl, hu n, Algebra.smul_def]
  set z : D.La := ∑ n, u n • e n with hz
  have hz0 : ∀ y, sesq D y z = 0 := by
    intro y
    have h1 : sesq D z y = 0 := by
      rw [hz, sesq_sum_smul_left]
      simp_rw [huv]
      calc ∑ n, (c : 𝓞 E) * C m n * sesq D (e n) y = (c : 𝓞 E) * ∑ n, C m n * sesq D (e n) y := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
        _ = 0 := by rw [hC m y, mul_zero]
    rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 z y, h1, map_zero, neg_zero]
  have hzz : z = 0 := (GlobalTheory.T.sesq_unimodular_dual E H D).1 z hz0
  have hu0 := (Fintype.linearIndependent_iff.1 he) u (by rw [← hz]; exact hzz)
  have : (c : 𝓞 E) * C m k = 0 := by rw [← huv, hu0 k]; simp
  simpa [hc0] using this

theorem isTransition_of_coefficients {I : Type} [Fintype I] (x e : I → D.La) (m : ℕ) (hm : 0 < m) (S : Matrix I I (𝓞 E))
    (hS : ∀ a, m • x a = ∑ b, S a b • e b) :
    IsTransition D x e (Matrix.of fun a b => (S a b : E) / m) := by
  intro a y
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have h := congrArg (fun z => sesq D z y) (hS a)
  rw [sesq_sum_smul_left, ← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1] at h
  apply mul_left_cancel₀ hm0
  have h' : (m : E) * sesq D (x a) y = ∑ b, (S a b : E) * sesq D (e b) y := by simpa using h
  rw [h', Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.of_apply]
  field_simp

end

theorem padic_norm_transition_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La) (T : Matrix I I E) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → IsLocBasis (𝓞 E) ℓ e → IsTransition D x e T → ∀ j : E →+* ℂ_[ℓ], ‖j T.det‖ = 1 := by
  intro E _ _ _ H D I _ _ x e T ℓ hx he hT j
  classical
  have : Fact (Nat.Prime ℓ) := ⟨ℓ.2⟩
  obtain ⟨hxi, n0, hn0, hspx⟩ := hx
  obtain ⟨hei, m0, hm0, hspe⟩ := he
  have hm0p : 0 < m0 := Nat.pos_of_ne_zero fun h => hm0 (h ▸ dvd_zero _)
  have hn0p : 0 < n0 := Nat.pos_of_ne_zero fun h => hn0 (h ▸ dvd_zero _)
  choose S hS using fun a => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspe (x a))
  choose R hR using fun b => (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hspx (e b))
  have hT1 := isTransition_of_coefficients D x e m0 hm0p (Matrix.of S) fun a => (hS a).symm
  have hT2 := isTransition_of_coefficients D e x n0 hn0p (Matrix.of R) fun b => (hR b).symm
  set T1 : Matrix I I E := Matrix.of fun a b => ((Matrix.of S) a b : E) / m0
  set T2 : Matrix I I E := Matrix.of fun a b => ((Matrix.of R) a b : E) / n0

  have hTT1 : T = T1 := by
    have := transition_matrix_unique D e hei (T - T1) fun m y => by
      calc ∑ n, (T - T1) m n * sesq D (e n) y = ∑ n, T m n * sesq D (e n) y - ∑ n, T1 m n * sesq D (e n) y := by
            rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [← hT m y, ← hT1 m y, sub_self]
    exact sub_eq_zero.1 this

  have hTT2 : T2 * T = 1 := by
    have := transition_matrix_unique D e hei (T2 * T - 1) fun b y => by
      have hsum : ∑ n, (T2 * T) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [hT2 b y]
        calc ∑ n, (T2 * T) b n * sesq D (e n) y = ∑ n, ∑ c, T2 b c * T c n * sesq D (e n) y := by
              refine Finset.sum_congr rfl fun n _ => ?_; rw [Matrix.mul_apply, Finset.sum_mul]
          _ = ∑ c, T2 b c * ∑ n, T c n * sesq D (e n) y := by
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
          _ = ∑ c, T2 b c * sesq D (x c) y := Finset.sum_congr rfl fun c _ => by rw [hT c y]
      have hone : ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y = sesq D (e b) y := by
        rw [Finset.sum_eq_single b]
        · rw [Matrix.one_apply_eq, _root_.one_mul]
        · intro n _ hn; rw [Matrix.one_apply_ne (Ne.symm hn), MulZeroClass.zero_mul]
        · simp
      calc ∑ n, (T2 * T - 1) b n * sesq D (e n) y
            = ∑ n, (T2 * T) b n * sesq D (e n) y - ∑ n, (1 : Matrix I I E) b n * sesq D (e n) y := by
              rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun n _ => by rw [Matrix.sub_apply, sub_mul]
        _ = 0 := by rw [hsum, hone, sub_self]
    exact sub_eq_zero.1 this

  have hnat : ∀ k : ℕ, ¬ (ℓ : ℕ) ∣ k → ‖((k : ℕ) : ℂ_[ℓ])‖ = 1 := by
    intro k hk
    have hcop : Nat.Coprime k ℓ := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd ℓ.2).2 hk))
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * k + b * ℓ = 1 := by
      refine ⟨Nat.gcdA k ℓ, Nat.gcdB k ℓ, ?_⟩
      have := Nat.gcd_eq_gcd_ab k ℓ
      rw [hcop] at this
      push_cast at this
      linarith
    have h1 : ((a : ℂ_[ℓ]) * k + (b : ℂ_[ℓ]) * ℓ) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : ℂ_[ℓ])) hab
    have hle : ‖((k : ℕ) : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have ha : ‖(a : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hb : ‖(b : ℂ_[ℓ])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
    have hl := GlobalTheory.FlatCM.PlaceShiftModel.norm_ell (ℓ := (ℓ : ℕ))
    have hmax := IsUltrametricDist.norm_add_le_max ((a : ℂ_[ℓ]) * k) ((b : ℂ_[ℓ]) * ℓ)
    rw [h1, norm_one, norm_mul, norm_mul] at hmax
    have hbl : ‖(b : ℂ_[ℓ])‖ * ‖((ℓ : ℕ) : ℂ_[ℓ])‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hb) hl
    rcases le_max_iff.1 hmax with h | h
    · have : 1 ≤ ‖((k : ℕ) : ℂ_[ℓ])‖ := le_trans h (mul_le_of_le_one_left (norm_nonneg _) ha)
      exact le_antisymm hle this
    · exact absurd h (not_le.2 hbl)
  have hentry : ∀ (A : Matrix I I (𝓞 E)) (k : ℕ), ¬ (ℓ : ℕ) ∣ k → ∀ a b,
      ‖j (((Matrix.of fun a b => ((A a b : 𝓞 E) : E) / k) : Matrix I I E) a b)‖ ≤ 1 := by
    intro A k hk a b
    simp only [Matrix.of_apply, map_div₀, map_natCast, norm_div, hnat k hk, div_one]
    exact GlobalTheory.FlatCM.PlaceShiftModel.norm_le_one j (A a b)
  have hdet : ∀ M : Matrix I I E, (∀ a b, ‖j (M a b)‖ ≤ 1) → ‖j M.det‖ ≤ 1 := by
    intro M hM
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] I (M.map j) 1 zero_le_one (fun a b => hM a b)
    simpa using this
  have h1 : ‖j T.det‖ ≤ 1 := by rw [hTT1]; exact hdet _ (hentry (Matrix.of S) m0 hm0)
  have h2 : ‖j T2.det‖ ≤ 1 := hdet _ (hentry (Matrix.of R) n0 hn0)
  have hprod : ‖j T2.det‖ * ‖j T.det‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Matrix.det_mul, hTT2, Matrix.det_one, map_one, norm_one]
  nlinarith [norm_nonneg (j T.det), norm_nonneg (j T2.det)]

end PositivityTheory.Xgf
