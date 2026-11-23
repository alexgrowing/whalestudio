import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.RationalPoints

theorem Hf_nsmul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (m n : ℕ) (y y' : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D T (m • y) (n • y') = ((m * n : ℝ) : ℂ) * TaylorLogMetric.Hf D T y y' := by
  rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.Hf_eq, ← Nat.cast_smul_eq_nsmul ℂ m,
    ← Nat.cast_smul_eq_nsmul ℂ n, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.sq_smul_right]
  simp only [map_natCast]
  push_cast
  ring

theorem rational_points : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ), StandardLatticesGL3.Crv D cc dl → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → (∀ x : Matrix (Fin b) (Fin a) D.host.E, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' (dl • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc dl) x)) ∧ ∀ y y', StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y' → (∃ q : ℚ, (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y').im = q) ∧ ∃ q : ℚ, (Real.sqrt D.host.d / 2 : ℝ) * TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc dl) y y = ((q : ℝ) : ℂ) := by
  intro D cc dl hc a b L L' hL hL'
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hK : StandardLatticesGL3.KLat D (TaylorLogMetric.tor0 D cc dl) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc dl) L L') :=
    Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, h1, -, -, -, h5⟩ := GlobalTheory.ThetaLine.theta_line D hG cc dl hc a b _ hK
  refine ⟨fun x => GlobalTheory.ThetaInter.klat_mul_mem hG.1 hc.1.1 hK x, ?_⟩
  rintro y y' ⟨m, hm, hy⟩ ⟨n, hn, hy'⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  constructor
  · obtain ⟨k, hk⟩ := h1 _ hy _ hy'
    rw [Hf_nsmul, Complex.im_ofReal_mul] at hk
    refine ⟨k / (m * n), ?_⟩
    push_cast
    rw [← hk]
    field_simp
  · obtain ⟨k, hk⟩ := h5 _ hy
    rw [TaylorLogMetric.qH, Hf_nsmul, Complex.re_ofReal_mul] at hk
    refine ⟨k / (m * m), Complex.ext ?_ ?_⟩
    · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      push_cast
      rw [← hk]
      field_simp
    · rw [Complex.im_ofReal_mul, Complex.ofReal_im, GlobalTheory.ThetaLine.im_Hf, GlobalTheory.ThetaLine.sq_self_im]
      simp

end GlobalTheory.RationalPoints
