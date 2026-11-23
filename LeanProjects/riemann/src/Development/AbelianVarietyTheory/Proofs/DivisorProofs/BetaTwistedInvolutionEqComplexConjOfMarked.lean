import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem iM_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (τ : FM P →+* ℂ) (a : FM P), τ (iM P a) = (starRingEnd ℂ) (τ a) := by
  intro p _ G P μ ha hM τ a
  set φ : G.F →+* ℂ := τ.comp (algebraMap G.F (FM P)) with hφ
  have hroot : P.pol.eval₂ φ (τ (AdjoinRoot.root P.pol)) = 0 := by
    rw [hφ, ← Polynomial.hom_eval₂]
    have : P.pol.eval₂ (algebraMap G.F (FM P)) (AdjoinRoot.root P.pol) = 0 := AdjoinRoot.eval₂_root P.pol
    rw [this, map_zero]
  have hn := GlobalTheory.LKMid.MarkEll.mark_ell p G P μ ha hM φ _ hroot
  set z := τ (AdjoinRoot.root P.pol) with hz
  have hc0 : ((P.c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast (P.c.ne_zero)
  have hzc : (starRingEnd ℂ) z * z = ((P.c : ℚ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; exact_mod_cast hn
  have hz0 : z ≠ 0 := by
    rintro h; rw [h, mul_zero] at hzc; exact hc0 hzc.symm
  have hiz : τ (iM P (AdjoinRoot.root P.pol)) * z = ((P.c : ℚ) : ℂ) := by
    rw [hz, ← map_mul, iM_root_mul]
    exact eq_ratCast (τ.comp (algebraMap ℚ (FM P))) _
  have h1 : τ (iM P (AdjoinRoot.root P.pol)) = (starRingEnd ℂ) z :=
    mul_right_cancel₀ hz0 (hiz.trans hzc.symm)
  have hext : τ.comp (iM P).toRingHom = (starRingEnd ℂ).comp τ := by
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp only [RingHom.comp_apply]
      change τ (iM P (algebraMap G.F (FM P) x)) = (starRingEnd ℂ) (τ (algebraMap G.F (FM P) x))
      rw [iM_algF]
      exact IsCMField.complexEmbedding_complexConj G.F φ x
    · simpa using h1
  exact congrArg (fun f => f a) hext

end GlobalTheory.StabFin
