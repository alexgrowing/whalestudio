import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem ker_localizedTheta_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    Per.kerP l = Ideal.span {beta ϖ} := by
  intro l _ ϖ hϖ
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  obtain ⟨-, hker, hA, -⟩ := thetaP_facts l
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hmem : ∀ a : Per.Ainf l, Per.θ l a = 0 →
      algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    intro a ha
    rw [← hker, RingHom.mem_ker, hA, ha]
    rfl
  have h0 : Per.θ l (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) = 0 := by
    have : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ∈ RingHom.ker (Per.θ l) := by
      rw [hk]; exact Ideal.mem_span_singleton_self _
    exact this
  have hlb : ((l : ℕ) : Per.AinfP l) * beta ϖ =
      -algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) := by
    rw [l_mul_beta, map_sub, map_natCast]; ring
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hker, RingHom.mem_ker] at hy
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    rw [map_natCast] at h
    have ha : Per.θ l a = 0 := by
      apply Subtype.ext
      rw [← hA, ← h, map_mul, hy, zero_mul]
      rfl
    have h2 : a ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h2
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h, map_mul]
    have : algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) =
        -(((l : ℕ) : Per.AinfP l) * beta ϖ) := by rw [hlb, neg_neg]
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : Per.AinfP l) * beta ϖ ∈ Per.kerP l := by
      rw [hlb]; exact neg_mem (hmem _ h0)
    have h4 : linv l * (((l : ℕ) : Per.AinfP l) * beta ϖ) = beta ϖ := by
      rw [← mul_assoc, mul_comm (linv l), mul_linv, one_mul]
    rw [← h4]
    exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.Pst.StLat
