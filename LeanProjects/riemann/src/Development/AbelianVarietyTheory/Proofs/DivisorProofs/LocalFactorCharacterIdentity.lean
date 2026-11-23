import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittCharacterConjugateInverse
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeLawAChar

theorem fac_div_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ t : (AE F E)ˣ, GlobalTheory.ThK.LemF.fac X.β (((b + 2 : ℕ) : ℝ) / 2) t *
      ((X.ν (Units.map (cA σ : AE F E →* AE F E) t) : ℂ) *
        ((absE F E (Units.map (cA σ : AE F E →* AE F E) t) : ℝ) : ℂ) ^ ((b + 2 - a') / 2))⁻¹ =
      GlobalTheory.ThK.LemF.fac X.α ((a' : ℝ) / 2) t := by
  intro F E _ _ _ _ _ σ B b a' G X om om' T t
  obtain ⟨k, hk⟩ := T.geo.even
  have hlt := T.geo.lt
  have hα : X.α (Units.map (cA σ : AE F E →* AE F E) t) = (X.α t)⁻¹ :=
    GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' T) t
  have hβ : X.β (Units.map (cA σ : AE F E →* AE F E) t) = (X.β t)⁻¹ :=
    GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV T) t
  have habs : absE F E (Units.map (cA σ : AE F E →* AE F E) t) = absE F E t := by
    have : Units.map (cA σ : AE F E →* AE F E) t = GlobalTheory.Doubling.conjUnit σ t := by
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe]
      rfl
    rw [this, GlobalTheory.Doubling.absE_conjUnit]
  have hν : X.ν (Units.map (cA σ : AE F E →* AE F E) t) = X.β t / X.α t := by
    rw [Chars.ν, MonoidHom.div_apply, hα, hβ, inv_div_inv]
  have hpos : (0 : ℝ) < absE F E t := by
    have h := map_mul (absE F E) t t⁻¹
    rw [mul_inv_cancel, map_one] at h
    have : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
    exact_mod_cast pos_iff_ne_zero.mpr this
  have hexp : ((b + 2 : ℕ) : ℝ) / 2 = (a' : ℝ) / 2 + (((b + 2 - a') / 2 : ℕ) : ℝ) := by
    have h2 : 2 * ((b + 2 - a') / 2) + a' = b + 2 := by omega
    have h3 : (2 * (((b + 2 - a') / 2 : ℕ) : ℝ) + a' : ℝ) = ((b + 2 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  unfold GlobalTheory.ThK.LemF.fac
  rw [hν, habs, hexp, Real.rpow_add hpos, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, Circle.coe_div]
  have h0 : ((absE F E t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hA : (X.α t : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hB : (X.β t : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

end GlobalTheory.ConeLawAChar

end
