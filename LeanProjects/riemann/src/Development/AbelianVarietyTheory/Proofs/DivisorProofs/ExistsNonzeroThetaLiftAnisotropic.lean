import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLFunctionSpecialValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleDoublingPeriodFirstStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.BottomLarger

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isPair_larger {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) where
  base := hT.base
  herm := hT.geo.hV
  skew := hT.geo.hW
  good := hT.geo.hM
  hX := hT.chars.heckeβ
  hW := by
    refine ⟨?_, fun x => ?_⟩
    · exact hT.chars.heckeβ.1.div' hT.chars.heckeα.1
    · rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]
  resX := hT.chars.resβ
  weil := hT.weil
  resW := fun u => by
    rw [MonoidHom.div_apply, Circle.coe_div, hT.chars.resβ u, hT.chars.resα u]
    split_ifs
    · simp
    · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, pow_add]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

theorem locChar_div (χ χ' : Chr F E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    locChar (χ / χ') w x = locChar χ w x / locChar χ' w x := by
  simp only [locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]

theorem unrAt_div {χ χ' : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (h' : UnrAt χ' w) : UnrAt (χ / χ') w :=
  fun x hx => by rw [locChar_div, h x hx, h' x hx, div_one]

theorem unrAt_div_swap {χ χ' : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt (χ / χ') w) : UnrAt (χ' / χ) w :=
  fun x hx => by
    have := h x hx
    rw [locChar_div] at this ⊢
    rw [← inv_div, this, inv_one]

end

theorem nonzero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = 0 → ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT hp hq
  have h1 := hT.geo.lt
  have h2 := hT.geo.aBig
  refine GlobalTheory.T.doubling_l_function_special_value hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (isPair_larger hT)
    (by rw [hp]; simp) (by rw [hp, hq]; simp) (by omega) (by omega) hT.geo.even (fun w => B.mβ w - B.mα w)
    (hasExp_div B.emb hT.chars.expβ hT.chars.expα) (fun w => ?_) X.T hT.chars.sub
    (fun w hw => unrAt_div (hT.chars.unrβ w hw) (hT.chars.unrα w hw))
    (fun w hw h => hT.chars.ram w hw (unrAt_div_swap h))
    (GlobalTheory.T.triple_doubling_period_first hKP F E σ B a a' G X om om' hT hp hq)
  rw [abs_sub_comm]
  exact (hT.geo.kappa w).trans_le (le_abs_self _)

end GlobalTheory.ThK.BottomLarger

end
