import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLFunctionSpecialValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleDoublingPeriodSecondStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.BotSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pair_small {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) := by
  refine ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα,
    ⟨h.chars.heckeα.1.div' h.chars.heckeβ.1, fun x => by
      simp only [MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_self']⟩,
    h.chars.resα, fun x => ?_, h.weil'⟩
  rw [MonoidHom.div_apply, Circle.coe_div, h.chars.resα x, h.chars.resβ x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ a with hm | hm <;> rw [hm] <;> ring

theorem hasExp_div {τ : ∀ w : InfinitePlace F, EmbOver E w} {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') fun w => m w - m' w := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map (piInf (τ w))).ne_zero
  have h1 : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1]

theorem unrOff_div {χ χ' : Chr F E} {S : Set (Pl F)} (h : UnrOff χ S) (h' : UnrOff χ' S) : UnrOff (χ / χ') S := by
  intro w hw x hx
  have e := h w hw x hx
  have e' := h' w hw x hx
  simp only [locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div] at e e' ⊢
  rw [e, e', div_one]

theorem exists_I_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = 0 → ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT hp hq
  have hlt := hT.geo.lt
  have ha := hT.geo.aBig
  refine GlobalTheory.T.doubling_l_function_special_value hK F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ (pair_small hT)
    (by omega) (by omega) (by omega) (by omega) hT.geo.even (fun w => B.mα w - B.mβ w)
    (hasExp_div hT.chars.expα hT.chars.expβ) (fun w => (hT.geo.kappa w).trans_le (le_abs_self _)) X.T hT.chars.sub
    (unrOff_div hT.chars.unrα hT.chars.unrβ) hT.chars.ram ?_
  exact GlobalTheory.T.triple_doubling_period_second hK F E σ B a a' G X om om' hT hp hq

end GlobalTheory.ThK.BotSmall

end
