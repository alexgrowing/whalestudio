import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SatChar

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem charPol_satWD (h : IsPlaceOver A w) (n : ℕ) (B : Multiset ℂˣ) (g : Weil h) :
    (satWD h n B).charPol g = (B.map fun b : ℂˣ =>
      X - C ((((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - n) / 2 : ℝ)) : ℂ)) ^ deg g * ((b : ℂ)⁻¹) ^ deg g)).prod := by
  classical
  have hs : ∀ {ι : Type} (c : ℂ) (d : ι → ℂ), c • diagEnd d = diagEnd (fun i => c * d i) := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [satWD, WD.lpUnr, WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hs, charpoly_diagEnd,
    ← Finset.prod_map_val]
  rw [Multiset.map_univ (B.map fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))
    (fun z : ℂ => X - C ((((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) ^ deg g * ((WD.unitOf z : ℂˣ) : ℂ) ^ deg g)),
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [WD.coe_unitOf (by simp), Units.val_inv_eq_inv_val]

def ordHom (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ord (w.adicCompletion E) x)) fun x y => by
    rw [ord_mul, ofAdd_add]

theorem unram_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : ∀ x : (w.adicCompletion E)ˣ, Valued.v (x : w.adicCompletion E) = 1 → χ x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (g : Weil h) :
    χ (a g) = χ ϖ ^ (-deg g) := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  have h2 : ord (w.adicCompletion E) (a g * ϖ ^ deg g) = 0 := by
    have := congrArg Multiplicative.toAdd (map_mul (ordHom w) (a g) (ϖ ^ deg g))
    rw [map_zpow] at this
    simp only [ordHom, MonoidHom.mk'_apply, toAdd_ofAdd, toAdd_mul, toAdd_zpow, smul_eq_mul] at this
    rw [this, ha.ord_eq, h1]; ring
  have h3 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [SphCompletion.ord_completion, neg_eq_zero] at h2
    have h0 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    rw [← WithZero.exp_log h0, h2, WithZero.exp_zero]
  have h4 : a g = (a g * ϖ ^ deg g) * ϖ ^ (-deg g) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h4, map_mul, hχ _ h3, one_mul, map_zpow]

theorem absPow_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (s : ℝ)
    (g : Weil h) :
    (absPow (w.adicCompletion E) (s : ℂ) (a g) : ℂ) = (((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    exact_mod_cast (zero_lt_one.trans this)
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq.le, ← Complex.ofReal_zpow,
    ← Complex.ofReal_cpow (zpow_pos hq _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, mul_comm]

theorem satWD_charPol_chars : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ) (ξ ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, ξ' j = ξ j * absPow (w.adicCompletion E) ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := by
  intro Ω _ E _ _ _ _ w A h n ξ ξ' hξ' hun ϖ hϖ a ha g
  rw [charPol_satWD, Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rw [hξ' j, MonoidHom.mul_apply, Units.val_mul, unram_art ha (ξ j) (hun j) ϖ hϖ g, absPow_art ha]
  congr 2
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, inv_zpow, mul_comm]

end GlobalTheory.SatChar
