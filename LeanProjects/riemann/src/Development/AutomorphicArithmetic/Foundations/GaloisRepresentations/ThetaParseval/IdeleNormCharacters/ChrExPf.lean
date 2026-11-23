import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

noncomputable section

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def psi (μ : HChar E) (k : ℕ) (s : ℤ) : HChar E := μ ^ k * Model.absC E ((s : ℂ) / 2)

private theorem hpow_apply (μ : HChar E) (k : ℕ) (x) : (μ ^ k).1 x = μ.1 x ^ k := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem hpow_loc (μ : HChar E) (k : ℕ) (w) (x) : (μ ^ k).loc w x = μ.loc w x ^ k :=
  hpow_apply μ k _

private theorem hpow_inf (μ : HChar E) (k : ℕ) (x) : (μ ^ k).inf x = μ.inf x ^ k :=
  hpow_apply μ k _

private theorem hpow_val (μ : HChar E) (k : ℕ) (w) : (μ ^ k).val w = μ.val w ^ k :=
  hpow_apply μ k _

private theorem lc_pow (χ : Chr (maximalRealSubfield E) E) (k : ℕ) (w : HeightOneSpectrum (𝓞 E)) (x) :
    locChar (χ ^ k) w x = locChar χ w x ^ k := by
  show Circle.toUnits ((χ ^ k) (locIdele _ w x)) = Circle.toUnits (χ (locIdele _ w x)) ^ k
  rw [MonoidHom.pow_apply, map_pow]

private theorem typ_term (z : ℂ) (hz : z ≠ 0) (a b : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (a - b) * ((‖z‖ : ℝ) : ℂ) ^ (a + b) = z ^ a * (starRingEnd ℂ z) ^ b := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h2 : (((‖z‖ : ℝ) : ℂ) ^ 2) ^ b = (((‖z‖ : ℝ) : ℂ) ^ b) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, zpow_comm]
  have hA : z ^ a ≠ 0 := zpow_ne_zero _ hz
  have hB : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have hC : ((‖z‖ : ℝ) : ℂ) ^ a ≠ 0 := zpow_ne_zero _ hn
  have hD : ((‖z‖ : ℝ) : ℂ) ^ b ≠ 0 := zpow_ne_zero _ hn
  rw [hc, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hn, zpow_add₀ hn, h2]
  field_simp

private theorem inf_psi (hAb : AbsFacts) (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (μ : HChar E) (m : InfinitePlace (maximalRealSubfield E) → ℤ) (hμ : InfExp emb μ m) (k : ℕ) (s : ℤ) (x : Eˣ) :
    (((psi μ k s).inf x : ℂˣ) : ℂ) = ∏ w, ((emb w).1 (x : E) / ‖(emb w).1 (x : E)‖) ^ ((k : ℤ) * m w) *
      ((‖(emb w).1 (x : E)‖ : ℝ) : ℂ) ^ s := by
  rw [psi, HChar.inf_mul, Units.val_mul, hpow_inf, Units.val_pow_eq_pow_val, hμ x, (hAb E emb _).2 x,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h2 : (2 : ℂ) * ((s : ℂ) / 2) = s := by ring
  rw [h2, Complex.cpow_intCast, mul_comm (k : ℤ), zpow_mul, zpow_natCast]

private theorem exps {k : ℕ} {s m : ℤ} (hev : Even ((k : ℤ) + s)) (hm : Odd m) :
    ∃ a b : ℤ, (s + k * m) / 2 = a ∧ (s - k * m) / 2 = b ∧ a + b = s ∧ a - b = k * m := by
  obtain ⟨r, hr⟩ := hev
  obtain ⟨t, rfl⟩ := hm
  refine ⟨r + k * t, r - k * t - k, ?_, ?_, ?_, ?_⟩
  · rw [show s + k * (2 * t + 1) = 2 * (r + k * t) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · rw [show s - k * (2 * t + 1) = 2 * (r - k * t - k) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · linear_combination -hr
  · ring

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.chrEx :
    UpperTheory.Gal.TP.Chr.MuEmb → UpperTheory.Gal.TP.Chr.ReadEx → UpperTheory.Gal.TP.Chr.ReadLoc → UpperTheory.Gal.TP.Chr.ReadRes → UpperTheory.Gal.TP.Chr.ReadExp → UpperTheory.Gal.TP.Chr.AbsFacts → UpperTheory.Gal.TP.Chr.TypProd → UpperTheory.Gal.TP.Chr.ExpInj → UpperTheory.Gal.TP.Chr.ChrEx := by
  intro hMu hRE hRL hRR hRX hAb hTP hEI E _ _ _ hun emb w₀ m hm
  obtain ⟨μ, hμu, hμq, hμi, hμ0⟩ := hMu E hun emb w₀ m hm
  obtain ⟨χ, hr, hH⟩ := hRE E μ hμu
  have hl := hRL E μ χ hr
  have hres := hRR E μ χ hr hμq
  have hexp := hRX E emb μ χ m hr hμi
  have hval : ∀ w, val χ w = μ.val w := fun w => by
    show locChar χ w (atFin w (unif w)) = μ.loc w (atFin w (unif w))
    rw [hl]
  refine ⟨χ, psi μ, fun x hx => ?_, fun k => ⟨⟨hH.1.pow k, fun x => ?_⟩, fun z hz => ?_, fun j hj a => ?_⟩,
    fun k s w => ⟨⟨fun h x hx => ?_, fun h x hx => ?_⟩, ?_⟩, fun k s hev x _ => ?_, fun k k' s s' h => ?_⟩
  · rw [hl]
    exact hμ0 x hx
  · rw [MonoidHom.pow_apply, hH.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hexp z hz, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    beta_reduce
    rw [mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hres a]
    split_ifs with h
    · simp
    · rw [pow_one, neg_one_pow_eq_pow_mod_two, ← hj, ← neg_one_pow_eq_pow_mod_two]
  · have h1 : (psi μ k s).loc w x = 1 := h x hx
    rw [psi, HChar.loc_mul, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one] at h1
    rw [lc_pow, hl]
    exact h1
  · have h1 : locChar (χ ^ k) w x = 1 := h x hx
    rw [lc_pow, hl] at h1
    rw [psi, HChar.loc_mul, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one]
    exact h1
  · rw [psi, HChar.val_mul, Units.val_mul, hpow_val, Units.val_pow_eq_pow_val, ((hAb E emb _).1 w).2, hval, neg_div]
  · rw [hTP E emb _ _ (x : E), inf_psi hAb emb μ m hμi]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨a, b, ha, hb, h1, h2⟩ := exps hev (hm w)
    have hz : (emb w).1 (x : E) ≠ 0 := (map_ne_zero (emb w).1).2 x.ne_zero
    beta_reduce
    rw [ha, hb, ← typ_term _ hz a b, h1, h2]
  · have h1 := hEI E emb (fun w => k * m w) (fun w => k' * m w) s s' fun x => by
      rw [← inf_psi hAb emb μ m hμi k s x, ← inf_psi hAb emb μ m hμi k' s' x, h]
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    have h3 : (k : ℤ) * m w = k' * m w := congrFun h1 w
    have hm0 : m w ≠ 0 := fun h0 => by simpa [h0] using hm w
    exact_mod_cast mul_right_cancel₀ hm0 h3

end
