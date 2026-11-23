import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ChiVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsCast
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private theorem hs_real {d x : ℝ} (hd : d < 0) : Loc.hs d x * ((|x| : ℝ) : ℂ) = (x : ℂ) := by
  unfold Loc.hs
  rcases le_or_gt 0 x with h | h
  · rw [if_pos ⟨√x, 0, by rw [Real.sq_sqrt h]; ring⟩, abs_of_nonneg h, one_mul]
  · rw [if_neg (by rintro ⟨a, b, e⟩; nlinarith [sq_nonneg a, sq_nonneg b]), abs_of_neg h]
    push_cast
    ring

private theorem real_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (x : F) :
    (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ x)) * ((|Algebra.norm ℚ x| : ℚ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have hN := GlobalTheory.LipschitzTR.LhsSum.prod_realEmb_eq_norm x
  have h1 : ((|Algebra.norm ℚ x| : ℚ) : ℂ) = ∏ σ : F →+* ℝ, ((|σ x| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, Rat.cast_abs, ← hN, Finset.abs_prod]
    push_cast
    rfl
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : F →+* ℝ, ((σ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← hN]
    push_cast
    rfl
  rw [h1, h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun σ _ => hs_real (hΔ σ)

private theorem delta_ne {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ} (h : D.Ok) : Δ ≠ 0 := by
  intro hΔ
  haveI := h.real
  have h0 : ∏ τ : F →+* ℝ, τ 0 = 0 := by
    rw [GlobalTheory.LipschitzTR.LhsSum.prod_realEmb_eq_norm]
    simp
  obtain ⟨σ, -, -⟩ := Finset.prod_eq_zero_iff.mp h0
  have hσ := h.neg σ
  rw [hΔ, map_zero] at hσ
  exact lt_irrefl _ hσ

private theorem int_case {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ} (h : D.Ok) (z : Fˣ) (a : 𝓞 F)
    (ha : (a : F) = z) :
    (Function.mulSupport fun v : Pl F => (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ)).Finite ∧
    (∏ᶠ v, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ)) = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ := by
  haveI := h.real
  have hz : (z : F) ≠ 0 := z.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz
    rw [← ha]
    rfl
  obtain ⟨hfin, hrec⟩ := recip F Δ (z : F) (delta_ne h) hz
  have hval : ∀ v : Pl F, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ) =
      Loc.hs (cv v Δ) (cv v (z : F)) / (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ) := by
    intro v
    rw [chiVal F Δ D h v _ (algebraMap (𝓞 F) (Ov v) a) (by rw [Units.coe_map, ← ha]; rfl)]
    rfl
  obtain ⟨cfin, cprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map (K := F) (I := Ideal.span {a})
    (by simpa using ha0)
  simp only [Ideal.map_span, Set.image_singleton] at cfin cprod
  have cfinC : (Function.mulSupport fun v : Pl F =>
      (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ)).Finite := by
    have e := Function.mulSupport_comp_eq (Nat.cast : ℕ → ℂ) (fun {n} => Nat.cast_eq_one)
      (fun v : Pl F => Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}))
    rw [Function.comp_def] at e
    rw [e]
    exact cfin
  rw [funext hval]
  refine ⟨(hfin.union cfinC).subset (Function.mulSupport_div _ _), ?_⟩
  rw [finprod_div_distrib hfin cfinC, hrec]
  have hcard : (∏ᶠ v : Pl F, (Nat.card (Ov v ⧸ Ideal.span {algebraMap (𝓞 F) (Ov v) a}) : ℂ)) =
      ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) := by
    have e := (Nat.castRingHom ℂ : ℕ →* ℂ).map_finprod cfin
    simp only [MonoidHom.coe_coe, Nat.coe_castRingHom] at e
    rw [← e, cprod, Ideal.absNorm_span_singleton, ← ha, ← Algebra.coe_norm_int]
    rw [Nat.cast_natAbs, ← Int.cast_abs, Rat.cast_intCast]
  rw [hcard]
  have hp := real_prod h.neg (z : F)
  have hn : ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hz)
  have hA : ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hz)
  have hAA : ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) =
      ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) * ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) := by
    exact_mod_cast abs_mul_abs_self (Algebra.norm ℚ (z : F))
  calc (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ (z : F))) / ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ)
      = (∏ σ : F →+* ℝ, Loc.hs (σ Δ) (σ (z : F))) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) /
          (((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ) * ((|Algebra.norm ℚ (z : F)| : ℚ) : ℂ)) := by
        rw [mul_div_mul_right _ _ hA]
    _ = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ) /
          (((Algebra.norm ℚ (z : F) : ℚ) : ℂ) * ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)) := by
        rw [hp, hAA]
    _ = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ := by
        rw [div_mul_cancel_left₀ hn]

theorem UpperTheory.V.Z.Sym.Glob.chiProd :
    UpperTheory.V.Z.Sym.Glob.ChiProd := by
  intro F _ _ Δ D h z
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 F) (z : F)
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h0
    apply z.ne_zero
    rw [← hab, h0, zero_div]
  have hz : z = Units.mk0 _ ha0 * (Units.mk0 _ hb0)⁻¹ := by
    ext
    simp [← hab, div_eq_mul_inv]
  obtain ⟨fa, pa⟩ := int_case h (Units.mk0 _ ha0) a rfl
  obtain ⟨fb, pb⟩ := int_case h (Units.mk0 _ hb0) b rfl
  have hf : ∀ v : Pl F, (D.χ v (Units.map (cv v : F →* Kv v) z) : ℂ) =
      (D.χ v (Units.map (cv v : F →* Kv v) (Units.mk0 _ ha0)) : ℂ) /
        (D.χ v (Units.map (cv v : F →* Kv v) (Units.mk0 _ hb0)) : ℂ) := by
    intro v
    rw [hz, map_mul, map_inv, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have hinv : Algebra.norm ℚ ((algebraMap (𝓞 F) F b)⁻¹) = (Algebra.norm ℚ (algebraMap (𝓞 F) F b))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel₀ hb0, map_one]
  rw [finprod_congr hf, finprod_div_distrib fa fb, pa, pb, hz]
  simp [map_mul, hinv, div_eq_mul_inv, mul_comm]
