import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstFamComponentsBasisExpansion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValFeTranslate

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstFamValues

open ConstThetaSections ConstFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b}

omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem ex_add_nsmul (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) :
    Λ.u.ex (Λ.A.ct α + j • Λ.A.ct mu) = a.D₀.c (Λ.ε α + j • Λ.ε mu) := by
  rw [← map_nsmul, ← map_add, ← map_nsmul, ← map_add, Λ.ct]

omit [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem expo_eq (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) : expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := by
  rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]

theorem secVal_mul_genVal (Λ : GtAn a) (j : ℕ) (α mu : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (v : Λ.A.V) :
    FrameValue.secVal Λ.u a.D₀.P.isLB (feTranslate a.D₀ j (Λ.ε mu) (Λ.ε α) s₀) (Λ.u.ex v.2).left
        ![v.2, v.2 + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] *
      FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s (Λ.ε α + j • Λ.ε mu)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![(Λ.A.ct α + j • Λ.A.ct mu) + v.2, Λ.A.ct α + j • Λ.A.ct mu, v.2, 0] =
      Λ.A.term j α (Λ.fn j α s₀) mu v := by
  have h₁ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB ((Λ.ex0 v).s x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![z + v.2, z, v.2, 0] = eTwoPi (v.1 y) := by
    rintro y _ _ rfl rfl
    exact Λ.arcDict_expZero_section v y
  have h₂ : ∀ y x z, x = Λ.ε y → z = Λ.A.ct y → FrameValue.genVal Λ.u a.D₀.P.isLB (a.D₀.psi x)
      (Out.jFK (R := ℂ) ℂ) (fun _ => z) = Λ.A.psi y := by
    rintro y _ _ rfl rfl
    exact Λ.psi y
  refine (congrArg₂ (· * ·) (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu)
    (h₂ (mu + α) _ _ (map_add _ _ _).symm (map_add _ _ _).symm) s₀ v.2)
    (h₁ (α + j • mu) _ _ (by rw [map_add, map_nsmul]) (by rw [map_add, map_nsmul]))).trans ?_
  change Λ.fn j α s₀ (v.2 + Λ.A.ct mu) * _ * _ = _
  have n₁ := (Λ.A.psi mu).ne_zero
  have n₂ := (Λ.A.psi α).ne_zero
  simp only [AnArc.term, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Λ.A.psi_add]
  field_simp

end

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e) (j : ℕ) [NeZero j] (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (m : ℕ) (f : ∀ x, ConstFam.SecBMod W.P.D.toPre j x) (σ : Out.H0 W.P.U.LG.L j), ConstFam.IsIntegralForm hW j (Λ.ε α) s₀ m f → (∀ n, W.P.U.toUnifPre.ExpandsAt n j σ f) → Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α (Λ.fn j α s₀) v) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ hW j _ α s₀ m f σ hf hE v jL hL
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  have hm : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => expo_eq Λ j α mu ▸ (hf.1 (Λ.ε mu)).1
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ :=
    hJ.symm ▸ (admissibleBase_powerSeries ℂ).2.2.2
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  replace hM := (top_le_iff_cpt (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) _).2 hM
  obtain ⟨j₀, h₀⟩ : ∃ j₀, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := ⟨_, FrameValue.le_chartAt a.D₀.P.isLB _⟩
  have hd := ConstTerm.le_div (M := W.P.D.toPre.P.L) (φ := W.φ) (k := j₀) (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left)
    (hb ▸ FormalValue.top_le_comp h₀ _) hM
  have hτ := Ξ.τ_eq v jL jM j₀ hL hd
  have hu := FormalValue.isUnit_valR _ _ hd (W.w.s (fun _ => j₀, jM))
  choose jf jt hc using FormalValue.exists_cohCharts (Ξ.g v) jM hM
  have hs := exists_sum_sub_mem (i := fun mu => W.e (Λ.ε α + j • Λ.ε mu))
    (fun _ _ h => Λ.ε.injective (FamFree.add_nsmul_inj hj _ _ _ (W.e.injective h)))
    (n := fun mu => ((m : ℤ) + Λ.A.exponent j α mu).toNat)
    (c := fun mu => Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j)
    (h := fun x => valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j *
      (FormalValue.famVal (Ξ.g v) (f x) (jf x) * FormalValue.coordVal (Ξ.g v) x (jt x)))
    (fun mu => by
      rw [(hf.1 (Λ.ε mu)).2, ← secVal_mul_genVal, ← expo_eq]
      exact ConstTerm.core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v)
        (ex_add_nsmul Λ j α mu) (Λ.ex0_b v) (Ξ.g_rel v _) _ _ _
        (fun p => valR_smul_pullB hW j _ _ _ _ p _) jM j₀ _ _ (hc _) hd)
    (fun x hx => by
      have e : f x = 0 := hf.2 x fun mu h => hx (Λ.ε.symm (W.e.symm mu)) (by
        rw [Λ.ε.apply_symm_apply, map_add_nsmul, W.e.apply_symm_apply, h])
      have e' : FormalValue.famVal (Ξ.g v) (f x) (jf x) = 0 := by
        rw [e]
        exact (HolHom.valR_eq _ _ (hc x).1 _).trans (map_zero _)
      rw [e', zero_mul, mul_zero])
    (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
      have := hm mu
      rw [AnArc.mem_level]
      omega)
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α _ v hm, ← map_pow, ← map_mul]
  refine congrArg _ ((hu.pow j).mul_left_cancel (FormalValue.eq_of_forall_mk_eq
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => Ideal.Quotient.eq.2 ?_))
  obtain ⟨F, -, hF⟩ := ((FormalValue.value_eq_sum_expansion (admissibleBase_powerSeries ℂ) W.P.U (Ξ.g v) (Ξ.x v).left
    (Ξ.x_fm v)).2 j σ f hE).1 e
  obtain ⟨F', hFF, h₂⟩ := hs (e + 1) F
  have h₁ := hF F' jL jM jf jt hFF hL hM fun x _ => hc x
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
      Λ.A.term j α (Λ.fn j α s₀) mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α (Λ.fn j α s₀) mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, ← Finset.mul_sum, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow] at h₂
  replace h₂ := Ideal.pow_right_mono hJ.ge (e + 1) h₂
  have h₃ := congrArg (· ^ j) hτ
  simp only [mul_pow] at h₃
  convert add_mem (Ideal.mul_mem_left _ (valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j) h₁)
    (Ideal.mul_mem_left _ ((FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map
      (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (Ξ.x v).left jL jM).val ^ j) h₂) using 1
  linear_combination (-(PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m),
    Λ.A.term j α (Λ.fn j α s₀) mu v)) * h₃

end GlobalTheory.ConstFamValues
