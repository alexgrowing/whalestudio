import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValFeTranslate

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.ConstThetaSections

open ConstFam FormalValue

theorem exists_vals_fsum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) [NeZero j] (α : Λ.A.X), ∀ th ∈ Λ.A.Theta j α, ∃ (m : ℕ) (σ : Out.H0 W.P.U.LG.L j), Ξ.Vals σ (fun v => HahnSeries.single (m : ℤ) (1 : ℂ) * Λ.A.FSum j α th v) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j _ α th hth
  have hj : 1 ≤ j := NeZero.one_le
  obtain ⟨s₀, hs₀, -⟩ := ((ArcThetaSpaces.sections_theta hL hL₂ E H D l c O β b a Λ).1 j α hj).2 th hth
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e := ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1,
    W.spec.2.2.2.2.1, fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨m, hm⟩ := exists_expandsAt hW hL.globalFns hj W.P.U (Λ.ε α) s₀
  obtain ⟨f, σ, hf, hE⟩ := hm m le_rfl
  have ex : ∀ mu, expo a j (Λ.ε α) (Λ.ε mu) = Λ.A.exponent j α mu := fun mu => by
    rw [expo, AnArc.exponent, AnArc.q, Λ.be_eq, Λ.be_eq]
  have hpos : ∀ mu, 0 ≤ (m : ℤ) + Λ.A.exponent j α mu := fun mu => ex mu ▸ (hf.1 (Λ.ε mu)).1
  have comp : ∀ mu, ∃ t : SecBMod a.D₀ j (Λ.ε (α + j • mu)), f (W.e (Λ.ε (α + j • mu))) =
      (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
      ∀ z, Λ.fn j (α + j • mu) t z = Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := fun mu => by
    have cast : ∀ x, Λ.ε α + j • Λ.ε mu = x → ∃ t : SecBMod a.D₀ j x, f (W.e x) =
        (PowerSeries.X : ℂ⟦X⟧) ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat • pullB hW j _ t ∧
        ∀ z, FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left
          ![z, z + (Λ.A.ct α + j • Λ.A.ct mu), Λ.A.ct α + j • Λ.A.ct mu, 0] =
            Λ.A.psi mu ^ j * eTwoPi (Λ.A.T mu α) * th (z + Λ.A.ct mu) := by
      rintro _ rfl
      refine ⟨_, ex mu ▸ (hf.1 (Λ.ε mu)).2, fun z => ?_⟩
      have es := Λ.psi (mu + α)
      rw [map_add Λ.ε, map_add Λ.A.ct] at es
      refine (secVal_feTranslate Λ.ah Λ.rig j (Λ.ct α) (Λ.ct mu) (Λ.psi α) (Λ.psi mu) es s₀ z).trans ?_
      refine (congrArg (· * _) (congrFun hs₀ (z + Λ.A.ct mu))).trans ?_
      have := (Λ.A.psi mu).ne_zero
      have := (Λ.A.psi α).ne_zero
      push_cast
      rw [Λ.A.psi_add]
      field_simp
    obtain ⟨t, h₁, h₂⟩ := cast (Λ.ε (α + j • mu)) (by rw [map_add, map_nsmul])
    refine ⟨t, h₁, fun z => Eq.trans ?_ (h₂ z)⟩
    exact congrArg (fun q => FrameValue.secVal Λ.u a.D₀.P.isLB t (Λ.u.ex z).left ![z, z + q, q, 0])
      ((map_add Λ.A.ct _ _).trans (congrArg _ (map_nsmul Λ.A.ct _ _)))
  refine ⟨m, σ, fun v jL hjL => ?_⟩
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB (basePt (Ξ.g v) (cpt ℂ⟦X⟧))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB (W.φ (basePt (Ξ.g v) (cpt ℂ⟦X⟧)))
  have hM' := (top_le_iff_cpt _ _).2 hM
  have hw : ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 ⟨mem_pull.2 h₀, hM⟩
  choose jf jt hc using exists_cohCharts (Ξ.g v) jM hM'
  obtain ⟨w, hw'⟩ := isUnit_valR (A := ℂ⟦X⟧) _ _ hw (W.w.s (fun _ => j₀, jM))
  have hτ := Ξ.τ_eq v jL jM j₀ hjL hw
  have hI : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} :=
    Ideal.map_id _
  have hx := Ξ.x_fm v
  rw [hI, ← hw'] at hτ
  rw [hI] at hx
  let i : Λ.A.X → W.P.D.toPre.X := fun mu => W.e (Λ.ε (α + j • mu))
  have hi : Function.Injective i := fun mu mu' h =>
    smul_right_injective Λ.A.X (Int.natCast_ne_zero.2 (NeZero.ne j)) ((natCast_zsmul mu j).trans
      ((add_left_cancel (Λ.ε.injective (W.e.injective h))).trans (natCast_zsmul mu' j).symm))
  let h : W.P.D.toPre.X → ℂ⟦X⟧ := fun x => w.val ^ j * (famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x))
  have h₁ : ∀ mu, h (i mu) = PowerSeries.X ^ ((m : ℤ) + Λ.A.exponent j α mu).toNat *
      PowerSeries.C (Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) := fun mu => by
    obtain ⟨t, e₁, e₂⟩ := comp mu
    have := GlobalTheory.ConstTerm.main hL hL₂ E H D l Xo c O β Y b a χ W Λ Ξ j (α + j • mu) t (f (i mu)) _
      (fun Z _ _ p κ jf j₀ hp hi => by
        rw [show f (i mu) = _ from e₁]
        exact valR_smul_pullB hW j _ t _ Z p κ jf j₀ hp hi) v jM j₀ _ _ (hc (i mu)) hw
    rw [← hw', e₂] at this
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [AnArc.term]; ring
  have h₂ : ∀ x, (∀ mu, i mu ≠ x) → h x = 0 := fun x hx => by
    have e₁ : f x = 0 := hf.2 x fun y e => hx (Λ.ε.symm (W.e.symm y)) (by
      rw [← e]
      show W.e (Λ.ε _) = _
      rw [map_add, map_add, map_nsmul, map_nsmul, Λ.ε.apply_symm_apply, W.e.apply_symm_apply])
    have e₂ : famVal (Ξ.g v) (f x) (jf x) = 0 := by
      rw [e₁]
      exact (dif_pos (hc x).1).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    show _ * (_ * _) = _
    rw [e₂, zero_mul, mul_zero]
  beta_reduce
  rw [← algebraMap_mk_eq Λ.A j α th v hpos, ← map_pow, ← map_mul]
  refine congrArg _ ((Units.mul_right_inj (w ^ j)).1 (eq_of_forall_mk_eq (Ideal.span {PowerSeries.X}) fun e => ?_))
  have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)})) e
  obtain ⟨F, hF⟩ := map_secVal_eq W.P.U.toUnifPre (hE e)
  obtain ⟨F', hF', hd⟩ := exists_sum_sub_mem hi h₁ h₂ (L := fun k => Λ.A.level j α ((k : ℤ) - m)) (fun k mu => by
    have := hpos mu
    rw [Λ.A.mem_level]
    omega) (e + 1) F
  have H := (hF _ _ _ _ _ hx _ (Ideal.Quotient.mk (Ideal.span {PowerSeries.X} ^ (e + 1))) Ideal.mk_ker.ge).2
    F' jL jM jf jt hF' hjL hM' fun x _ => hc x
  rw [map_mul, H, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e₁ : (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v * Λ.u.fr j₀ v.2 ^ j) =
      (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) *
        PowerSeries.C (Λ.u.fr j₀ v.2) ^ j := by
    ext k
    rw [← map_pow, PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Finset.sum_mul]
  rw [e₁, show ∑ x ∈ F', h x = w.val ^ j * ∑ x ∈ F', famVal (Ξ.g v) (f x) (jf x) * coordVal (Ξ.g v) x (jt x) from
    (Finset.mul_sum _ _ _).symm] at hd
  refine (congrArg (_ ∣ ·) ?_).mp (hd.mul_left ((tau W.P.U.toUnifPre (Ideal.span {PowerSeries.X}) (Ξ.x v).left jL jM).val ^ j))
  rw [Units.val_pow_eq_pow_val]
  have := congrArg (· ^ j) hτ
  simp only [mul_pow] at this
  linear_combination (PowerSeries.mk fun k : ℕ => ∑ mu ∈ Λ.A.level j α ((k : ℤ) - m), Λ.A.term j α th mu v) * this

end GlobalTheory.ConstThetaSections
