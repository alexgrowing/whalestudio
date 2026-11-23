import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValFeTranslate

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstExpSpan

open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

theorem exists_rep (M : Type) [AddCommGroup M] (j : ℕ) :
    ∃ (C : Type) (rep : C → M), ∀ α, ∃! x, ∃ mu, rep x + j • mu = α := by
  refine ⟨M ⧸ (nsmulAddMonoidHom j : M →+ M).range, Quotient.out, fun α => ⟨QuotientAddGroup.mk α, ?_, ?_⟩⟩
  · obtain ⟨mu, h⟩ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk α :
      M ⧸ (nsmulAddMonoidHom j : M →+ M).range))
    exact ⟨mu, by rw [show j • mu = _ from h, add_neg_cancel_left]⟩
  · rintro x ⟨mu, rfl⟩
    exact (QuotientAddGroup.out_eq' x).symm.trans (QuotientAddGroup.eq.2 ⟨mu, (neg_add_cancel_left _ _).symm⟩)

def valLin {R Z : Type} [CommRing R] [CommRing Z] [IsLocalRing Z] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (M : LB Y)
    (κ : R →+* Z) (p : Sp Z ⟶ Y) (hp : p ≫ π = spMap κ) (i : M.ι) (hi : ⊤ ≤ p ⁻¹ᵁ M.U i) :
    SecOver π M →ₛₗ[κ] Z where
  toFun s := valR p (M.U i) (LB.Sec.f s i)
  map_add' s t := toStkA_injective (by
    rw [map_add, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi,
      FormalValue.toStkA_valR_eq_gs _ _ _ hi]
    exact gs_add p _ _ (hi trivial) _ _)
  map_smul' r s := toStkA_injective (by
    have H : constVal (p ≫ π) (cpt Z) r = toStkA (cpt Z) (κ r) := by
      rw [hp, ← Category.id_comp (spMap κ)]
      exact (constVal_specMap _ κ _ r).trans (gs_eq (𝟙 _) _ ⊤ trivial _)
    rw [smul_eq_mul, map_mul, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi, ← H]
    exact gs_smul π p _ _ (hi trivial) r _)

theorem exists_pow_mul_eq_sum : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  intro hL E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W j σ hj
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e :=
    ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1, W.spec.2.2.2.2.1,
      fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨C, rep, hrep⟩ := exists_rep a.D₀.X j
  let bas := fun x => Module.Basis.ofVectorSpace ℂ (SecBMod a.D₀ j (rep x))
  have ex := fun i : Σ x, Module.Basis.ofVectorSpaceIndex ℂ (SecBMod a.D₀ j (rep x)) =>
    exists_expandsAt hW hL.globalFns hj W.P.U (rep i.1) (bas i.1 i.2)
  choose m hm using ex
  choose f s hf hE using fun i => hm i (m i) le_rfl
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_span hW hL.globalFns hj W.P.U rep hrep bas m f s hf hE σ
  obtain ⟨n, r, t, ht⟩ := Submodule.mem_span_set'.1 hN
  refine ⟨N, n, r, fun i => (t i).1, fun i => ?_, fun Z _ _ κ p k hp hk => ?_⟩
  · obtain ⟨q, hq⟩ := (t i).2
    refine (congrArg (HasConstExp W) hq).mp ⟨f q, hE q, fun x => ?_⟩
    rcases eq_or_off W.e j (rep q.1) (W.e x) with ⟨mu, h⟩ | h
    · obtain rfl := W.e.injective h
      refine ⟨feTranslate a.D₀ j mu _ (bas q.1 q.2), PowerSeries.X ^ ((m q : ℤ) + expo a j (rep q.1) mu).toNat,
        fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [((hf q).1 mu).2]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
    · refine ⟨(0 : SecBMod a.D₀ j x), 0, fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [(hf q).2 _ h, ← zero_smul ℂ⟦X⟧ (pullB hW j x 0)]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
  · let v := valLin W.t.G.hom
      (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ))) κ p hp (fun _ => k)
      (FormalValue.top_le_secChart hk)
    refine (congrArg (· * _) (map_pow κ _ N).symm).trans ((v.map_smulₛₗ _ σ).symm.trans
      ((congrArg v ht.symm).trans ((map_sum v _ _).trans (Finset.sum_congr rfl fun i _ => v.map_smulₛₗ _ _))))

end GlobalTheory.ConstExpSpan
