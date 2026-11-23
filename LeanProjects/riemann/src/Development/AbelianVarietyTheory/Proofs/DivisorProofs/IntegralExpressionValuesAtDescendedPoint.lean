import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameValueLocalUnitsMulSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

theorem unit_of_val {K S : Type} [Field K] [CommRing S] [Nontrivial S] (f : K →+* S) {u v : Sˣ} {c : K}
    (h : u.val = v.val * f c) : ∃ m : Kˣ, (m : K) = c ∧ u = v * Units.map f.toMonoidHom m := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at h
    exact u.ne_zero h
  exact ⟨Units.mk0 c hc, rfl, Units.ext (by rw [h, Units.val_mul]; rfl)⟩

theorem toStk_surj' {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem units_identity {U : Type} [CommGroup U] (gO gB gP gC gCn R M2 M3 M4 M5 : U) :
    (gO⁻¹ * gB * M2) ^ 2 * (gP * gC⁻¹ * gB⁻¹ * gO * M3) ^ 2 * (gCn⁻¹ * gC * M4) *
        (gO * gC⁻¹ * gCn⁻¹ * gO * M5)⁻¹ * (R ^ 2)⁻¹ =
      gP ^ 2 * (gO⁻¹ ^ 2 * (R ^ 2)⁻¹) * (M2 ^ 2 * M3 ^ 2 * M4 * M5⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem sq_cancel {S : Type} [CommRing S] (a b c d f : S) (h : a * c = 1) :
    (a * b) ^ 2 * (c ^ 2 * d * f) = b ^ 2 * (d * f) := by
  linear_combination (a * c + 1) * b ^ 2 * d * f * h

theorem c_zero_eta {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) : D.c 0 = η[D.P.A] := by
  rw [GlobalTheory.Poinc.ThetaOne.c_zero]
  rfl

theorem ev_values : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  intro N₁ hN V₁ _ _ _ hV hunit D X C _ e τ₀ θ hθ b hb t ht χt hχt G hG K _ _ ev k₀ hk₀ W₀ _ ib hB hib
  obtain ⟨B₀, iG, M₀, c₀, τ₁, β, w, hFB⟩ := (fromBase_iff D τ₀ ib).1 hB
  have hM₀ : M₀.IsLB := hFB.2.1
  let z : Sp K := IsLocalRing.closedPoint K
  choose J hJ using fun ψ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J₀ hJ₀ using fun ψ : Sp K ⟶ B₀.left => exists_chart hM₀ (ψ z)
  have gJ : Good D.P.L z J := hJ
  have gJ₀ : Good M₀ z J₀ := hJ₀
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ θ hθ
  set r : Sp K ⟶ Sp V₁ := spMap ev with hr
  set U0 : ((Sp K).presheaf.stalk z)ˣ := (gwx w z J J₀ (r ≫ (D.c 0).left))⁻¹ ^ 2 * (rigV D r z J ^ 2)⁻¹ with hU0
  have hO : r ≫ (η[D.P.A]).left = r ≫ (D.c 0).left := by rw [c_zero_eta]
  have key : ∀ mu c, ∃ q ∈ k₀, toStk z (ev (G mu c)) = toStk z (κ ^ 2 * q) * U0.val := by
    intro mu c
    obtain ⟨hBd, -, hPd, -⟩ := GlobalTheory.T.torsionPoints_projections_defined_over_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib N₁ (by omega)
      (b c) (hb c) (e mu)
    obtain ⟨c1, hc1, e1⟩ := hκ (b c * D.c (e mu)) hPd
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (b c) (hb c) hBd (t c) (ht c)
    obtain ⟨c3, hc3, e3⟩ := GlobalTheory.T.characterValue_mem_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (e mu) (b c) (hb c) hBd (χt mu c) (hχt mu c)
    obtain ⟨c4, hc4, e4⟩ := GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ (e mu)
    obtain ⟨c5, hc5, e5⟩ := GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀
      (e mu) (-e mu)
    have hPP : r ≫ (D.c (e mu) * b c).left = r ≫ (b c * D.c (e mu)).left := by rw [mul_comm]
    have h00 : r ≫ (D.c (e mu + -e mu)).left = r ≫ (D.c 0).left := by rw [add_neg_cancel]
    rw [hO] at e2 e3
    rw [hPP] at e3
    rw [h00] at e5
    obtain ⟨m2, rfl, u2⟩ := unit_of_val (toStk z) e2
    obtain ⟨m3, rfl, u3⟩ := unit_of_val (toStk z) e3
    obtain ⟨m4, rfl, u4⟩ := unit_of_val (toStk z) e4
    obtain ⟨m5, rfl, u5⟩ := unit_of_val (toStk z) e5
    have h1 := hG mu c (Sp K) r z J gJ
    rw [u2, u3, u4, u5, e1, units_identity, ← hU0] at h1
    have hL : gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) = toStk z (ev (G mu c)) := by
      have := GlobalTheory.RatioVal.gs_specMap ev z ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c))
      rw [Iso.inv_hom_id_apply] at this
      exact this
    refine ⟨c1 ^ 2 * ((m2 : K) ^ 2 * (m3 : K) ^ 2 * (m4 : K) * (m5 : K)⁻¹),
      k₀.mul_mem (k₀.pow_mem hc1 2) (k₀.mul_mem (k₀.mul_mem (k₀.mul_mem (k₀.pow_mem hc2 2) (k₀.pow_mem hc3 2)) hc4)
        (k₀.inv_mem hc5)), ?_⟩
    rw [← hL, h1, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
      sq_cancel _ _ _ _ _ (Units.inv_mul _)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← map_inv, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Units.val_inv_eq_inv_val, map_mul, map_pow]
    ring
  obtain ⟨lam, hlam⟩ := toStk_surj' z U0.val
  refine ⟨κ ^ 2 * lam, fun mu c => ?_⟩
  obtain ⟨q, hq, eq⟩ := key mu c
  refine ⟨q, hq, (toStk z).injective ?_⟩
  rw [eq, ← hlam, ← map_mul]
  congr 1
  ring

end GlobalTheory.USep.EvG
