import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_pos {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  set u := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hu
  have h0 : t.T.ϖ ≠ 0 := t.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective t.T.V (FractionRing t.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : t.ι u ≠ 0 := (map_ne_zero t.ι).2 hu0
  have hle : ‖t.ι u‖ ≤ 1 := (t.int u).2 ⟨_, rfl⟩
  have hlt : ‖t.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖t.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (t.int _).1 this
    apply t.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective t.T.V (FractionRing t.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖t.ι u‖ := norm_pos_iff.2 hι0
  unfold UCTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {φ : InvFun O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[O] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone bar X := StrictData.toReal_mem_psdCone hβ hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem posW_one : PosW (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![(1 : ℤ)] + (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) =
      Matrix.diagonal fun _ => (2 : ℝ) := by
    ext i j; fin_cases i; fin_cases j; norm_num
  rw [this]
  exact Matrix.PosDef.diagonal (fun _ => by norm_num)

end GlobalTheory.UPoinc.GApprox

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_evalZ_eq {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun (𝓞 E)}
    (hpol : IsPolFan H.bar (min D.p D.q) φ)
    (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min D.p D.q) p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (t : UCTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) :
    Φ.sc y * φ.evalZ (Φ.β y) = t.sc * φ.evalZ t.T.be :=
  sc_evalZ_eq_of_equiv (hpol _ (Φ.rank_le y)) (Φ.bal y) (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos t) e he

theorem exists_hasSupports_cm (q : ℕ) (φ : InvFun (𝓞 E)) (hpol : IsPolFan H.bar q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) q φ d :=
  exists_hasSupports (𝓞 E) H.bar q φ hpol fun X _ _ _ _ hX r γ hγ => GlobalTheory.T.exists_supportingTuple_smoothCone_cmField E H φ X (hpol X hX) r γ hγ

end GlobalTheory.UPoinc.GApprox

open GlobalTheory.UPoinc.GApprox in

theorem GlobalTheory.UPoinc.exists_uApproxAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∃ d : ℕ, 1 ≤ d ∧ UApproxAt X₁ φ d := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_cm (H := H) (min Dw.p Dw.q) φ hpol
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  have hW1 : ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat = 1 := by simp
  refine ⟨((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀, by rw [hW1]; omega, ?_⟩
  intro p _ z₁ t₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := t₀.cen ▸ isClosed_singleton_cPt t₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := GlobalTheory.T.exists_unitaryThetaSystem_classicalTraits_closedPoint E H Dw hpq l Xo c C X₁ p z₁ hcl
  have hF := GlobalTheory.T.unitary_classicalTraits_fourierTerms_all_levels E H Dw hpq l Xo c C X₁ p z₁ Φ hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre (𝓞 E) H.bar (bddAct_int_and_cm.2 E H) (min Dw.p Dw.q) φ hpol d₀ hsup 0
    !![(1 : ℤ)] posW_one (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  set d := ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀ with hd
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM t₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (t : UCTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e' a) (e' b)) →
      Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by
    intro y t e' h
    have := sc_evalZ_eq hpol Φ y t e' h
    calc Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = (d : ℝ) * (Φ.sc y * φ.evalZ (Φ.β y)) := by ring
      _ = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by rw [this]; ring
  refine ⟨f, ?_, fun t => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ t₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM t
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y t e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
