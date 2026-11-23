import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingGaloisTransportDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodFormAutomorphismUnitaryLabellingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem three_le_level (X₁ : USetup C) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem uIsLab_onto (X : USetup C) {p : ℕ} [Fact p.Prime] {z : X.M.Z} (ct : UCTrait X p z)
    (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy) (μ : ct.T.P.D.toPre.X) :
    ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem be_pos (T : UTrait Xo cf) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • x) : ModN m X) = QuotientAddGroup.mk (κ (d • x))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  simp only [nsmulAddMonoidHom_apply, map_nsmul] at hw
  refine ⟨w, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

end GlobalTheory.UPoinc.UGalLab

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem eq_of_diag_congMod (T : UTrait Xo cf) (κ : T.P.D.toPre.X ≃+ T.P.D.toPre.X)
    (hd : ∀ x, T.be (κ x) (κ x) = T.be x x) (L : ℕ) (hL : 3 ≤ L) (hc : ∀ x, CongMod L (κ x) x) (x : T.P.D.toPre.X) :
    κ x = x := by
  let β : LinearMap.BilinForm ℤ T.P.D.toPre.X := T.be + T.be.flip
  have hβ : ∀ u v, β u v = T.be u v + T.be v u := fun u v => rfl
  let e : T.P.D.toPre.X ≃ₗ[ℤ] T.P.D.toPre.X := κ.toIntLinearEquiv
  have hiso : ∀ u v, β (e u) (e v) = β u v := by
    intro u v
    have huv := hd (u + v)
    simp only [map_add, LinearMap.add_apply] at huv
    rw [hd u, hd v] at huv
    rw [hβ, hβ]
    show T.be (κ u) (κ v) + T.be (κ v) (κ u) = _
    linarith
  have hpos : ∀ u, u ≠ 0 → 0 < β u u := fun u hu => by
    rw [hβ]; have := be_pos T u hu; linarith
  have he := eq_refl_of_isometry_congMod _ β hpos e hiso L hL hc
  have := congrArg (fun f : T.P.D.toPre.X ≃ₗ[ℤ] T.P.D.toPre.X => f x) he
  simpa [e] using this

end GlobalTheory.UPoinc.UGalLab

namespace GlobalTheory.UPoinc.UGalLab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem rigid (hpq : 1 ≤ Dw.p + Dw.q) {X₁ : USetup C} (D : UDeep X₁) {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}
    (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X) (h₁ : UIsLab X₁ ct yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X)
    (hl : UIsLab D.X (D.lift ct y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : UIsLab D.X (D.lift ct y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := GlobalTheory.T.exists_periodForm_automorphism_unitary_labellings E H Dw hpq l Xo cf C D.X p (y (cPt p)) (D.lift ct y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := uIsLab_onto X₁ ct yy₁ h₁ x
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  have hκ1 : ∀ x, κ x = x := eq_of_diag_congMod ct.T κ hκβ _ (three_le_level X₁) hcong
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ, hκ1]

end GlobalTheory.UPoinc.UGalLab

theorem GlobalTheory.UPoinc.UGalLab.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → UIsLab D.X (D.lift ct (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs
  obtain ⟨a, hfix, htr⟩ := GlobalTheory.T.unitary_labelling_galois_transport_deeper_level E H Dw hpq l Xo cf C X₁ D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ ct yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ ct y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GlobalTheory.UPoinc.UGalLab.rigid hpq D ct yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact DFunLike.congr_fun this x
