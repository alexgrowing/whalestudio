import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingClassicalTraitSameGeometricFibrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.ULabUniq

section Cong
variable {Y : Type} [AddCommGroup Y]

theorem cm_trans {N : ℕ} {x y z : Y} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_symm {N : ℕ} {x y : Y} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_map {Y' : Type} [AddCommGroup Y'] (f : Y →+ Y') {N : ℕ} {x y : Y} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add, map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : Y}
    (h : (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : Y} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

end Cong

theorem sc_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : UCTrait X p z) : 0 < c.sc := by
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h =>
    c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have h1 : 0 < ‖c.ι x‖ := norm_pos_iff.2 ((map_ne_zero c.ι).2 h0)
  have h2 : ‖c.ι x‖ < 1 := by
    by_contra h
    have : ‖c.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (c.int _).1 this
    refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)

open MonObj in

theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a ν, yy a = QuotientAddGroup.mk ν → yy' a = QuotientAddGroup.mk (κ ν) := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hS, -, -, hR, -, -, -, -, -, -, -, y₀, hy₀, u, lb, j, hq, hyy, -⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', -, hS₁, -, -, hR₁, -, -, -, -, -, -, -, y₁, hy₁, u', lb', j', hq',
    hyy', -⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab⟩ := GlobalTheory.T.unitaryRecharting_classicalTrait_same_geometric_fibre E H Dw l Xo cf C X p z ct c₀ hc R' fg frac hth hev ρ' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → ∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have tors' : ∀ m, 1 ≤ m → ∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have hqe : ∀ χ, lb'.q (e χ) = lb.q χ := fun χ => by
    have h2 := (hψ χ _).1 (lb.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (lb'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), lb.yy b = QuotientAddGroup.mk χ →
      lb'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := tors _ hrN x (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := tors' _ hrN x' (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u' b x' hx')
    have e1 := lb.yy_eq b pk x hpk hx
    have e2 := lb'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have e1 := hq χ
    have e2 := hq' (e χ)
    rw [hqe] at e2
    have hs := sc_pos ct
    have h4 : ((ct.T.be (j' (e χ)) (j' (e χ)) : ℤ) : ℝ) = ((ct.T.be (j χ) (j χ) : ℤ) : ℝ) := by
      have := e2.symm.trans e1
      have h5 : ct.sc * (ct.T.be (j' (e χ)) (j' (e χ)) : ℝ) = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) := by linarith
      exact mul_left_cancel₀ hs.ne' h5
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (lb'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (κ μ) := core

end GlobalTheory.UPoinc.ULabUniq
