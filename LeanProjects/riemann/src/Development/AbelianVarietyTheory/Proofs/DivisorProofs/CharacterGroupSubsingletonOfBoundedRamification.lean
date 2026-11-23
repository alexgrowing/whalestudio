import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLabRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsRam

theorem classes_fixed {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    {D : DegData W (maximalIdeal W)} {Q : PolAV (Sp (FractionRing W))} {H : Over (Sp W)} [GrpObj H] [IsCommMonObj H]
    (hH : IsSemiAbelian H) (U : Unif (maximalIdeal W) D Q H) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k) (σ : F ≃+* F)
    (hσ : σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F)
    (hfixH : ∀ x : TF (R := W) F ⟶ H, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left)
    (p q : QkPt D.toPre F k) (hpq : QkExt σ.toRingHom p q) : QkPt.Equiv D.toPre F p q := by
  haveI : CharZero W := hW.2.2
  have hA := GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hW
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨f, hf, hiff⟩ := GlobalTheory.Mum.Recog.exists_goodLab hA hH U F
  have hx₀ : f k p ^ k = 1 := hf.pow k hk p
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback Q.A H (jK W) (U.gen.inv.left ≫ pullback.fst H.hom (jK W)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback H (jK W))).congr (Category.id_comp _) rfl
  have w₁ : ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) ≫ H.hom = jFK (R := W) F ≫ jK W := by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w (f k p)]; rfl
  let xG : TF (R := W) F ⟶ H := Over.homMk ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) w₁
  have hxG : xG ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := f k p) rfl).1 hx₀
  have fixG := hfixH xG hxG
  let σ' : F →ₐ[FractionRing W] F := ⟨σ.toRingHom, RingHom.congr_fun hσ⟩
  have s₂ : spMap σ.toRingHom ≫ jFK (R := W) F = jFK (R := W) F := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  have fix₀ : spMap σ.toRingHom ≫ (f k p).left = (f k p).left := by
    refine gp.1.hom_ext ?_ ?_
    · rw [Category.assoc]; exact fixG
    · rw [Category.assoc, Over.w (f k p)]; exact s₂
  let x' : TFK (R := W) F ⟶ Q.A := Over.homMk (spMap σ.toRingHom ≫ (f k p).left) (by
    rw [Category.assoc, Over.w (f k p)]; exact s₂)
  have hq : QkToAkU U.toUnifPre F k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL W (maximalIdeal W) hA D Q H hH U F F σ' k hk p q (f k p) x' hpq rfl).1
      ((hiff k hk p (f k p)).2 rfl)
  have e : x' = f k p := Over.OverMorphism.ext fix₀
  exact (hf.eqv k hk p q).1 (e.symm.trans ((hiff k hk q x').1 hq))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam
open GlobalTheory.BXOf in

theorem psiLoc_not_unit {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (D : DegData W (maximalIdeal W))
    (J₀ : D.toPre.P.A.left → D.toPre.P.L.ι) (h₀ : ∀ x, x ∈ D.toPre.P.L.U (J₀ x)) (χ : D.toPre.X) (hχ : χ ≠ 0) (u : Wˣ)
    (hu : (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
      algebraMap W _ u) : False := by
  obtain ⟨e, -, a, ha, hψ⟩ := GlobalTheory.LevelOneIdeal.exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) J₀ h₀
  have h1 := hψ (TK W).left (𝟙 _) (closedPoint (FractionRing W)) J hJ
  have hj : J (𝟙 _ ≫ D.toPre.xK χ) = J₀ ((D.toPre.c χ).left (closedPoint W)) := by
    rw [Category.id_comp]
    exact eJ (D.toPre.c χ).left
  have e0 := val_of (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J _ (fun _ => hj)
  have e1 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J).val = algebraMap W _ u := by
    rw [e0]; exact hu
  obtain ⟨u', hu'⟩ := GlobalTheory.UnramTorsion.val_integral (algebraMap W (FractionRing W)) h₀ eJ e (𝟙 _)
  have e2 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (cst (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) a) = algebraMap W _ a := by
    rw [Category.id_comp]; exact GlobalTheory.UnramTorsion.stalk_gs_top _ a
  have e3 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val e (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) J).val = algebraMap W _ u' := by
    rw [Category.id_comp]; exact hu'
  have e4 := congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom h1
  rw [map_mul, e1, e2, e3, ← map_mul] at e4
  have e5 := IsFractionRing.injective W (FractionRing W) e4
  exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_mul_isUnit_left (e5 ▸ u.isUnit))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

theorem zpow_of_mul_eq {F : Type} [Field F] {a b c : F} {e : ℕ} (hb : b ≠ 0) (h : a * b = c ^ e) (m : ℤ) :
    a ^ m = c ^ ((e : ℤ) * m) * b ^ (-m) := by
  rw [show a = c ^ e * b⁻¹ by rw [← h, mul_inv_cancel_right₀ hb], mul_zpow, zpow_mul, zpow_natCast, inv_zpow']

theorem coe_units_zpow {F : Type} [Field F] (T : Subring F) (w : Tˣ) (z : ℤ) :
    (((w ^ z : Tˣ) : T) : F) = ((w : T) : F) ^ z :=
  (congrArg Units.val (map_zpow (Units.map T.subtype.toMonoidHom) w z)).trans (Units.val_zpow_eq_zpow_val _ _)

theorem subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  intro W _ _ _ hW D Q H _ _ hH U _ F _ _ _ n N hn Hj
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : CharZero W := hW.2.2
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing W) F).injective
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := FractionRing W) hπ
    (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W)))).ne_zero
  have key : ∀ j : ℕ, ∃ e : ℕ, 1 ≤ e ∧ e ≤ N ∧ (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ) ∧
      ∀ χ, (e : ℤ) * m (-χ) = (e : ℤ) * m χ := fun j => by
    obtain ⟨T, hT, g, e, hg, he1, heN, hram, hfix⟩ := Hj j
    obtain ⟨ϖ, hϖ, v, hv⟩ := hram π hπ
    have hP : ∀ r, r ∈ (closedPoint W).asIdeal ↔ ¬ IsUnit (g r) := fun r => by
      show r ∈ maximalIdeal W ↔ _
      refine ⟨fun hr hgr => ?_, fun h => (mem_maximalIdeal r).2 fun hr => h (hr.map g)⟩
      · rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
        obtain ⟨s, rfl⟩ := hr
        rw [map_mul] at hgr
        have h1 : IsUnit (ϖ ^ e) := hv ▸ (isUnit_of_mul_isUnit_left hgr).mul v.isUnit
        exact hϖ.not_isUnit (isUnit_pow_iff (by omega) |>.1 h1)
    have hv' : (g π : F) * ((v : T) : F) = (ϖ : F) ^ e := by
      have := congrArg (fun t : T => (t : F)) hv
      simpa only [Subring.coe_mul, Subring.coe_pow] using this
    have hvne : ((v : T) : F) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
    have hm : ∀ χ, ∃ u' : Tˣ, algebraMap (FractionRing W) F
        (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
        ((u' : T) : F) * (ϖ : F) ^ ((fun χ => (e : ℤ) * m χ) χ) := fun χ =>
      ⟨Units.map g.toMonoidHom (u χ) * v ^ (-(m χ)), by
        rw [hu χ, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hg, ← hg, Units.val_mul, Subring.coe_mul,
          coe_units_zpow, zpow_of_mul_eq hvne hv' (m χ)]
        rw [show (((Units.map g.toMonoidHom (u χ) : Tˣ) : T) : F) = (g (u χ) : F) from rfl]
        ring⟩
    have hσ : ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) →
        σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F := fun σ hσ =>
      IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun r => by
        show σ (algebraMap (FractionRing W) F (algebraMap W _ r)) = algebraMap (FractionRing W) F (algebraMap W _ r)
        rw [← hg]; exact hσ _ (g r).2)
    obtain ⟨h1, h2⟩ := GlobalTheory.UnramTorsion.level_step hL.1.mulN D.tau_bimult D.psi_even (closedPoint W) J₀ h₀ (n ^ j)
      (pow_ne_zero _ (by omega)) T g hg hP ϖ hϖ (fun χ => (e : ℤ) * m χ) hm
      (fun σ hσ' p q hpq => classes_fixed hW hH U F (Nat.one_le_pow _ _ (by omega)) σ (hσ σ hσ')
        (fun x hx => hfix σ hσ' x hx) p q hpq)
    exact ⟨e, he1, heN, h1, h2⟩
  have add : ∀ y χ, m (y + χ) = m y + m χ := fun y χ => by
    obtain ⟨e, he1, heN, hdiv, -⟩ := key (N * (m (y + χ) - m y - m χ).natAbs)
    have h1 := hdiv y χ
    rw [show (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ = (e : ℤ) * (m (y + χ) - m y - m χ) by ring] at h1
    by_contra hne
    have hd : m (y + χ) - m y - m χ ≠ 0 := fun h => hne (by omega)
    have h2 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 (by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ heN) (Nat.lt_pow_self (by omega)))
    exact (mul_ne_zero (by exact_mod_cast (show e ≠ 0 by omega)) hd) h2
  have even : ∀ χ, m (-χ) = m χ := fun χ => by
    obtain ⟨e, he1, -, -, h⟩ := key 0
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast (show e ≠ 0 by omega)) (h χ)
  have m0 : ∀ y, m y = 0 := fun y => by
    have a := add 0 0
    have b := add y (-y)
    rw [add_zero] at a
    rw [add_neg_cancel, even] at b
    omega
  have z : ∀ y : D.toPre.X, y = 0 := fun y => by
    by_contra hy
    refine psiLoc_not_unit D J₀ h₀ y hy (u y) ?_
    rw [hu y, m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one]
  exact ⟨fun a b => (z a).trans (z b).symm⟩

end GlobalTheory.TorsRam

end
