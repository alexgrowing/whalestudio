import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

namespace GlobalTheory.PeriodFormCompare

variable {R : Type} [CommRing R] [IsDomain R]

theorem generic_val (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) = algebraMap R (FractionRing R) r := by
  have e : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [e]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (jK R).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

theorem psiCoord_iff (D : DegPre R) (χ : D.X) (r : R) :
    PsiCoord D χ r ↔ ∃ x, IsPsiCoord D χ x ∧ x.val = algebraMap R (FractionRing R) r := by
  constructor
  · rintro ⟨j, hj, h, e⟩
    exact ⟨_, ⟨j, h, hj, rfl⟩, (congrArg _ e.symm).trans (generic_val r)⟩
  · rintro ⟨_, ⟨j, h, hj, rfl⟩, e⟩
    refine ⟨j, hj, h, ?_⟩
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
      ((generic_val r).trans e.symm)

theorem isPsiCoord_toUnitK {D : DegPre R} {χ : D.X} {r : R} (h : PsiCoord D χ r) (h0 : r ≠ 0) :
    IsPsiCoord D χ (toUnitK r h0) := by
  obtain ⟨x, hx, e⟩ := (psiCoord_iff D χ r).1 h
  have : x = toUnitK r h0 := Units.ext e
  exact this ▸ hx

theorem exists_psiCoord_iff [IsLocalRing R] (D : DegPre R) (χ : D.X) :
    (∃ r, PsiCoord D χ r) ↔ D.PsiIn χ ⊤ := by
  constructor
  · rintro ⟨r, hr⟩
    exact (PeriodFormEdge.psiIn_iff hr ⊤).2 trivial
  · intro hI
    obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D χ
    have h := PsiCoordLocal.generic_le D χ j hj
    obtain ⟨s, -, e⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
    exact ⟨r, j, hj, h, e⟩

theorem exists_psiCoord_of_isPsiCoord [IsLocalRing R] {D : DegPre R} {χ : D.X} (hI : D.PsiIn χ ⊤)
    {x : (FractionRing R)ˣ} (hx : IsPsiCoord D χ x) :
    ∃ r, PsiCoord D χ r ∧ x.val = algebraMap R (FractionRing R) r := by
  obtain ⟨r, hr⟩ := (exists_psiCoord_iff D χ).2 hI
  obtain ⟨y, hy, e⟩ := (psiCoord_iff D χ r).1 hr
  obtain ⟨u, hu⟩ := hx.unique hy
  have : x.val = algebraMap R (FractionRing R) (u * r) := by
    rw [hu, map_mul, ← e]; rfl
  exact ⟨u * r, (psiCoord_iff D χ _).2 ⟨x, hx, this⟩, this⟩

theorem psiIn_top {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) : D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h; exact (PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

theorem ordPsi_eq_psiOrd [IsLocalRing R] (D : DegData R (maximalIdeal R)) (χ : D.toPre.X) :
    ordPsi D.toPre χ = psiOrd D χ := rfl

section DVR

variable [IsDiscreteValuationRing R]

theorem exists_ord (r : R) (h0 : r ≠ 0) : ∃ n : ℕ,
    (⨆ (k : ℕ) (_ : r ∈ maximalIdeal R ^ k), (k : ℕ∞)) = n ∧ (ord_vw R).toFun (toUnitK r h0) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  refine ⟨n, PeriodFormEdge.iSup_pow_mem hϖ u n, ?_⟩
  have e : toUnitK ((u : R) * ϖ ^ n) h0 =
      Units.map (algebraMap R (FractionRing R)).toMonoidHom u * toUnitK ϖ hϖ.ne_zero ^ n := by
    ext; simp [toUnitK]
  have h1 : (ord_vw R).toFun 1 = 0 := by simpa using (ord_vw R).map_unit 1
  rw [e, (ord_vw R).map_mul, (ord_vw R).map_unit, zero_add]
  clear e h0
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [pow_succ, (ord_vw R).map_mul, ih, ord_vw_uniformiser _ hϖ.maximalIdeal_eq]; push_cast; rfl

theorem exists_ordPsi {D : DegPre R} {χ : D.X} (hI : D.PsiIn χ ⊤) :
    ∃ n : ℕ, ordPsi D χ = n ∧ psiOrd_vw D χ = n := by
  obtain ⟨r, hr⟩ := (exists_psiCoord_iff D χ).2 hI
  have h0 := PsiCoordLocal.ne_zero_of_coord hr
  obtain ⟨n, h1, h2⟩ := exists_ord r h0
  refine ⟨n, ?_, (psiVal_eq _ (isPsiCoord_toUnitK hr h0)).trans h2⟩
  unfold ordPsi
  simp only [PeriodFormEdge.psiIn_iff hr]
  exact h1

theorem psiOrd_vw_neg {D : DegPre R} {χ : D.X} (hI : ¬ D.PsiIn χ ⊤) : psiOrd_vw D χ < 0 := by
  have hn : ∀ r : R, (psiCoord D χ).val ≠ algebraMap R (FractionRing R) r := fun r e =>
    hI ((exists_psiCoord_iff D χ).1 ⟨r, (psiCoord_iff D χ r).2 ⟨_, psiCoord_spec D χ, e⟩⟩)
  rcases ValuationRing.isInteger_or_isInteger R (psiCoord D χ).val with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact absurd hr.symm (hn r)
  · have h0 : r ≠ 0 := by
      rintro rfl
      exact inv_ne_zero (psiCoord D χ).ne_zero (by simpa using hr.symm)
    have hm : r ∈ maximalIdeal R := by
      by_contra hu
      obtain ⟨u, rfl⟩ := notMem_maximalIdeal.1 hu
      refine hn (u⁻¹ : Rˣ) ?_
      rw [map_units_inv, hr, inv_inv]
    have e : psiCoord D χ * toUnitK r h0 = 1 := by
      ext; simp [toUnitK, hr]
    have h1 : (ord_vw R).toFun 1 = 0 := by simpa using (ord_vw R).map_unit 1
    have h2 := (ord_vw R).map_mul (psiCoord D χ) (toUnitK r h0)
    have h3 := ord_vw_pos h0 hm
    rw [e, h1] at h2
    change (ord_vw R).toFun (psiCoord D χ) < 0
    omega

theorem ordPsi_eq_toNat (D : DegPre R) (χ : D.X) : ordPsi D χ = ((psiOrd_vw D χ).toNat : ℕ∞) := by
  by_cases hI : D.PsiIn χ ⊤
  · obtain ⟨n, h1, h2⟩ := exists_ordPsi hI
    rw [h1, h2, Int.toNat_natCast]
  · rw [PeriodFormEdge.ordPsi_of_pole D χ hI, Int.toNat_eq_zero.2 (psiOrd_vw_neg hI).le]; rfl

theorem ordPsi_toNat_eq_iff (D : DegPre R) (χ : D.X) :
    ((ordPsi D χ).toNat : ℤ) = psiOrd_vw D χ ↔ D.PsiIn χ ⊤ := by
  constructor
  · intro h
    by_contra hI
    have := psiOrd_vw_neg hI
    omega
  · intro hI
    obtain ⟨n, h1, h2⟩ := exists_ordPsi hI
    rw [h1, h2, ENat.toNat_coe]

theorem betaZ_eq {D : DegPre R} {a b : D.X} (ha : D.PsiIn a ⊤) (hb : D.PsiIn b ⊤) (hab : D.PsiIn (a + b) ⊤) :
    betaZ D a b = periodForm_vw D a b := by
  rw [betaZ, (ordPsi_toNat_eq_iff D _).2 ha, (ordPsi_toNat_eq_iff D _).2 hb, (ordPsi_toNat_eq_iff D _).2 hab]
  rfl

theorem ordNat_eq {p : ℕ} (hp : IsOverPrime R p) : ∃ e : ℕ, ordNat R p = e ∧ ramIdx hp = e :=
  exists_ord (p : R) hp.ne_zero

theorem betaP_eq {p : ℕ} (hp : IsOverPrime R p) {D : DegPre R} {a b : D.X} (ha : D.PsiIn a ⊤) (hb : D.PsiIn b ⊤)
    (hab : D.PsiIn (a + b) ⊤) : betaP D p a b = (periodForm_vp hp D a b : ℝ) := by
  obtain ⟨e, h1, h2⟩ := ordNat_eq hp
  rw [betaP, periodForm_vp_eq, betaZ_eq ha hb hab, h1, h2]
  simp

end DVR

section At

variable [IsLocalRing R] {C : Type} [NormedField C]

def ReadsAt (v : LatticeVal R ℝ) (f : R →+* C) (p : ℕ) : Prop :=
  ∀ (r : R) (h0 : r ≠ 0), f r ≠ 0 → v.toFun (toUnitK r h0) = -Real.logb p ‖f r‖

theorem vPsiAt_eq_psiVal {v : LatticeVal R ℝ} {f : R →+* C} {p : ℕ} (hv : ReadsAt v f p) {D : DegPre R} {χ : D.X}
    (h : ∃ r, PsiCoord D χ r ∧ f r ≠ 0) : vPsiAt D f p χ = psiVal v D χ := by
  obtain ⟨r, hr, hf⟩ := h
  have h : ∃ r, PsiCoord D χ r := ⟨r, hr⟩
  have h0 := PsiCoordLocal.ne_zero_of_coord h.choose_spec
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_unit_of_coord h.choose_spec hr
  have hf' : f h.choose ≠ 0 := fun e => hf (by rw [hu, map_mul, e, mul_zero])
  rw [vPsiAt, dif_pos h, psiVal_eq v (isPsiCoord_toUnitK h.choose_spec h0), hv _ h0 hf']

theorem betaAt_eq_periodForm {v : LatticeVal R ℝ} {f : R →+* C} {p : ℕ} (hv : ReadsAt v f p) {D : DegPre R}
    {a b : D.X} (ha : ∃ r, PsiCoord D a r ∧ f r ≠ 0) (hb : ∃ r, PsiCoord D b r ∧ f r ≠ 0)
    (hab : ∃ r, PsiCoord D (a + b) r ∧ f r ≠ 0) : betaAt D f p a b = periodForm v D a b := by
  rw [betaAt, vPsiAt_eq_psiVal hv ha, vPsiAt_eq_psiVal hv hb, vPsiAt_eq_psiVal hv hab, periodForm]

omit [IsLocalRing R] in

theorem exists_readsAt (f : R →+* C) (hle : ∀ r, ‖f r‖ ≤ 1) (p : ℕ) : ∃ v : LatticeVal R ℝ, ReadsAt v f p := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let S := Localization.AtPrime (RingHom.ker f)
  have hf : ∀ y : (RingHom.ker f).primeCompl, IsUnit (f y) := fun y => Ne.isUnit y.2
  have hk : ∀ y : (RingHom.ker f).primeCompl, IsUnit (algebraMap R (FractionRing R) y) := fun y =>
    (toUnitK y.1 (fun e => y.2 (by rw [e]; exact zero_mem _))).isUnit
  let g : S →+* C := IsLocalization.lift hf
  let i : S →+* FractionRing R := IsLocalization.lift hk
  have hi : Function.Injective i := by
    refine (IsLocalization.lift_injective_iff hk).2 fun x y => ⟨fun e => ?_, fun e => ?_⟩
    · simpa using congrArg (IsLocalization.lift (S := S) hk) e
    · rw [IsFractionRing.injective R (FractionRing R) e]
  let w : Additive Sˣ →+ ℝ := AddMonoidHom.mk' (fun u => -Real.logb p ‖g u.toMul.val‖) fun x y => by
    rw [toMul_add, Units.val_mul, map_mul, norm_mul,
      Real.logb_mul (norm_ne_zero_iff.2 (x.toMul.isUnit.map g).ne_zero)
        (norm_ne_zero_iff.2 (y.toMul.isUnit.map g).ne_zero), neg_add]
  let ι : Additive Sˣ →+ Additive (FractionRing R)ˣ := (Units.map i.toMonoidHom).toAdditive
  have hι : Function.Injective ι := fun x y e =>
    Additive.toMul.injective (Units.map_injective (f := i.toMonoidHom) hi (congrArg Additive.toMul e))
  obtain ⟨v, hv⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom ι hι w
  have key : ∀ (r : R) (h0 : r ≠ 0), f r ≠ 0 → v (Additive.ofMul (toUnitK r h0)) = -Real.logb p ‖f r‖ := by
    intro r h0 hr
    have hu : IsUnit (algebraMap R S r) := IsLocalization.map_units S (⟨r, hr⟩ : (RingHom.ker f).primeCompl)
    have e : Additive.ofMul (toUnitK r h0) = ι (Additive.ofMul hu.unit) := by
      refine congrArg Additive.ofMul (Units.ext ?_)
      exact (IsLocalization.lift_eq hk r).symm
    rw [e]
    refine (DFunLike.congr_fun hv _).trans ?_
    change -Real.logb p ‖g (algebraMap R S r)‖ = _
    rw [IsLocalization.lift_eq]
  refine ⟨⟨fun x => v (Additive.ofMul x), fun x y => map_add v _ _, fun u => ?_⟩, key⟩
  have h1 : ‖f u‖ = 1 := by
    have h1 : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul]; simp
    have h2 := hle (u⁻¹ : Rˣ)
    have h3 := hle u
    nlinarith [norm_nonneg (f u), norm_nonneg (f (u⁻¹ : Rˣ))]
  have e : Units.map (algebraMap R (FractionRing R)).toMonoidHom u = toUnitK u.val u.ne_zero := Units.ext rfl
  rw [e, key _ _ (u.isUnit.map f).ne_zero, h1, Real.logb_one, neg_zero]

variable {φ : FractionRing R →+* C}

theorem vPsiAt_eq_mul (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) {D : DegPre R} {χ : D.X}
    (hI : D.PsiIn χ ⊤) :
    vPsiAt D (φ.comp (algebraMap R (FractionRing R))) p χ = psiOrdAt_vp hφ hp D χ * -Real.logb p ‖(p : C)‖ := by
  have h := (exists_psiCoord_iff D χ).2 hI
  have h0 := PsiCoordLocal.ne_zero_of_coord h.choose_spec
  rw [vPsiAt, dif_pos h, psiOrdAt_vp, psiVal_eq _ (isPsiCoord_toUnitK h.choose_spec h0)]
  change -Real.logb p ‖φ (algebraMap R _ h.choose)‖ = Real.log ‖φ (algebraMap R _ h.choose)‖ / _ * _
  have := (hφ.log_norm_p_neg hp).2.ne
  simp only [Real.logb]
  field_simp

theorem betaAt_eq_mul (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) {D : DegPre R} {a b : D.X}
    (ha : D.PsiIn a ⊤) (hb : D.PsiIn b ⊤) (hab : D.PsiIn (a + b) ⊤) :
    betaAt D (φ.comp (algebraMap R (FractionRing R))) p a b =
      periodFormAt_vp hφ hp D a b * -Real.logb p ‖(p : C)‖ := by
  rw [betaAt, vPsiAt_eq_mul hφ hp ha, vPsiAt_eq_mul hφ hp hb, vPsiAt_eq_mul hφ hp hab]
  simp only [periodFormAt_vp, periodForm, psiOrdAt_vp]
  ring

theorem neg_logb_eq_one {p : ℕ} (hp : p.Prime) (hn : ‖(p : C)‖ = (p : ℝ)⁻¹) : -Real.logb p ‖(p : C)‖ = 1 := by
  rw [hn, Real.logb_inv, neg_neg, Real.logb_self_eq_one (by exact_mod_cast hp.one_lt)]

theorem exists_isCentred_iff (f : R →+* C) :
    (∃ φ : FractionRing R →+* C, IsCentred φ ∧ φ.comp (algebraMap R (FractionRing R)) = f) ↔
      Function.Injective f ∧ (∀ r, ‖f r‖ ≤ 1) ∧ ∀ r ∈ maximalIdeal R, ‖f r‖ < 1 := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ.injective.comp (IsFractionRing.injective R _), hφ.le_one, hφ.lt_one⟩
  · rintro ⟨hi, h1, h2⟩
    refine ⟨IsFractionRing.lift hi, ⟨fun r => ?_, fun r hr => ?_⟩, RingHom.ext fun r => ?_⟩
    · rw [IsFractionRing.lift_algebraMap]; exact h1 r
    · rw [IsFractionRing.lift_algebraMap]; exact h2 r hr
    · exact IsFractionRing.lift_algebraMap hi r

end At

theorem main :
    (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R),
      PsiCoord D χ r ↔ ∃ x, IsPsiCoord D χ x ∧ x.val = algebraMap R (FractionRing R) r) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (χ : D.toPre.X),
      ordPsi D.toPre χ = psiOrd D χ ∧ (∃ r, PsiCoord D.toPre χ r) ∧
      ∀ x, IsPsiCoord D.toPre χ x ↔ ∃ r, PsiCoord D.toPre χ r ∧ x.val = algebraMap R (FractionRing R) r) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
      (∀ (D : DegPre R) (χ : D.X), ordPsi D χ = ((psiOrd_vw D χ).toNat : ℕ∞) ∧
        (((ordPsi D χ).toNat : ℤ) = psiOrd_vw D χ ↔ D.PsiIn χ ⊤)) ∧
      (∀ (p : ℕ) (hp : IsOverPrime R p), ∃ e : ℕ, ordNat R p = e ∧ ramIdx hp = e) ∧
      ∀ (D : DegData R (maximalIdeal R)),
        (∀ χ, ∃ n : ℕ, ordPsi D.toPre χ = n ∧ psiOrd_vw D.toPre χ = n) ∧
        (∀ a b, betaZ D.toPre a b = periodForm_vw D.toPre a b) ∧
        ∀ (p : ℕ) (hp : IsOverPrime R p) (a b : D.toPre.X),
          betaP D.toPre p a b = (periodForm_vp hp D.toPre a b : ℝ)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [NormedField C],
      (∀ f : R →+* C, (∃ φ : FractionRing R →+* C, IsCentred φ ∧ φ.comp (algebraMap R (FractionRing R)) = f) ↔
        Function.Injective f ∧ (∀ r, ‖f r‖ ≤ 1) ∧ ∀ r ∈ maximalIdeal R, ‖f r‖ < 1) ∧
      ∀ (φ : FractionRing R →+* C) (hφ : IsCentred φ) (p : ℕ) (hp : IsOverPrime R p)
        (D : DegData R (maximalIdeal R)),
        (∀ χ, vPsiAt D.toPre (φ.comp (algebraMap R (FractionRing R))) p χ =
          psiOrdAt_vp hφ hp D.toPre χ * -Real.logb p ‖(p : C)‖) ∧
        (∀ a b, betaAt D.toPre (φ.comp (algebraMap R (FractionRing R))) p a b =
          periodFormAt_vp hφ hp D.toPre a b * -Real.logb p ‖(p : C)‖) ∧
        (‖(p : C)‖ = (p : ℝ)⁻¹ →
          (∀ χ, vPsiAt D.toPre (φ.comp (algebraMap R (FractionRing R))) p χ = psiOrdAt_vp hφ hp D.toPre χ) ∧
          ∀ a b, betaAt D.toPre (φ.comp (algebraMap R (FractionRing R))) p a b =
            periodFormAt_vp hφ hp D.toPre a b)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [NormedField C] (f : R →+* C) (p : ℕ),
      ((∀ r, ‖f r‖ ≤ 1) → ∃ v : LatticeVal R ℝ, ReadsAt v f p) ∧
      ∀ v : LatticeVal R ℝ, ReadsAt v f p → ∀ D : DegPre R,
        (∀ χ, (∃ r, PsiCoord D χ r ∧ f r ≠ 0) → vPsiAt D f p χ = psiVal v D χ) ∧
        ((∀ χ, ∃ r, PsiCoord D χ r ∧ f r ≠ 0) → ∀ a b, betaAt D f p a b = periodForm v D a b)) := by
  refine ⟨fun R _ _ => psiCoord_iff, fun R _ _ _ D χ => ⟨rfl, (exists_psiCoord_iff _ χ).2 (psiIn_top D χ), fun x =>
      ⟨exists_psiCoord_of_isPsiCoord (psiIn_top D χ), fun ⟨r, hr, e⟩ => ?_⟩⟩,
    fun R _ _ _ => ⟨fun D χ => ⟨ordPsi_eq_toNat D χ, ordPsi_toNat_eq_iff D χ⟩, fun p hp => ordNat_eq hp, fun D =>
      ⟨fun χ => exists_ordPsi (psiIn_top D χ), fun a b => betaZ_eq (psiIn_top D _) (psiIn_top D _) (psiIn_top D _),
        fun p hp a b => betaP_eq hp (psiIn_top D _) (psiIn_top D _) (psiIn_top D _)⟩⟩,
    fun R _ _ _ C _ => ⟨exists_isCentred_iff, fun φ hφ p hp D => ?_⟩,
    fun R _ _ _ C _ f p => ⟨fun h => exists_readsAt f h p, fun v hv D =>
      ⟨fun χ => vPsiAt_eq_psiVal hv, fun h a b => betaAt_eq_periodForm hv (h _) (h _) (h _)⟩⟩⟩
  · obtain ⟨y, hy, e'⟩ := (psiCoord_iff _ χ r).1 hr
    have : x = y := Units.ext (e.trans e'.symm)
    exact this ▸ hy
  · have h1 := fun χ => vPsiAt_eq_mul hφ hp (psiIn_top D χ)
    have h2 := fun a b => betaAt_eq_mul hφ hp (psiIn_top D a) (psiIn_top D b) (psiIn_top D (a + b))
    exact ⟨h1, h2, fun hn => ⟨fun χ => by rw [h1, neg_logb_eq_one hp.prime hn, mul_one],
      fun a b => by rw [h2, neg_logb_eq_one hp.prime hn, mul_one]⟩⟩

end GlobalTheory.PeriodFormCompare
