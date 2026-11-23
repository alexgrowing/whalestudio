import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Algebra

variable (R : Type) [CommRing R] [IsDomain R]

abbrev intUnits : Subgroup (FractionRing R)ˣ := (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

abbrev Cls : Type := (FractionRing R)ˣ ⧸ intUnits R

variable {R}

def toK (r : R) (h : r ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R _ r) ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h)

theorem cls_eq_iff {x y : (FractionRing R)ˣ} : (x : Cls R) = y ↔
    ∃ u : Rˣ, (x : FractionRing R) * algebraMap R _ (u : R) = y := by
  rw [show ((x : Cls R) = y) ↔ QuotientGroup.mk' (intUnits R) x = QuotientGroup.mk' (intUnits R) y from Iff.rfl,
    QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h⟩
    exact ⟨u, congrArg Units.val h⟩
  · rintro ⟨u, h⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext h⟩

theorem cls_pow_eq_one [IsIntegrallyClosed R] {n : ℕ} (hn : n ≠ 0) (c : Cls R) (h : c ^ n = 1) : c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have h' : x ^ n ∈ intUnits R := (QuotientGroup.eq_one_iff _).1 ((QuotientGroup.mk_pow _ _ _).trans h)
  obtain ⟨u, hu⟩ := h'
  have key : ∀ (y : (FractionRing R)ˣ) (v : Rˣ), Units.map (algebraMap R (FractionRing R)).toMonoidHom v = y ^ n →
      ∃ a : R, algebraMap R _ a = (y : FractionRing R) := fun y v hv => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_)
    have := congrArg Units.val hv
    rw [Units.val_pow_eq_pow_val] at this
    rw [← this]
    exact isIntegral_algebraMap
  obtain ⟨a, ha⟩ := key x u hu
  obtain ⟨b, hb⟩ := key x⁻¹ u⁻¹ (by rw [map_inv, hu, inv_pow])
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact (QuotientGroup.eq_one_iff _).2 ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

instance [IsIntegrallyClosed R] : IsMulTorsionFree (Cls R) where
  pow_left_injective n hn a b h := by
    have : (a * b⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, show a ^ n = b ^ n from h, mul_inv_cancel]
    exact mul_inv_eq_one.1 (cls_pow_eq_one hn _ this)

theorem exists_lift [IsIntegrallyClosed R] {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (b : X → X → Cls R)
    (h₁ : ∀ a a' c, b (a + a') c = b a c * b a' c) (h₂ : ∀ a c, b a c = b c a) :
    ∃ t : X → X → (FractionRing R)ˣ, (∀ a c, (t a c : Cls R) = b a c) ∧ (∀ a a' c, t (a + a') c = t a c * t a' c) ∧
      ∀ a c a' c', b a c = b a' c' → t a c = t a' c' := by
  let B₀ : X →+ X →+ Additive (Cls R) := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun c => Additive.ofMul (b a c))
    (fun c c' => by rw [h₂, h₁, h₂ c, h₂ c']; rfl)) (fun a a' => AddMonoidHom.ext fun c => by
      show Additive.ofMul (b (a + a') c) = Additive.ofMul (b a c) + Additive.ofMul (b a' c)
      rw [h₁]; rfl)
  let B : TensorProduct ℤ X X →ₗ[ℤ] Additive (Cls R) := TensorProduct.lift
    ((AddMonoidHom.toIntLinearMap ((addMonoidHomLequivInt ℤ).toAddEquiv.toAddMonoidHom.comp B₀)))
  have hB : ∀ a c, B (a ⊗ₜ c) = Additive.ofMul (b a c) := fun a c => rfl
  let q : Additive (FractionRing R)ˣ →ₗ[ℤ] Additive (Cls R) :=
    (MonoidHom.toAdditive (QuotientGroup.mk' (intUnits R))).toIntLinearMap
  have hq : Function.Surjective q := fun c => QuotientGroup.mk_surjective (Additive.toMul c)
  have : Module.Finite ℤ (TensorProduct ℤ X X) := Module.Finite.tensorProduct ℤ X X
  have : Module.Finite ℤ (LinearMap.range B) := Module.Finite.range B
  have : Module.Free ℤ (LinearMap.range B) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q (LinearMap.range B).subtype hq
  refine ⟨fun a c => Additive.toMul (s (B.rangeRestrict (a ⊗ₜ c))), fun a c => ?_, fun a a' c => ?_, fun a c a' c' h => ?_⟩
  · exact congrArg Additive.toMul (LinearMap.congr_fun hs (B.rangeRestrict (a ⊗ₜ c)))
  · beta_reduce
    rw [TensorProduct.add_tmul, map_add, map_add]; rfl
  · have : B.rangeRestrict (a ⊗ₜ c) = B.rangeRestrict (a' ⊗ₜ c') := Subtype.ext (by
      show B _ = B _
      rw [hB, hB, h])
    simp only [this]

end Algebra

section Coord

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

open GlobalTheory.BetaAdd in

theorem coord_rel (Dg : DegData R (maximalIdeal R)) (r : Dg.toPre.X → R) (hr : ∀ χ, PsiCoord Dg.toPre χ (r χ)) :
    (∀ a a' b, ∃ u : Rˣ, r (a + a' + b) * r a * r a' * r b * u = r (a + b) * r (a' + b) * r (a + a')) ∧
      ∀ a, ∃ u : Rˣ, r (-a) * u = r a := by
  set D := Dg.toPre with hD
  let z : (TK R).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ, hI⟩ := exists_good_int D z
  choose u hu hur using fun χ => coord_val hI hJ (hr χ)
  let Q := QuotientGroup.mk' (intU z)
  have hQ : ∀ w ∈ intU z, Q w = 1 := fun w hw => (QuotientGroup.eq_one_iff w).2 hw
  let P : D.X → _ := fun χ => Q (val (D.psi χ) (𝟙 _) z J)
  have hP : ∀ χ, Q (u χ * val (D.psi χ) (𝟙 _) z J) = P χ := fun χ => by rw [map_mul, hQ _ (hu χ), _root_.one_mul]
  have fin : ∀ {x y : R} {X Y : ((TK R).left.presheaf.stalk z)ˣ}, toGen z x = X.val → toGen z y = Y.val →
      Q X = Q Y → ∃ v : Rˣ, x * v = y := fun {x y X Y} hX hY h => by
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (QuotientGroup.mk'_eq_mk' (intU z)).1 h
    exact ⟨v, toGen_injective z (by rw [map_mul, hX, hY, ← hv]; rfl)⟩
  have vρ : Q (val D.rigK (𝟙 _) z J) = 1 := by
    refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.rig (𝟙 _) (fun _ => ?_) _ ?_))
    · rw [Category.id_comp]; exact Over.w η[D.P.A]
    · rw [Category.id_comp, Category.comp_id]; rfl
  have vτ : ∀ a b : D.X, Q (val (D.tau a b) (𝟙 _) z J) = P (a + b) * (P a)⁻¹ * (P b)⁻¹ := fun a b => by
    refine (congrArg Q ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _)))).trans ?_
    simp only [map_mul, map_inv]
    erw [vρ]
    rw [inv_one, _root_.mul_one]
  refine ⟨fun a a' b => ?_, fun a => ?_⟩
  · have e := congrArg Q ((val_mul hJ _ _ _).symm.trans ((val_corr hJ (Dg.tau_bimult a a' b) (𝟙 _)).trans
      (val_mul hJ _ _ _)))
    have vc : Q (val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.cub.t
        (lift (D.c a) (lift (D.c a') (D.c b))).left (fun _ => over_sec _ _) _ ?_))
      simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
    rw [map_mul, map_mul, vc, vτ, vτ, vτ] at e
    refine fin
      (X := u (a + a' + b) * val (D.psi (a + a' + b)) (𝟙 _) z J * (u a * val (D.psi a) (𝟙 _) z J) *
        (u a' * val (D.psi a') (𝟙 _) z J) * (u b * val (D.psi b) (𝟙 _) z J))
      (Y := u (a + b) * val (D.psi (a + b)) (𝟙 _) z J * (u (a' + b) * val (D.psi (a' + b)) (𝟙 _) z J) *
        (u (a + a') * val (D.psi (a + a')) (𝟙 _) z J)) ?_ ?_ ?_
    · simp only [map_mul, hur, Units.val_mul]
    · simp only [map_mul, hur, Units.val_mul]
    · rw [map_mul Q, map_mul Q, map_mul Q, hP, hP, hP, hP, map_mul Q, map_mul Q, hP, hP, hP]
      have E := congrArg Additive.ofMul e
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at E ⊢
      rw [← sub_eq_zero] at E ⊢
      refine Eq.trans ?_ E
      abel
  · have e := congrArg Q ((val_mul hJ _ _ _).symm.trans (val_corr hJ (Dg.psi_even a) (𝟙 _)))
    have vs : Q (val (LB.pullGen D.P.L _ _ D.sym (D.xK a)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.sym (D.c a).left (fun k => ?_) _ ?_))
      · fin_cases k
        · exact over_sec _ _
        · exact over_sec (D.c a) (𝟙 _)
      · simp [ptK]
    rw [map_mul, vs, _root_.mul_one] at e
    exact fin (hur (-a)) (hur a) ((hP _).trans (e.trans (hP _).symm))

variable (Dg : DegData R (maximalIdeal R))

def coord (χ : Dg.toPre.X) : R := (GlobalTheory.BetaAdd.exists_coord Dg χ).choose

theorem coord_spec (χ : Dg.toPre.X) : PsiCoord Dg.toPre χ (coord Dg χ) := (GlobalTheory.BetaAdd.exists_coord Dg χ).choose_spec

theorem coord_ne (χ : Dg.toPre.X) : coord Dg χ ≠ 0 := GlobalTheory.PsiCoordLocal.ne_zero_of_coord (coord_spec Dg χ)

def psiCls (χ : Dg.toPre.X) : Cls R := (toK (coord Dg χ) (coord_ne Dg χ) : (FractionRing R)ˣ)

def tauCls (a b : Dg.toPre.X) : Cls R := psiCls Dg (a + b) * (psiCls Dg a)⁻¹ * (psiCls Dg b)⁻¹

omit [IsLocalRing R] in
theorem toK_cls_eq {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (h : ∃ u : Rˣ, x * u = y) : (toK x hx : Cls R) = toK y hy := by
  obtain ⟨u, rfl⟩ := h
  exact cls_eq_iff.2 ⟨u, (map_mul _ _ _).symm⟩

omit [IsLocalRing R] in
theorem toK_mul {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) : toK (x * y) (mul_ne_zero hx hy) = toK x hx * toK y hy :=
  Units.ext (map_mul _ _ _)

theorem psiCls_eq {χ : Dg.toPre.X} {r : R} (hr : PsiCoord Dg.toPre χ r) :
    psiCls Dg χ = toK r (GlobalTheory.PsiCoordLocal.ne_zero_of_coord hr) := by
  obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord (coord_spec Dg χ) hr
  exact toK_cls_eq _ _ ⟨u, by rw [hu, mul_comm]⟩

theorem tauCls_symm (a b : Dg.toPre.X) : tauCls Dg a b = tauCls Dg b a := by
  rw [tauCls, tauCls, add_comm a b, mul_right_comm]

theorem tauCls_add (a a' b : Dg.toPre.X) : tauCls Dg (a + a') b = tauCls Dg a b * tauCls Dg a' b := by
  have n := coord_ne Dg
  have h := toK_cls_eq (mul_ne_zero (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) (n _))
    (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) ((coord_rel Dg _ (coord_spec Dg)).1 a a' b)
  rw [toK_mul (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _),
    toK_mul (n _) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _), toK_mul (n _) (n _)] at h
  have h' : psiCls Dg (a + a' + b) * psiCls Dg a * psiCls Dg a' * psiCls Dg b =
    psiCls Dg (a + b) * psiCls Dg (a' + b) * psiCls Dg (a + a') := h
  have E := congrArg Additive.ofMul h'
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv] at E ⊢
  rw [← sub_eq_zero] at E ⊢
  refine Eq.trans ?_ E
  abel

theorem psiCls_neg (a : Dg.toPre.X) : psiCls Dg (-a) = psiCls Dg a :=
  toK_cls_eq _ _ ((coord_rel Dg _ (coord_spec Dg)).2 a)

theorem tauCls_self (a : Dg.toPre.X) : tauCls Dg a a = psiCls Dg a ^ 2 := by
  have h0 := congrArg Additive.ofMul (tauCls_add Dg 0 0 0)
  have h1 := congrArg Additive.ofMul (tauCls_add Dg a (-a) a)
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv, add_zero, zero_add, add_neg_cancel, neg_add_cancel, psiCls_neg, ofMul_pow] at h0 h1 ⊢
  rw [← sub_eq_zero] at h0 h1 ⊢
  have : ∀ {x y z : Additive (Cls R)}, x = 0 → y = 0 → z = -y - x - x → z = 0 := fun hx hy hz => by rw [hz, hx, hy]; simp
  refine this h0 h1 ?_
  rw [two_nsmul]
  abel

theorem tauCls_bal {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] (ρ : Dg.toPre.OAct O) (x : O) (a b : Dg.toPre.X) :
    tauCls Dg (x • a) b = tauCls Dg a (star x • b) := by
  have n := coord_ne Dg
  have s := coord_spec Dg
  obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance Dg.toPre ρ x a b (s _) (s _) (s _) (s _) (s _) (s _)
  have h := toK_cls_eq (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _))
    (mul_ne_zero (mul_ne_zero (n _) (n _)) (n _)) ⟨u, (mul_comm _ _).trans hu⟩
  rw [toK_mul (mul_ne_zero (n _) (n _)) (n _), toK_mul (n _) (n _), toK_mul (mul_ne_zero (n _) (n _)) (n _),
    toK_mul (n _) (n _)] at h
  have h' : psiCls Dg (x • a + b) * psiCls Dg a * psiCls Dg (star x • b) =
    psiCls Dg (a + star x • b) * psiCls Dg (x • a) * psiCls Dg b := h
  have E := congrArg Additive.ofMul h'
  apply Additive.ofMul.injective
  simp only [tauCls, ofMul_mul, ofMul_inv] at E ⊢
  rw [← sub_eq_zero] at E ⊢
  refine Eq.trans ?_ E
  abel

theorem tauCls_half [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] (ρ : Dg.toPre.OAct O)
    {w : O} (hw : w + star w = 1) (a : Dg.toPre.X) : tauCls Dg a (w • a) = psiCls Dg a := by
  refine pow_left_injective (n := 2) two_ne_zero ?_
  show _ ^ 2 = _ ^ 2
  rw [← tauCls_self, sq]
  nth_rewrite 2 [tauCls_symm]
  rw [tauCls_bal Dg ρ, tauCls_symm Dg a, tauCls_symm Dg a, ← tauCls_add, ← add_smul, hw, one_smul]

structure IsReading (O : Type) [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (t : Dg.toPre.X → Dg.toPre.X → (FractionRing R)ˣ) : Prop where
  add_left : ∀ a a' b, t (a + a') b = t a b * t a' b
  symm : ∀ a b, t a b = t b a
  bal : ∀ (x : O) a b, t (x • a) b = t a (star x • b)
  coord : ∀ a b ra rb rab, PsiCoord Dg.toPre a ra → PsiCoord Dg.toPre b rb → PsiCoord Dg.toPre (a + b) rab →
    ∃ u : Rˣ, (t a b : FractionRing R) * algebraMap R _ (ra * rb * u) = algebraMap R _ rab

theorem exists_reading [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (ρ : Dg.toPre.OAct O) : ∃ t, IsReading Dg O t := by
  obtain ⟨t, h₀, h₁, h₂⟩ := exists_lift (tauCls Dg) (tauCls_add Dg) (tauCls_symm Dg)
  refine ⟨t, h₁, fun a b => h₂ _ _ _ _ (tauCls_symm Dg a b), fun x a b => h₂ _ _ _ _ (tauCls_bal Dg ρ x a b),
    fun a b ra rb rab ha hb hab => ?_⟩
  have h := h₀ a b
  rw [tauCls, psiCls_eq Dg ha, psiCls_eq Dg hb, psiCls_eq Dg hab, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq] at h
  obtain ⟨u, hu⟩ := cls_eq_iff.1 (show ((t a b * toK rb _ * toK ra _ : (FractionRing R)ˣ) : Cls R) = toK rab _ from h)
  refine ⟨u, Eq.trans ?_ hu⟩
  simp only [map_mul, Units.val_mul, toK, Units.val_mk0]
  ring

variable {Dg}

theorem IsReading.cls {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t} (h : IsReading Dg O t) (a b : Dg.toPre.X) :
    (t a b : Cls R) = tauCls Dg a b := by
  obtain ⟨u, hu⟩ := h.coord a b _ _ _ (coord_spec Dg _) (coord_spec Dg _) (coord_spec Dg _)
  rw [tauCls, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq]
  refine (cls_eq_iff (x := t a b * toK _ (coord_ne Dg b) * toK _ (coord_ne Dg a)) (y := toK _ (coord_ne Dg (a + b)))).2 ⟨u, Eq.trans ?_ hu⟩
  simp only [map_mul, Units.val_mul, toK, Units.val_mk0]
  ring

omit [IsLocalRing R] in
theorem mem_range_of_cls {x : (FractionRing R)ˣ} {r : R} (hr : r ≠ 0) (h : (x : Cls R) = toK r hr) :
    (x : FractionRing R) ∈ (algebraMap R (FractionRing R)).range := by
  obtain ⟨u, hu⟩ := cls_eq_iff.1 h.symm
  exact ⟨r * u, (map_mul _ _ _).trans hu⟩

theorem IsReading.pos {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t} (h : IsReading Dg O t) (a : Dg.toPre.X) :
    (t a a : FractionRing R) ∈ (algebraMap R (FractionRing R)).range :=
  mem_range_of_cls (mul_ne_zero (coord_ne Dg a) (coord_ne Dg a)) (by
    rw [h.cls, tauCls_self, toK_mul (coord_ne Dg a) (coord_ne Dg a), sq]; rfl)

theorem IsReading.pos_max [CharZero R] [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X] {t}
    (h : IsReading Dg O t) {a : Dg.toPre.X} (ha : a ≠ 0) :
    ∃ r ∈ maximalIdeal R, algebraMap R (FractionRing R) r = t a a := by
  obtain ⟨r, hr, h0, hm, -⟩ := (GlobalTheory.PsiCoordLocal.main R Dg inferInstance a).1
  have e : (t a a : Cls R) = toK (r * r) (mul_ne_zero h0 h0) := by
    rw [h.cls, tauCls_self, psiCls_eq Dg hr, toK_mul h0 h0, sq]; rfl
  obtain ⟨u, hu⟩ := cls_eq_iff.1 e.symm
  exact ⟨r * r * u, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hm ha)), (map_mul _ _ _).trans hu⟩

end Coord

end GlobalTheory.LocM.Bdy
