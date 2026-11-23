import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BetaAdd

variable {R : Type} [CommRing R] [IsDomain R]

def toGen (z : (TK R).left) : R →+* (TK R).left.presheaf.stalk z :=
  ((TK R).left.presheaf.germ (jK R ⁻¹ᵁ ⊤) z trivial).hom.comp (((jK R).app ⊤).hom.comp (DegPre.toOpen (R := R) ⊤))

omit [IsDomain R] in
theorem toOpen_top (r : R) : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
  simp only [DegPre.toOpen, RingHom.coe_comp, Function.comp_apply]
  have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

omit [IsDomain R] in
theorem toOpen_bij : Function.Bijective (DegPre.toOpen (R := R) ⊤) := by
  have : ⇑(DegPre.toOpen (R := R) ⊤) = ⇑(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := funext toOpen_top
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

theorem toGen_injective (z : (TK R).left) : Function.Injective (toGen z) := by
  have : IsIntegral (TK R).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (FractionRing R))))
  intro a b h
  have h1 := germ_injective_of_isIntegral (TK R).left (U := jK R ⁻¹ᵁ ⊤) z trivial h
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [RingHom.comp_apply, toOpen_top] at h1
  exact IsFractionRing.injective R (FractionRing R) (hi ((e a).trans (h1.trans (e b).symm)))

theorem toGen_eq (z : (TK R).left) (r : R) : toGen z r = gs (jK R) z ⊤ (DegPre.toOpen (R := R) ⊤ r) :=
  (gs_eq (jK R) z ⊤ trivial _).symm

abbrev intU (z : (TK R).left) : Subgroup ((TK R).left.presheaf.stalk z)ˣ :=
  (Units.map (toGen z).toMonoidHom).range

theorem gm_mem (z : (TK R).left) {X : Scheme.{0}} (x : Spec (CommRingCat.of R) ⟶ X) (U : X.Opens)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : gm (jK R ≫ x) z U a ∈ intU z := by
  let e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) := RingEquiv.ofBijective _ toOpen_bij
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (res hU (pullU x U a)), Units.ext ?_⟩
  show toGen z (e.symm (res hU (pullU x U a)).val) = _
  rw [toGen_eq, show DegPre.toOpen (R := R) ⊤ (e.symm (res hU (pullU x U a)).val) = (res hU (pullU x U a)).val from
    e.apply_symm_apply _, gs_unit (jK R) z ⊤ trivial, gm_res (jK R) z hU trivial,
    gm_pull (jK R) x z U (hU trivial)]

theorem exists_good_int [IsLocalRing R] (D : DegPre R) (z : (TK R).left) :
    ∃ J, Good D.P.L z J ∧ ∀ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ →
      ⊤ ≤ x ⁻¹ᵁ D.P.L.U (J (jK R ≫ x)) := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun x : Spec (CommRingCat.of R) ⟶ D.P.A.left => exists_chart D.P.isLB (x (closedPoint R))
  have htop : ∀ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, ⊤ ≤ x ⁻¹ᵁ D.P.L.U (pick x) := fun x =>
    (DVR.eq_top_of_closedPoint_mem _ (hpk x)).ge
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z
    (K := {x : Spec (CommRingCat.of R) ⟶ D.P.A.left // x ≫ D.P.A.hom = 𝟙 _}) (fun x => jK R ≫ x.1) (fun x => pick x.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated D.P.A.hom (a.2.trans b.2.symm) (jK R) h))
    (fun x => htop x.1 (show jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial))
  exact ⟨J, hJ, fun x hx => (eJ ⟨x, hx⟩).symm ▸ htop x⟩

section
variable {D : DegPre R} {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
  (hI : ∀ x : Spec (CommRingCat.of R) ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ D.P.L.U (J (jK R ≫ x)))
include hI

theorem val_mem {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (p : Spec (CommRingCat.of R) ⟶ Y)
    (hp : ∀ k, (p ≫ φ k) ≫ D.P.A.hom = 𝟙 _) (q : (TK R).left ⟶ Y) (hq : q = jK R ≫ p) : val t q z J ∈ intU z := by
  subst hq
  refine gm_mem z p _ (fun y _ => Set.mem_iInter.2 fun k => ?_) _
  have := hI _ (hp k) (show y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  rw [← Category.assoc] at this
  exact this

theorem coord_val (hJ : Good D.P.L z J) {χ : D.X} {r : R} (hr : PsiCoord D χ r) :
    ∃ u ∈ intU z, toGen z r = (u * val (D.psi χ) (𝟙 _) z J).val := by
  obtain ⟨j, hj, h, e⟩ := hr
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by simp [ptK]
  have hz : (𝟙 (TK R).left : _ ⟶ _) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := h trivial
  have hz' := hJ.mem (K := PUnit) (fun _ => D.xK χ) (𝟙 _)
  have tr := gen_trans (D.psi_gen χ) (𝟙 _) z hz hz'
  refine ⟨trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) (𝟙 _) z j (fun _ => J (𝟙 _ ≫ D.xK χ)),
    Subgroup.prod_mem _ fun k _ => Subgroup.zpow_mem _ ?_ _, ?_⟩
  · have e1 : 𝟙 _ ≫ D.xK χ = jK R ≫ (D.c χ).left := (Category.id_comp _).trans hx
    have h2 := hI (D.c χ).left (Over.w _)
    rw [e1]
    exact gm_mem z (D.c χ).left (D.P.L.U (j k) ⊓ D.P.L.U (J (jK R ≫ (D.c χ).left))) (fun y hy => ⟨hj hy, h2 hy⟩) _
  · refine Eq.trans ?_ (congrArg Units.val tr)
    refine Eq.trans ?_ ((gs_res (𝟙 _) z h trivial _).trans (gs_unit _ _ _ hz _))
    refine Eq.trans ?_ (congrArg (gs (𝟙 _) z _) e)
    exact (gs_eq (𝟙 (TK R).left) z (jK R ⁻¹ᵁ ⊤) trivial _).symm

end

theorem exists_coord [IsLocalRing R] (Dg : DegData R (maximalIdeal R)) (χ : Dg.toPre.X) :
    ∃ r, PsiCoord Dg.toPre χ r := by
  have hin : Dg.toPre.PsiIn χ ⊤ := by
    by_cases h : χ = 0
    · subst h; exact (GlobalTheory.PsiZero.main R Dg.toPre).1 Dg.tau_bimult
    · exact (GlobalTheory.PsiZero.main R Dg.toPre).2 χ _ _ le_top (Dg.psi_pos χ h)
  obtain ⟨i, hi⟩ := exists_chart Dg.toPre.P.isLB ((Dg.toPre.c χ).left (closedPoint R))
  have htop : ⊤ ≤ (Dg.toPre.c χ).left ⁻¹ᵁ Dg.toPre.P.L.U i := (DVR.eq_top_of_closedPoint_mem _ hi).ge
  have hx : Dg.toPre.xK χ = jK R ≫ (Dg.toPre.c χ).left := by simp [ptK]
  have h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb Dg.toPre.P.L (K := PUnit) (fun _ => Dg.toPre.xK χ) (fun _ => -1)).U (fun _ => i) :=
    fun y _ => Set.mem_iInter.2 fun _ => by
      rw [hx]; exact htop (show jK R y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)
  obtain ⟨s, -, hs⟩ := hin (fun _ => i) ⊤ (isAffineOpen_top _) htop h
  obtain ⟨r, rfl⟩ := toOpen_bij.2 s
  exact ⟨r, fun _ => i, htop, h, hs⟩

theorem norm_unit {C : Type} [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) : ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, u.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := _root_.mul_one _

theorem norm_eq {C : Type} [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (z : (TK R).left) {x y : R}
    {X Y : ((TK R).left.presheaf.stalk z)ˣ} (hX : toGen z x = X.val) (hY : toGen z y = Y.val)
    (h : QuotientGroup.mk' (intU z) X = QuotientGroup.mk' (intU z) Y) : ‖f x‖ = ‖f y‖ := by
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (QuotientGroup.mk'_eq_mk' (intU z)).1 h
  have : x * u = y := toGen_injective z (by rw [map_mul, hX, hY, ← hu]; rfl)
  rw [← this, map_mul, norm_mul, norm_unit f hf, _root_.mul_one]

theorem over_sec {Y B : Over (Spec (CommRingCat.of R))} (q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Y) (g : Y ⟶ B) :
    (q.left ≫ g.left) ≫ B.hom = 𝟙 _ := by
  rw [Category.assoc, Over.w g, Over.w q]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)) (C : Type) [NormedField C] [IsUltrametricDist C] (f : R →+* C) (p : ℕ), IsIntegrallyClosed R → (∀ a, ‖f a‖ ≤ 1) → (∀ χ r, PsiCoord Dg.toPre χ r → f r ≠ 0) → (∀ a a' b, betaAt Dg.toPre f p (a + a') b = betaAt Dg.toPre f p a b + betaAt Dg.toPre f p a' b) ∧ ∀ a, betaAt Dg.toPre f p a a = 2 * vPsiAt Dg.toPre f p a := by
  intro R _ _ _ _ Dg C _ _ f p _ hf hne
  set D := Dg.toPre with hD
  let z : (TK R).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ, hI⟩ := exists_good_int D z
  have hex := exists_coord Dg
  let r : D.X → R := fun χ => (hex χ).choose
  have hr : ∀ χ, PsiCoord D χ (r χ) := fun χ => (hex χ).choose_spec
  have hv : ∀ χ, vPsiAt D f p χ = -Real.logb p ‖f (r χ)‖ := fun χ => dif_pos (hex χ)
  have hn : ∀ χ, ‖f (r χ)‖ ≠ 0 := fun χ => norm_ne_zero_iff.2 (hne χ _ (hr χ))
  choose u hu hur using fun χ => coord_val hI hJ (hr χ)
  let Q := QuotientGroup.mk' (intU z)
  have hQ : ∀ w ∈ intU z, Q w = 1 := fun w hw => (QuotientGroup.eq_one_iff w).2 hw
  let P : D.X → _ := fun χ => Q (val (D.psi χ) (𝟙 _) z J)
  have hP : ∀ χ, Q (u χ * val (D.psi χ) (𝟙 _) z J) = P χ := fun χ => by rw [map_mul, hQ _ (hu χ), _root_.one_mul]
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
  have hadd : ∀ a a' b, betaAt D f p (a + a') b = betaAt D f p a b + betaAt D f p a' b := by
    intro a a' b
    have e := congrArg Q ((val_mul hJ _ _ _).symm.trans ((val_corr hJ (Dg.tau_bimult a a' b) (𝟙 _)).trans
      (val_mul hJ _ _ _)))
    have vc : Q (val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.cub.t
        (lift (D.c a) (lift (D.c a') (D.c b))).left (fun _ => over_sec _ _) _ ?_))
      simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]
    rw [map_mul, map_mul, vc, vτ, vτ, vτ] at e
    have key : ‖f (r (a + a' + b) * r a * r a' * r b)‖ = ‖f (r (a + b) * r (a' + b) * r (a + a'))‖ := by
      refine norm_eq f hf z
        (X := u (a + a' + b) * val (D.psi (a + a' + b)) (𝟙 _) z J * (u a * val (D.psi a) (𝟙 _) z J) *
          (u a' * val (D.psi a') (𝟙 _) z J) * (u b * val (D.psi b) (𝟙 _) z J))
        (Y := u (a + b) * val (D.psi (a + b)) (𝟙 _) z J * (u (a' + b) * val (D.psi (a' + b)) (𝟙 _) z J) *
          (u (a + a') * val (D.psi (a + a')) (𝟙 _) z J)) ?_ ?_ ?_
      · simp only [map_mul, hur, Units.val_mul]
      · simp only [map_mul, hur, Units.val_mul]
      · show Q _ = Q _
        rw [map_mul Q, map_mul Q, map_mul Q, hP, hP, hP, hP, map_mul Q, map_mul Q, hP, hP, hP]
        have E := congrArg Additive.ofMul e
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one] at E ⊢
        rw [← sub_eq_zero] at E ⊢
        refine Eq.trans ?_ E
        abel
    have k2 := congrArg (Real.logb p) key
    simp only [map_mul, norm_mul] at k2
    rw [Real.logb_mul (mul_ne_zero (mul_ne_zero (hn _) (hn _)) (hn _)) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _),
      Real.logb_mul (hn _) (hn _), Real.logb_mul (mul_ne_zero (hn _) (hn _)) (hn _), Real.logb_mul (hn _) (hn _)] at k2
    simp only [betaAt, hv]
    linarith
  have hneg : ∀ a, vPsiAt D f p (-a) = vPsiAt D f p a := by
    intro a
    have e := congrArg Q ((val_mul hJ _ _ _).symm.trans (val_corr hJ (Dg.psi_even a) (𝟙 _)))
    have vs : Q (val (LB.pullGen D.P.L _ _ D.sym (D.xK a)) (𝟙 _) z J) = 1 := by
      refine (congrArg Q (val_pull hJ _ _ _)).trans (hQ _ (val_mem hI D.sym (D.c a).left (fun k => ?_) _ ?_))
      · fin_cases k
        · exact over_sec _ _
        · exact over_sec (D.c a) (𝟙 _)
      · simp [ptK]
    rw [map_mul, vs, _root_.mul_one] at e
    rw [hv, hv, norm_eq f hf z (hur (-a)) (hur a) ((hP _).trans (e.trans (hP _).symm))]
  refine ⟨hadd, fun a => ?_⟩
  have h0 := hadd 0 0 0
  have h1 := hadd a (-a) a
  have hn := hneg a
  simp only [betaAt, add_zero, zero_add, add_neg_cancel, neg_add_cancel] at h0 h1 ⊢
  linarith

end GlobalTheory.BetaAdd
