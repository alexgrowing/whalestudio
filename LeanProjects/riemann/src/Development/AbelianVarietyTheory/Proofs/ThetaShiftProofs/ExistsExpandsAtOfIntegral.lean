import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecBGenerates
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSmulMemSpanOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaUnit

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection

theorem secIsMul_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y} (a : R)
    (s t : SecOver p L) : SecIsMul p a s t ↔ s = a • t :=
  ⟨fun h => SecOver.ext _ _ h, fun h _ => by rw [h]; rfl⟩

theorem exists_integral_term (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (D : DegData R I) (E : Fam D.toPre (FractionRing R) 1) (g₀ : D.toPre.SecB 1 0)
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) 0) (DegPre.famε 1) (E.s 0) (D.toPre.famφB 0)
      (DegPre.famε 1) g₀ (DegPre.prB D.toPre (FractionRing R)).left 1) (χ : D.toPre.X) (hχ : χ ≠ 0) :
    ∃ a ∈ I, ∃ g g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom a g g' ∧
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) χ) (DegPre.famε 1) (E.s χ) (D.toPre.famφB χ)
        (DegPre.famε 1) g (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  have hL := D.toPre.P.isLB
  obtain ⟨e, he, a, ha, hψ⟩ := LevelOneIdeal.exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  refine ⟨a, ha, ?_⟩
  suffices H : ∃ g g' : D.toPre.SecB 1 (0 + 1 • χ), SecIsMul D.toPre.P.A.hom a g g' ∧
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) (0 + 1 • χ)) (DegPre.famε 1) (E.s (0 + 1 • χ))
        (D.toPre.famφB (0 + 1 • χ)) (DegPre.famε 1) g (DegPre.prB D.toPre (FractionRing R)).left 1 by
    rwa [zero_add, one_smul] at H
  have c₁ : D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by simp [SectionScalarValuation.cQ]
  have c₂ : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have c₃ : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero (D := D.toPre) _
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre 1 0 χ (LB.mulGen D.toPre.P.L _ _ _ _ e D.toPre.rig)
    (mulGen_isGen _ _ _ _ _ _ _ he D.toPre.rig_gen) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, c₃, _root_.one_mul]
      simp)
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)
      (Sum.elim (D.toPre.famφB (0 + 1 • χ))
        (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)))
      (Sum.elim (DegPre.famε 1) (DegPre.deltaε 1)) (D.toPre.famφB (0 + 1 • χ)) (DegPre.famε 1) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨g', hg'⟩ := exists_sec hL hformB
    (pullMulSec g₀ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left eB heB)
  obtain ⟨g, hgg⟩ := IntegralExpansion.exists_secIsMul D.toPre.P.A.hom a g'
  refine ⟨g, g', hgg, SectionScalarValuation.secScal_of_sval hL fun y J hJ => Eq.symm ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG 1 χ 0
  have vu := hv u hu hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (E.fe χ 0 u hu hc) _ (𝟙 _) y J hJ
  have htr : (DegPre.trF D.toPre (FractionRing R) χ).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [DegPre.trF, DegPre.prB, lift_snd, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
    rfl
  rw [H1.sval_scal hg _ y hJ, Category.id_comp, htr] at hrel
  rw [hrel, sval_of_secIsMul hgg _ y hJ, Category.id_comp, hg' _ _ y J hJ, sval_pullMulSec _ _ _ heB _ y hJ,
    mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing R))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
  have v₂ := hψ _ ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
  have v₃ : val D.toPre.rigK ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J =
      val D.toPre.rig ((DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom) y J := by
    rw [← w₁, ← Category.assoc]
    exact val_pull hJ _ _ _
  rw [Category.assoc, w₁] at v₂
  rw [Over.id_left, Category.id_comp, LevelOneIdeal.val_famMult_one D.tau_bimult _ hJ, v₃, uVal, Category.id_comp,
    Category.id_comp, comp_cP] at vu
  rw [val_mul hJ] at v₁
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

theorem exists_expandsAt_of_integral [IsNoetherianRing R] (hI : I ≤ maximalIdeal R) (U : Unif I D A G)
    [GeometricallyConnected G.hom] {k : ℕ} (hk : 1 ≤ k) (Φ : Fam D.toPre (FractionRing R) k)
    (f : ∀ α, D.toPre.SecB k α)
    (hf : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (Φ.s α)
      (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) :
    ∃ σ : H0 U.LG.L k, ∀ e : ℕ, U.ExpandsAt e k σ f := by
  obtain ⟨s, ⟨r, hr, σ₁, f₁, -, hf₁, hE₁⟩, -⟩ := (U.expand k hk).2 Φ
  have h₁ : ∀ α, SecIsMul D.toPre.P.A.hom r (f₁ α) (f α) := fun α =>
    IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB _ (IntegralExpansion.prB_app_injective D.toPre) (hf α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₁ α)
  have := U.smooth
  have hJac : I ≤ Ideal.jacobson ⊥ := by rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  obtain ⟨σ, hσ⟩ := GermDiv.main R I hJac G _ (LB.isLB_linComb U.LG.isLB _ _) σ₁ r hr fun n y j hj => by
    obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    obtain ⟨S, hS⟩ := expandsAt_val U.toUnifPre n k σ₁ f₁ (hE₁ n)
    obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB y
    have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hj 0)
    have hc : pGl U.toUnifPre n ≫ D.toPre.P.A.hom = fGl I G n ≫ G.hom :=
      (Over.w (U.gt n).pG).trans (Over.w (fstG I n G)).symm
    simp only [Category.id_comp] at H
    refine (Units.dvd_mul_left.1 (H ▸ Finset.dvd_sum fun α _ => ?_) : _ ∣ sv U.toUnifPre k σ₁ (fGl I G n) y jL)
    rw [sval_of_secIsMul (h₁ α) _ y hJ, hc, _root_.mul_assoc]
    exact dvd_mul_right _ _
  exact ⟨σ, expandsAt_cancel_of_ne_zero R I D A G U.toUnifPre k r hr σ σ₁ f f₁ hσ h₁ hE₁⟩

omit [IsDomain R] in

theorem exists_thick_pt {J : Ideal R} (hJ : J ≤ maximalIdeal R) (e : ℕ) (X : Over (Spec (CommRingCat.of R)))
    (x : X.left) (hx : X.hom x = closedPoint R) :
    ∃ y : (thickObj R J e X).left, pullback.fst X.hom (thick R J e) y = x := by
  have hm : closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ (e + 1)))) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.mem_zeroLocus]
    exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hJ
  obtain ⟨z, hz⟩ := hm
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback X.hom (thick R J e)) x z
    (hx.trans hz.symm)
  exact ⟨y, hy⟩

theorem exists_group_pt (hI : I ≤ maximalIdeal R) (U : UnifPre I D A G) (e : ℕ) (x : D.toPre.P.A.left)
    (hx : D.toPre.P.A.hom x = closedPoint R) : ∃ y : (thickObj R I e G).left, pGl U e y = x := by
  obtain ⟨x', rfl⟩ := exists_thick_pt hI e D.toPre.P.A x hx
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x'
  exact ⟨y, rfl⟩

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 X) (r z) U f) := by
  rw [gs_stalkMap r z U h, isUnit_map_iff]

theorem isUnit_sval {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) := by
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((isUnit_gs_iff r z _ hj _).2 hu)

omit [IsDomain R] in

theorem mem_of_cst_eq_zero {J : Ideal R} {Y : Scheme.{0}} (p : Y ⟶ Sp (R ⧸ J)) [Flat p] (y : Y)
    (hy : (p ≫ spMap (Ideal.Quotient.mk J)) y = closedPoint R) {a : R}
    (h : cst (p ≫ spMap (Ideal.Quotient.mk J)) y a = 0) : a ∈ J := by
  rw [cst_comp] at h
  have h₁ : cst (𝟙 _) (p y) (Ideal.Quotient.mk J a) = 0 := by
    refine stalkMap_injective_of_flat p y ?_
    rw [H1.cst_stalkMap, Category.comp_id, h, map_zero]
  rw [cst, gs_eq _ _ ⊤ trivial] at h₁
  obtain ⟨W, hW, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq (Sp (R ⧸ J)).presheaf (U := ⊤) (V := ⊤) (p y) trivial trivial
    _ 0 (h₁.trans (map_zero _).symm)
  have hWt : W = ⊤ := top_le_iff.1 fun z _ => by
    refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes z (p y)).1 fun t ht => ?_) W.isOpen hW
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    have h₂ : t ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk J) (p y)).asIdeal := by
      rw [show PrimeSpectrum.comap (Ideal.Quotient.mk J) (p y) = closedPoint R from hy]
      exact le_maximalIdeal (PrimeSpectrum.comap (Ideal.Quotient.mk J) z).isPrime.ne_top ht
    exact h₂
  subst hWt
  rw [map_zero, Subsingleton.elim i₁ (𝟙 _)] at e
  refine Ideal.Quotient.eq_zero_iff_mem.1
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv).1 ?_)
  simp only [op_id, CategoryTheory.Functor.map_id] at e
  exact e.trans (map_zero _).symm

theorem nonzeroOnSpecial_of_mem (U : Unif I D A G) (s : H0 U.LG.L 1) (g : G.left) (hg : G.hom g = closedPoint R)
    (hs : g ∈ nonzeroLocus s) : NonzeroOnSpecial U s := by
  obtain ⟨y, rfl⟩ := exists_thick_pt le_rfl 0 G g hg
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus s _).1 hs
  refine ⟨j, fun h => ?_⟩
  have h₁ := gs_pull (𝟙 _) (fGl (maximalIdeal R) G 0) y _ hj (s.f j)
  rw [Category.id_comp] at h₁
  exact ((isUnit_gs_iff (fGl (maximalIdeal R) G 0) y _ hj _).2 hu).ne_zero
    (h₁.symm.trans ((congrArg _ h).trans (gs_zero _ y _ hj)))

theorem isUnit_of_nonzeroOnSpecial (U : Unif I D A G) {s σ : H0 U.LG.L 1} {b : R} (h : SecIsMul G.hom b s σ)
    (hs : NonzeroOnSpecial U s) : IsUnit b := by
  by_contra hb
  obtain ⟨j, hj⟩ := hs
  refine hj ?_
  rw [h j, map_mul, ThickDiv.resTop_scal, ThickDiv.app_constFn_eq_zero (maximalIdeal R) 0 G _
    (by rw [zero_add, pow_one]; exact hb), zero_mul]

end

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

omit [IsLocalRing R] in
theorem secScal_one_iff (D : DegPre R) {k : ℕ} (Φ : Fam D (FractionRing R) k) (α : D.X) (g : SecBMod D k α) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (Φ.s α) (D.famφB α) (DegPre.famε k) g
      (DegPre.prB D (FractionRing R)).left 1 ↔ resF D (FractionRing R) k α g = famComp D (FractionRing R) k α Φ := by
  have h := secScal_iff_resF D (FractionRing R) (famComp D (FractionRing R) k α Φ) g 1
  rwa [map_one, one_smul, scal, map_one, map_one] at h

theorem exists_eq_smul (hS : SecBaseChangeSt) [IsNoetherianRing R] (D : DegPre R) (th : SecBMod D 1 0)
    (hth : ∃ x, D.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus th) (s : SecBMod D 1 0) : ∃ b : R, s = b • th := by
  obtain ⟨g, hg⟩ : ∃ g : SecBMod D 1 0, ∀ s, ∃! a : R, SecIsMul D.P.A.hom a s g := exists_generator D hS
  obtain ⟨a, ha, -⟩ := hg th
  obtain ⟨b, hb, -⟩ := hg s
  obtain ⟨x, hx, hn⟩ := hth
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB x
  have hu := isUnit_sval th (𝟙 _) x hn hJ
  rw [sval_of_secIsMul ha _ x hJ, Category.id_comp] at hu
  obtain ⟨u, rfl⟩ : IsUnit a := by
    by_contra h
    exact cst_not_isUnit D.P.A.hom x hx h (isUnit_of_mul_isUnit_left hu)
  refine ⟨b * u⁻¹.val, ?_⟩
  rw [(secIsMul_iff _ _ _ _).1 ha, smul_smul, Units.inv_mul_cancel_right]
  exact (secIsMul_iff _ _ _ _).1 hb

theorem exists_mem_nonzeroLocus (hI : I ≤ maximalIdeal R) (U : UnifPre I D A G) {σ : H0 U.LG.L 1}
    {f : ∀ α, D.toPre.SecB 1 α} (hE : U.ExpandsAt 0 1 σ f)
    (h0 : ∃ x, D.toPre.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus (f 0))
    (hf : ∀ α, α ≠ 0 → ∃ a ∈ I, ∃ g : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom a (f α) g) :
    ∃ g, G.hom g = closedPoint R ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hx, hn⟩ := h0
  obtain ⟨y, rfl⟩ := exists_group_pt hI U 0 x hx
  have hc : pGl U 0 ≫ D.toPre.P.A.hom = fGl I G 0 ≫ G.hom := (Over.w (U.gt 0).pG).trans (Over.w (fstG I 0 G)).symm
  have hc' : pGl U 0 ≫ D.toPre.P.A.hom = (thickObj R I 0 G).hom ≫ spMap (Ideal.Quotient.mk (I ^ (0 + 1))) :=
    Over.w (U.gt 0).pG
  refine ⟨fGl I G 0 y, (congrArg (fun q => q y) hc).symm.trans hx, ?_⟩
  obtain ⟨S, hS⟩ := expandsAt_val U 0 1 σ f hE
  obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB y
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl I G 0 y)
  obtain ⟨H₁, H₂⟩ := hS _ (𝟙 _) y J hJ
  have H := H₂ jL hL
  simp only [Category.id_comp] at H H₁
  have hu := isUnit_sval (f 0) (pGl U 0) y hn hJ
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, g, hg⟩ := hf α hα
    rw [sval_of_secIsMul hg _ y hJ, hc', cst_comp, Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha),
      GermDiv.cst_zero, zero_mul, zero_mul]) (fun h => absurd (H₁ 0 h) hu.ne_zero)] at H
  have hm : fGl I G 0 y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  exact (SectionBaseChange.mem_nonzeroLocus σ _).2 ⟨fun _ => jL, hm, (isUnit_gs_iff (fGl I G 0) y _ hm _).1
    (isUnit_of_mul_isUnit_right (H ▸ hu.mul (Units.isUnit _)))⟩

theorem eq_one_of_weight_zero [IsNoetherianRing R] (hI : I ≤ maximalIdeal R) (U : UnifPre I D A G)
    {σ σ' : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)))}
    {f f' : ∀ α, SecBMod D.toPre 1 α} (hE : ∀ e, U.ExpandsAt e 1 σ f) (hE' : ∀ e, U.ExpandsAt e 1 σ' f')
    (h : f' 0 = f 0) (h0 : ∃ x, D.toPre.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus (f 0)) {b : R}
    (hb : σ' = b • σ) : b = 1 := by
  obtain ⟨x, hx, hn⟩ := h0
  have := U.smooth
  have key : ∀ e, 1 - b ∈ I ^ (e + 1) := fun e => by
    obtain ⟨y, rfl⟩ := exists_group_pt hI U e x hx
    have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ spMap (Ideal.Quotient.mk (I ^ (e + 1))) :=
      Over.w (U.gt e).pG
    obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB y
    have hE₀ := expandsAt_add U (hE' e) (expandsAt_smul U (-b) (hE e))
    have h₁ := WeightDvd.dvd_on_group U e 1 0 _ σ _ ((secIsMul_iff _ _ _ _).2
      (by rw [hb, ← add_smul, add_neg_cancel])) hE₀ 0 y J hJ
    have h₂ : (f' + (-b) • f) 0 = (1 - b) • f 0 := by
      rw [Pi.add_apply, Pi.smul_apply, h, sub_smul, one_smul, neg_smul, sub_eq_add_neg]
    rw [h₂, GermDiv.cst_zero, zero_dvd_iff, sval_of_secIsMul ((secIsMul_iff _ _ _ _).2 rfl) _ y hJ,
      (isUnit_sval (f 0) (pGl U e) y hn hJ).mul_left_eq_zero, hc] at h₁
    have : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
    exact mem_of_cst_eq_zero _ y ((congrArg (fun q => q y) hc).symm.trans hx) h₁
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing I (fun h => (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ hI)))
  have : 1 - b ∈ (⊥ : Ideal R) := hbot ▸ Ideal.mem_iInf.2 fun n => Ideal.pow_le_pow_right (Nat.le_succ n) (key n)
  exact (sub_eq_zero.1 this).symm

theorem exists_eq_smul_group (hG : GlobalFnsSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R) (U : Unif I D A G)
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)))}
    {f : ∀ α, SecBMod D.toPre 1 α} (hE : ∀ e, U.ExpandsAt e 1 σ f) {Φ : Fam D.toPre (FractionRing R) 1}
    (hf : ∀ α, resF D.toPre (FractionRing R) 1 α (f α) = famComp D.toPre (FractionRing R) 1 α Φ)
    (hgen : ∀ t : SecBMod D.toPre 1 0, ∃ b : R, t = b • f 0)
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)))) :
    ∃ b : R, s = b • σ := by
  have hsm := U.smooth
  have h := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsSchemeTheoreticallyDominant (jK R) := h.2
  have : QuasiCompact (jK R) := h.1
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hp : pullback.fst G.hom (jK R) ≫ G.hom =
      pullback.snd G.hom (jK R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (jK R)) k =
      pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  have hρ := pullOver_injective_of_dominant U.LG.L (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) hp hφ
  set ρ := pullOver U.LG.L (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) hp hφ with hρdef
  have hS := fun s₁ s₂ c => secScal_iff hp hφ (ε := fun _ : Fin 1 => ((1 : ℕ) : ℤ)) U.LG.isLB s₁ s₂
    (pullback.snd G.hom (jK R) ≫ jK R) (algebraMap R (FractionRing R)) rfl c
  have one₁ : scal (pullback.snd G.hom (jK R) ≫ jK R) (1 : R) = 1 := by rw [scal, map_one, map_one]
  have one₂ : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by rw [scal, map_one, map_one]
  obtain ⟨Ψ, hΨ, -⟩ := (U.expand 1 le_rfl).1 (ρ s)
  obtain ⟨g, -, hg⟩ := IntegralExpansionLocal.main R I hI D A G U.toUnifPre 1 s (ρ s)
    (one₁ ▸ (hS _ _ 1).2 (by rw [map_one, one_smul])) Ψ hΨ
  obtain ⟨b, hb⟩ := hgen (g 0)
  have h₀ : Ψ = toF (R := R) (FractionRing R) b • Φ := by
    refine fam_ext fun χ i => congrArg (fun q => LB.Sec.f q i) (?_ : Ψ.s χ = (_ : Fam _ _ _).s χ)
    refine FamFree.eq_of_eq_add_nsmul hG _ _ (α := 0) ⟨χ, by rw [zero_add, one_smul]⟩ ?_
    have e := (secScal_one_iff D.toPre Ψ 0 _).1 (hg 0)
    rw [hb, map_smulₛₗ, hf, ← map_smul] at e
    exact e.symm
  have hX : U.toUnifPre.Expands 1 (ρ (b • σ)) Ψ :=
    ⟨1, one_ne_zero, (b • σ :), (b • f :), (hS _ _ _).2 (by rw [map_one, one_smul]),
      fun χ => one₂ ▸ (secScal_one_iff D.toPre Ψ χ _).2 (by
        rw [h₀, Pi.smul_apply, map_smulₛₗ, hf, ← map_smul]),
      fun e => expandsAt_smul U.toUnifPre b (hE e)⟩
  exact ⟨b, hρ (((U.expand 1 le_rfl).2 Ψ).unique hΨ hX)⟩

theorem exists_theta (hG : GlobalFnsSt) (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R)
    (U : Unif I D A G) [GeometricallyConnected G.hom] (th : D.toPre.SecB 1 0)
    (hth : ∃ x, D.toPre.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus th) :
    ∃ (σ : H0 U.LG.L 1) (fam : ∀ α, D.toPre.SecB 1 α), fam 0 = th ∧ (∀ n, U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      (∀ α, α ≠ 0 → ∃ a ∈ I, ∃ g : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom a (fam α) g) ∧
      (∀ (σ' : H0 U.LG.L 1) (fam' : ∀ α, D.toPre.SecB 1 α), fam' 0 = th →
        (∀ n, U.toUnifPre.ExpandsAt n 1 σ' fam') → σ' = σ) ∧
      (∀ s : H0 U.LG.L 1, ∃! b : R, SecIsMul G.hom b s σ) ∧
      ∀ (s : H0 U.LG.L 1) (b : R), SecIsMul G.hom b s σ → (IsUnit b ↔ NonzeroOnSpecial U s) ∧
        (IsUnit b ↔ ∃ g, G.hom g = closedPoint R ∧ g ∈ nonzeroLocus s) := by
  obtain ⟨Φ, hΦ, -⟩ := FamFree.exists_fam_single (F := FractionRing R) hG D.tau_bimult le_rfl 0
    (resF D.toPre (FractionRing R) 1 0 th)
  have h₀ := (secScal_one_iff D.toPre Φ 0 th).2 hΦ.symm
  have ex : ∀ α, ∃ g : D.toPre.SecB 1 α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α)
      (DegPre.famε 1) (Φ.s α) (D.toPre.famφB α) (DegPre.famε 1) g (DegPre.prB D.toPre (FractionRing R)).left 1 ∧
      (α ≠ 0 → ∃ a ∈ I, ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom a g g') := fun α => by
    by_cases hα : α = 0
    · subst hα
      exact ⟨th, h₀, fun h => absurd rfl h⟩
    · obtain ⟨a, ha, g, g', h₁, h₂⟩ := exists_integral_term hG D Φ th h₀ α hα
      exact ⟨g, h₂, fun _ => ⟨a, ha, g', h₁⟩⟩
  choose fam hfam hmem using ex
  have hres : ∀ α, resF D.toPre (FractionRing R) 1 α (fam α) = famComp D.toPre (FractionRing R) 1 α Φ :=
    fun α => (secScal_one_iff D.toPre Φ α _).1 (hfam α)
  obtain rfl : fam 0 = th := resF_injective D.toPre (FractionRing R) 1 0 ((hres 0).trans hΦ)
  obtain ⟨σ, hσ⟩ := exists_expandsAt_of_integral hI U le_rfl Φ fam hfam
  have hgen := exists_eq_smul_group hG hI U hσ hres (exists_eq_smul hS D.toPre _ hth)
  obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus hI U.toUnifPre (hσ 0) hth hmem
  obtain ⟨J, hJ⟩ := exists_good' U.LG.isLB g
  have hu := isUnit_sval σ (𝟙 _) g hn hJ
  have := U.smooth
  refine ⟨σ, fam, rfl, hσ, hmem, fun σ' fam' h hE => ?_, fun s => ?_, fun s b hb => ?_⟩
  · obtain ⟨b, hb⟩ := hgen σ'
    obtain rfl := eq_one_of_weight_zero hI U.toUnifPre hσ hE h hth hb
    exact hb.trans (one_smul R _)
  · obtain ⟨b, hb⟩ := hgen s
    have hb' := (secIsMul_iff _ _ _ _).2 hb
    refine ⟨b, hb', fun b' h => by_contra fun hne => hu.ne_zero (cst_regular G.hom g (sub_ne_zero.2 hne) ?_)⟩
    have e := (sval_of_secIsMul h (𝟙 _) g hJ).symm.trans (sval_of_secIsMul hb' _ g hJ)
    rw [Category.id_comp] at e
    show _ * _ = _ * _
    rw [cst_sub, sub_mul, e, sub_self, mul_zero]
  · have h₁ : IsUnit b → ∃ g, G.hom g = closedPoint R ∧ g ∈ nonzeroLocus s := fun h => by
      refine ⟨g, hg, (SectionBaseChange.mem_nonzeroLocus s _).2 ⟨_, hJ.mem _ (𝟙 _), ?_⟩⟩
      obtain ⟨u, rfl⟩ := h
      have e := sval_of_secIsMul hb (𝟙 _) g hJ
      have hc : IsUnit (cst (𝟙 _ ≫ G.hom) g u.val) :=
        IsUnit.of_mul_eq_one (cst (𝟙 _ ≫ G.hom) g u⁻¹.val) (by rw [← cst_mul', u.mul_inv, cst_one'])
      exact (e ▸ hc.mul hu : IsUnit (sval s _ g J))
    have h₂ : (∃ g, G.hom g = closedPoint R ∧ g ∈ nonzeroLocus s) → NonzeroOnSpecial U s :=
      fun ⟨g, h, h'⟩ => nonzeroOnSpecial_of_mem U s g h h'
    exact ⟨⟨h₂ ∘ h₁, isUnit_of_nonzeroOnSpecial U hb⟩, h₁, isUnit_of_nonzeroOnSpecial U hb ∘ h₂⟩

end

end GlobalTheory.ThetaUnit
