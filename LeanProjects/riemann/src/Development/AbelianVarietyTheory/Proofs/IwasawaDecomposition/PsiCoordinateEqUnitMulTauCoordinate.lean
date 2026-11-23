import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiTauCoordRel

open GlobalTheory.PeriodBalance GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

def kst (ξ : Spec (CommRingCat.of (FractionRing R))) :
    FractionRing R →+* (Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

theorem kst_algebraMap (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) :
    kst ξ (algebraMap R (FractionRing R) r) = cst ξ r := rfl

theorem kst_injective (ξ : Spec (CommRingCat.of (FractionRing R))) : Function.Injective (kst (R := R) ξ) :=
  RingHom.injective _

theorem gm_genVal (ξ : Spec (CommRingCat.of (FractionRing R))) {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι)
    (h : ⊤ ≤ M.U j) :
    (gm (𝟙 _) ξ (M.U j) (t.s j)).val = kst ξ (genVal t j h).val := by
  rw [gm_val _ ξ _ (h trivial)]
  simp only [kst, genVal, RingHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h) ξ trivial _).symm

theorem gm_mulGen {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (y : Y) (j : K ⊕ K' → L.ι) (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j) =
      gm (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)) *
        gm (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))

theorem gm_invGen {Y X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι) :
    gm (𝟙 Y) y (LB.wchart L φ j) ((LB.invGen L φ ε t).s j) = (gm (𝟙 Y) y (LB.wchart L φ j) (t.s j))⁻¹ :=
  map_inv _ _

theorem mem_inl {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ (j ∘ Sum.inl) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

theorem mem_inr {Y X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)}
    {φ' : K' → (Y ⟶ X)} {y : Y} {j : K ⊕ K' → L.ι} (hy : y ∈ LB.wchart L (Sum.elim φ φ') j) :
    y ∈ LB.wchart L φ' (j ∘ Sum.inr) :=
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

variable [IsLocalRing R]

theorem val_psi_chart (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) {J} (hJ : Good D.P.L ξ J)
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
      p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) :
    ∃ u : Rˣ, val (D.psi χ) (𝟙 _) ξ J = Units.map (cst ξ).toMonoidHom u *
      gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
  have hx : D.xK χ = jK R ≫ (D.c χ).left := DVR.QForm.ptK_eq D χ
  have t := gen_trans (D.psi_gen χ) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
    (hJ.mem (fun _ : PUnit => D.xK χ) (𝟙 _)) hm
  obtain ⟨u, hu⟩ := unit_gm' ξ (D.c χ).left (D.P.L.U (J (jK R ≫ (D.c χ).left)) ⊓ D.P.L.U (j PUnit.unit))
    ⟨hJc _ (Over.w _), hj trivial⟩ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit))
  have h2 : trF (L := D.P.L) (fun _ : PUnit => D.xK χ) (fun _ => -1) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) ξ
      (fun _ => J (𝟙 _ ≫ D.xK χ)) j =
        (gm (jK R ≫ (D.c χ).left) ξ _ (D.P.L.g (J (jK R ≫ (D.c χ).left)) (j PUnit.unit)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, hx]
  refine ⟨u⁻¹, t.trans ?_⟩
  rw [h2, map_inv]
  congr 2
  exact Units.ext hu

theorem val_int {A : Over (Spec (CommRingCat.of R))} {L : LB A.left} (ξ : Spec (CommRingCat.of (FractionRing R)))
    {J : ((Spec (CommRingCat.of (FractionRing R))) ⟶ A.left) → L.ι}
    (hJc : ∀ p : Spec (CommRingCat.of R) ⟶ A.left, p ≫ A.hom = 𝟙 _ → p (closedPoint R) ∈ L.U (J (jK R ≫ p)))
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (p : Spec (CommRingCat.of R) ⟶ Y) (hp : ∀ k, (p ≫ φ k) ≫ A.hom = 𝟙 _) :
    ∃ w : Rˣ, val t (jK R ≫ p) ξ J = Units.map (cst ξ).toMonoidHom w := by
  obtain ⟨w, hw⟩ := unit_gm' ξ p (LB.wchart L φ (fun k => J ((jK R ≫ p) ≫ φ k)))
    (Set.mem_iInter.2 fun k => by
      have := hJc (p ≫ φ k) (hp k)
      rw [← Category.assoc] at this
      exact this) (t.s _)
  exact ⟨w, Units.ext hw⟩

theorem toUnit_left : (toUnit (TK R)).left = jK R := by
  simpa using Over.w (toUnit (TK R))

theorem gm_rigK (D : DegPre R) (ξ : Spec (CommRingCat.of (FractionRing R))) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D η[D.P.A] (j PUnit.unit))
    (hm : ξ ∈ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) :
    ∃ w : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j) (D.rigK.s j) =
      Units.map (cst ξ).toMonoidHom w := by
  have e1 := gm_res (𝟙 _) ξ (show LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) j ≤
      (toUnit (TK R)).left ⁻¹ᵁ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j from
      fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) hm
    (pullU (toUnit (TK R)).left _ (D.rig.s j))
  have e2 := gm_pull (𝟙 _) (toUnit (TK R)).left ξ (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) (D.rig.s j)
  have e3 : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
  rw [e3] at e2
  obtain ⟨w, hw⟩ := unit_gm' ξ (𝟙 _) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) j)
    (Set.mem_iInter.2 fun _ => hj trivial) (D.rig.s j)
  exact ⟨w, (e1.trans e2).trans (Units.ext hw)⟩

theorem alg {G : Type} [CommGroup G] (T G1 G2 G3 c1 c2 c3 c4 c5 c6 c7 Vab Va Vb Vr Vu Kr : G)
    (h1 : T = G1 * G2⁻¹ * G3⁻¹ * c4⁻¹) (h2 : Vab = c1 * G1) (h3 : Va = c2 * G2) (h4 : Vb = c3 * G3)
    (h7 : Vr = c5) (h8 : Vu = c6)
    (h5 : Vab * Va⁻¹ * Vb⁻¹ * Vr⁻¹ * Vu = Va * Vr) (h6 : Va = c7 * Kr) :
    Kr = c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹ * T := by
  subst h1 h2 h4 h3 h7 h8
  have hK : Kr = c7⁻¹ * (c2 * G2) := by rw [h6]; group
  subst hK
  apply Additive.ofMul.injective
  have h5' := congrArg Additive.ofMul h5
  simp only [ofMul_mul, ofMul_inv] at h5' ⊢
  rw [← sub_eq_zero] at h5' ⊢
  refine Eq.trans ?_ (congrArg Neg.neg h5' |>.trans neg_zero)
  abel

theorem final (ξ : Spec (CommRingCat.of (FractionRing R))) (r : R) (h0 : r ≠ 0) (X : (FractionRing R)ˣ) (c : Rˣ)
    (key : Units.map (kst ξ).toMonoidHom (toUnitK r h0) =
      Units.map (cst ξ).toMonoidHom c * Units.map (kst ξ).toMonoidHom X) :
    algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (c : R) * (X : FractionRing R) := by
  have k3 : toUnitK r h0 = Units.map (algebraMap R (FractionRing R)).toMonoidHom c * X := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [key, map_mul]
    rfl
  exact congrArg Units.val k3

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O), TraceFormTwistIso D oa w0 → ∀ (y : D.X) (r : R) (x : (FractionRing R)ˣ),
    PsiCoord D y r → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D y (w0 • y) x →
    ∃ u : Rˣ, algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u : R) * (x : FractionRing R) := by
  intro R _ _ _ D O _ _ _ oa w0 hW y r x hr hx
  obtain ⟨u, -, -, hrel⟩ := hW
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom

  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hrel y) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [val_pull hJ] at e
  have e' := (congrArg (· * val u (𝟙 _ ≫ D.xK y) ξ J) (PeriodBalance.val_tau D ξ hJ y (w0 • y))).symm.trans e
  obtain ⟨c6, h6⟩ : ∃ w : Rˣ, val u (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact DVR.QForm.ptK_eq D y
    rw [this]
    refine val_int ξ hJc u (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A, (![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left,
        (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left] : Fin 4 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨c5, h5⟩ : ∃ w : Rˣ, val D.rigK (𝟙 _) ξ J = cU w := by
    unfold DegPre.rigK
    rw [val_pull hJ]
    have : 𝟙 _ ≫ (toUnit (TK R)).left = jK R ≫ 𝟙 _ := by rw [toUnit_left]; simp
    rw [this]
    exact val_int ξ hJc D.rig (𝟙 _) fun _ => by rw [Category.id_comp]; exact Over.w η[D.P.A]

  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau y (w0 • y)) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc (y + w0 • y) _ i1 (mem_inl (mem_inl (mem_inl hm)))
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc y _ i2 (mem_inr (mem_inl (mem_inl hm)))
  obtain ⟨c3, g3⟩ := val_psi_chart D ξ hJ hJc (w0 • y) _ i3 (mem_inr (mem_inl hm))
  obtain ⟨c4, g4⟩ := gm_rigK D ξ _ i4 (mem_inr hm)

  have h0 := PsiCoordLocal.ne_zero_of_coord hr
  obtain ⟨jp, hp, ip, ep⟩ := GlobalTheory.PeriodFormCompare.isPsiCoord_toUnitK hr h0
  obtain ⟨c7, g7⟩ := val_psi_chart D ξ hJ hJc y jp ip (hp trivial)
  have eP := gm_genVal ξ (D.psi y) jp hp
  rw [← ep] at eP
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau y (w0 • y)).s j) =
      kU (genVal (D.tau y (w0 • y)) j h) := Units.ext eT
  have eP' : gm (𝟙 _) ξ (LB.wchart D.P.L _ jp) ((D.psi y).s jp) = kU (toUnitK r h0) := Units.ext eP
  have key := alg (h1 := eT'.symm.trans (dT.trans (by rw [g4]))) (h2 := g1) (h3 := g2) (h4 := g3) (h7 := h5)
    (h8 := h6) (h5 := e') (h6 := g7.trans (congrArg (cU c7 * ·) eP'))
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4 * c5⁻¹ * c5⁻¹ * c6 * c7⁻¹, final ξ r h0 _ _ (key.trans ?_)⟩
  simp only [cU, kU, map_mul, map_inv]

end GlobalTheory.PsiTauCoordRel
