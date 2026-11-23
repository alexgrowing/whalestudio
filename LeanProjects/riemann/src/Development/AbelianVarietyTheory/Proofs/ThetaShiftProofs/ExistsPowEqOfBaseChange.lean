import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

noncomputable section

namespace GlobalTheory.TorusExt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Cocycle

variable {X U : Type} [AddCommGroup X] [CommGroup U]

structure IsSymmCocycle (c : X → X → U) : Prop where
  zero : ∀ x, c 0 x = 1
  symm : ∀ x y, c x y = c y x
  coc : ∀ x y z, c (x + y) z * c x y = c x (y + z) * c y z

@[ext] structure CocycleExt {c : X → X → U} (hc : IsSymmCocycle c) where

  u : U

  x : X

instance {c : X → X → U} (hc : IsSymmCocycle c) : AddCommGroup (CocycleExt hc) :=
  letI : Add (CocycleExt hc) := ⟨fun a b => ⟨a.u * b.u * (c a.x b.x)⁻¹, a.x + b.x⟩⟩
  letI : Zero (CocycleExt hc) := ⟨⟨1, 0⟩⟩
  letI : Neg (CocycleExt hc) := ⟨fun a => ⟨a.u⁻¹ * c (-a.x) a.x, -a.x⟩⟩
  { add_assoc := fun a b d => CocycleExt.ext (by
      show a.u * b.u * (c a.x b.x)⁻¹ * d.u * (c (a.x + b.x) d.x)⁻¹ =
        a.u * (b.u * d.u * (c b.x d.x)⁻¹) * (c a.x (b.x + d.x))⁻¹
      have e := congrArg Additive.ofMul (hc.coc a.x b.x d.x)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e ⊢
      linear_combination (norm := abel) -e) (add_assoc _ _ _)
    zero_add := fun a => CocycleExt.ext (by
      show 1 * a.u * (c 0 a.x)⁻¹ = a.u
      rw [hc.zero]; simp) (zero_add _)
    add_zero := fun a => CocycleExt.ext (by
      show a.u * 1 * (c a.x 0)⁻¹ = a.u
      rw [hc.symm, hc.zero]; simp) (add_zero _)
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun a => CocycleExt.ext (by
      show a.u⁻¹ * c (-a.x) a.x * a.u * (c (-a.x) a.x)⁻¹ = 1
      rw [mul_right_comm a.u⁻¹]; simp) (neg_add_cancel _)
    add_comm := fun a b => CocycleExt.ext (by
      show a.u * b.u * (c a.x b.x)⁻¹ = b.u * a.u * (c b.x a.x)⁻¹
      rw [hc.symm, mul_comm a.u]) (add_comm _ _) }

theorem IsSymmCocycle.exists_coboundary [Module.Free ℤ X] {c : X → X → U} (hc : IsSymmCocycle c) :
    ∃ f : X → U, f 0 = 1 ∧ ∀ x y, f (x + y) * c x y = f x * f y := by
  let p : CocycleExt hc →+ X := AddMonoidHom.mk' (fun a => a.x) fun _ _ => rfl
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p.toIntLinearMap (LinearMap.id : X →ₗ[ℤ] X)
    fun x => ⟨⟨1, x⟩, rfl⟩
  have hx : ∀ x, (σ x).x = x := fun x => LinearMap.congr_fun hσ x
  refine ⟨fun x => (σ x).u, congrArg CocycleExt.u (map_zero σ), fun x y => ?_⟩
  have e : (σ (x + y)).u = (σ x).u * (σ y).u * (c (σ x).x (σ y).x)⁻¹ := congrArg CocycleExt.u (map_add σ x y)
  show (σ (x + y)).u * c x y = _
  rw [e, hx, hx, inv_mul_cancel_right]

theorem exists_pow_eq_hom [Module.Free ℤ X] {F : Type} [Field F] [IsAlgClosed F] {n : ℕ} (hn : n ≠ 0)
    (t : Multiplicative X →* Fˣ) : ∃ s : Multiplicative X →* Fˣ, s ^ n = t := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (powMonoidHom n : Fˣ →* Fˣ).toAdditive.toIntLinearMap
    t.toAdditiveRight.toIntLinearMap fun x => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((x.toMul : Fˣ) : F) (Nat.pos_of_ne_zero hn)
      have h0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow hn] at hz
        exact x.toMul.ne_zero hz.symm
      exact ⟨Additive.ofMul (Units.mk0 z h0), Additive.toMul.injective (Units.ext hz)⟩
  exact ⟨σ.toAddMonoidHom.toMultiplicativeLeft, MonoidHom.ext fun x =>
    congrArg Additive.toMul (LinearMap.congr_fun hσ x.toAdd)⟩

end Cocycle

section Division

variable {S : Scheme.{0}} {k : Type} [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S)

theorem exists_pow_eq_of_noetherian [IsLocallyNoetherian S] (hM : MulNSt) (P : PolAV S) {n : ℕ} (hn : n ≠ 0)
    (a : Over.mk t ⟶ P.A) : ∃ b : Over.mk t ⟶ P.A, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hM S P n (Nat.pos_of_ne_zero hn)
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.snd (mulA P.A n).left a.left)
  have hb : (u ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu, Category.id_comp]
  have hw : (u ≫ pullback.fst (mulA P.A n).left a.left) ≫ P.A.hom = (Over.mk t).hom := by
    rw [← Over.w (mulA P.A n), ← Category.assoc, hb, Over.w a]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ n = b ≫ mulA P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_pow_eq_of_baseChange (hM : MulNSt) (hP : PolBaseChangeSt) (P : PolAV S) {n : ℕ} (hn : n ≠ 0)
    (a : Over.mk t ⟶ P.A) : ∃ b : Over.mk t ⟶ P.A, b ^ n = a := by
  obtain ⟨P', g, hg, -, hmul, -⟩ := hP S _ t P
  let a' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P'.A :=
    Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp t).symm)) (hg.lift_snd _ _ _)
  obtain ⟨b', hb'⟩ := exists_pow_eq_of_noetherian (𝟙 _) hM P' hn a'
  let Φ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ t) ⟶ P.A) :=
    MonoidHom.mk' (fun x => toBase hg.w x) (hmul _)
  let ρ : Over.mk t ⟶ Over.mk (𝟙 _ ≫ t) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  refine ⟨ρ ≫ Φ b', ?_⟩
  rw [← MonObj.comp_pow, ← map_pow, hb']
  exact Over.OverMorphism.ext ((Category.id_comp _).trans (hg.lift_fst _ _ _))

end Division

section Values

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem val_eq_of_val_eq {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {r : Z ⟶ Y}
    {z : Z} {J J' : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hJ' : Good L z J') (h : val t r z J = val t' r z J) :
    val t r z J' = val t' r z J' :=
  (gen_trans ht r z (hJ'.mem φ r) (hJ.mem φ r)).trans ((congrArg₂ (· * ·)
    (hF.trF r z (fun q => J' (r ≫ q)) (fun q => J (r ≫ q))) h).trans
    (gen_trans ht' r z (hJ'.mem φ' r) (hJ.mem φ' r)).symm)

theorem val_scaleGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

theorem oneGen_isGen : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable {F : Type} [Field F]

def stalkConst (y : Sp F) : F →+* (Sp F).presheaf.stalk y :=
  ((Sp F).presheaf.germ ⊤ y trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem stalkConst_surjective (y : Sp F) : Function.Surjective (stalkConst y) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) y z) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

def stalkUnits (y : Sp F) : Fˣ ≃* ((Sp F).presheaf.stalk y)ˣ :=
  Units.mapEquiv (RingEquiv.ofBijective (stalkConst y) ⟨(stalkConst y).injective, stalkConst_surjective y⟩).toMulEquiv

theorem stalkUnits_val (y : Sp F) (u : Fˣ) : (stalkUnits y u).val = stalkConst y u := rfl

theorem gm_unitOn (y : Sp F) (u : Fˣ) : gm (𝟙 (Sp F)) y ⊤ (unitOn u) = stalkUnits y u :=
  Units.ext (gm_val _ y ⊤ trivial _)

theorem gs_eq_stalkConst (x : Sp F ⟶ X) (y : Sp F) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    gs x y U f = stalkConst y (valF x U f) := by
  rw [valF, dif_pos h, gs_eq x y U (h trivial)]
  show _ = ((Sp F).presheaf.germ ⊤ y trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _))
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h) y trivial _).symm

theorem exists_gen_val (hL : L.IsLB) (φ : K → (Sp F ⟶ X)) (ε : K → ℤ) {y : Sp F} {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L y J) (u : ((Sp F).presheaf.stalk y)ˣ) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ val t (𝟙 _) y J = u := by
  obtain ⟨e, he⟩ := exists_gen_of_local L hL φ ε
  refine ⟨scaleGen (unitOn ((stalkUnits y).symm (u * (val e (𝟙 _) y J)⁻¹))) e, scaleGen_isGen _ _ he, ?_⟩
  rw [val_scaleGen _ _ _ hJ, gm_unitOn, MulEquiv.apply_symm_apply, inv_mul_cancel_right]

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] gtGroup

def IsTorusPtF (g : GtPtF D F) (t : D.X → F) : Prop :=
  g.b = DegPre.zeroF D F ∧ ∀ χ j, LB.Coh D.P.L (DegPre.gtφ D F g.b χ) j →
    ⊤ ≤ LB.wchart D.P.L (DegPre.gtφ D F g.b χ) j → valF (𝟙 (Sp F)) _ ((g.s χ).s j).val = t χ

theorem isTorusPtF_iff_isTorusPt [Algebra (FractionRing ℂ) ℂ] {D₀ : DegPre ℂ} (g : GtPtF D₀ ℂ) (t : D₀.X → ℂ) :
    IsTorusPtF g t ↔ IsTorusPt g t := Iff.rfl

theorem exists_good_chart (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ (y : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L y J := by
  let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
  choose I hI using fun q : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (q y)
  exact ⟨y, I, hI⟩

theorem pt_eq (y y' : (TF (R := R) F).left) : y = y' := Subsingleton.elim (α := PrimeSpectrum F) y y'

theorem isTorusPtF_iff_val (g : GtPtF D F) (t : D.X → F) : IsTorusPtF g t ↔
    g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → (charVal g χ y J).val = stalkConst (F := F) y (t χ) := by
  have key : ∀ χ (y : (TF (R := R) F).left) j (hj : ⊤ ≤ LB.wchart D.P.L (DegPre.gtφ D F g.b χ) j),
      (gm (𝟙 (TF (R := R) F).left) y (LB.wchart D.P.L (DegPre.gtφ D F g.b χ) j) ((g.s χ).s j)).val =
        stalkConst (F := F) y (valF (𝟙 (Sp F)) _ ((g.s χ).s j).val) := fun χ y j hj =>
    (gs_unit (𝟙 (Sp F)) y _ (hj trivial) _).symm.trans (gs_eq_stalkConst (𝟙 (Sp F)) y (U := LB.wchart D.P.L (DegPre.gtφ D F g.b χ) j) hj _)
  refine and_congr Iff.rfl ⟨fun h χ y J hJ => ?_, fun h χ j hc hj => ?_⟩
  · have hj : ⊤ ≤ LB.wchart D.P.L (DegPre.gtφ D F g.b χ) (fun k => J (𝟙 _ ≫ DegPre.gtφ D F g.b χ k)) :=
      fun z _ => pt_eq y z ▸ hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 _)
    exact (key χ y _ hj).trans (congrArg _ (h χ _ (fun a b e => congrArg (fun q => J (𝟙 _ ≫ q)) e) hj))
  · let y : (TF (R := R) F).left := IsLocalRing.closedPoint F
    obtain ⟨J, hJ, e⟩ := exists_good D.P.L D.P.isLB y _ j hc fun k => Set.mem_iInter.1 (hj (trivial : y ∈ ⊤)) k
    refine (stalkConst (F := F) y).injective ((key χ y j hj).symm.trans (Eq.trans ?_ (h χ y J hJ)))
    exact congrArg Units.val (val_of (g.s χ) _ y J j fun k => by rw [Category.id_comp]; exact e k).symm

theorem IsTorusPtF.fun_unique {g : GtPtF D F} {t t' : D.X → F} (h : IsTorusPtF g t) (h' : IsTorusPtF g t') : t = t' := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  exact funext fun χ => (stalkConst (F := F) y).injective
    ((((isTorusPtF_iff_val _ _).1 h).2 χ y J hJ).symm.trans (((isTorusPtF_iff_val _ _).1 h').2 χ y J hJ))

theorem IsTorusPtF.unique {g g' : GtPtF D F} {t : D.X → F} (h : IsTorusPtF g t) (h' : IsTorusPtF g' t) : g = g' := by
  obtain ⟨b, v⟩ := (isTorusPtF_iff_val _ _).1 h
  obtain ⟨b', v'⟩ := (isTorusPtF_iff_val _ _).1 h'
  exact gt_ext_val (b.trans b'.symm) fun χ y J hJ => Units.ext ((v χ y J hJ).trans (v' χ y J hJ).symm)

theorem formEq_gt_one (χ : D.X) : FormEq (K := PEmpty) PEmpty.elim PEmpty.elim
    (DegPre.gtφ D F (1 : TF (R := R) F ⟶ D.P.A) χ) DegPre.gtε :=
  fun U _ h => by rw [prod_gt, _root_.mul_one]; simp

theorem exists_isTorusPtF (t : Multiplicative D.X →* Fˣ) :
    ∃ g : GtPtF D F, IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ) := by
  have vv : ∀ χ (y : (TF (R := R) F).left) J, Good D.P.L y J →
      val (scaleGen (unitOn (t (Multiplicative.ofAdd χ))) (LB.oneGen D.P.L (Y := (TF (R := R) F).left)))
        (𝟙 (TF (R := R) F).left) y J =
        stalkUnits (F := F) y (t (Multiplicative.ofAdd χ)) := fun χ y J hJ =>
    (val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans ((_root_.mul_one _).trans (gm_unitOn y _)))
  obtain ⟨g, hb, hv⟩ := exists_gt (D := D) (F := F) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => scaleGen (unitOn (t (Multiplicative.ofAdd χ))) (LB.oneGen D.P.L))
    (fun _ => scaleGen_isGen _ _ oneGen_isGen) formEq_gt_one
    (fun y J hJ => (vv 0 y J hJ).trans (by rw [ofAdd_zero, map_one, map_one])) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, ofAdd_add, map_mul]
      exact map_mul (stalkUnits (F := F) y) _ _)
  exact ⟨g, (isTorusPtF_iff_val _ _).2 ⟨hb, fun χ y J hJ => congrArg Units.val ((hv χ y J hJ).trans (vv χ y J hJ))⟩⟩

theorem IsTorusPtF.add {g g' : GtPtF D F} {t t' : D.X → F} (h : IsTorusPtF g t) (h' : IsTorusPtF g' t') :
    IsTorusPtF (g + g') (t * t') := by
  obtain ⟨b, v⟩ := (isTorusPtF_iff_val _ _).1 h
  obtain ⟨b', v'⟩ := (isTorusPtF_iff_val _ _).1 h'
  refine (isTorusPtF_iff_val _ _).2 ⟨by rw [add_b, b, b', _root_.mul_one], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := add_val g g' χ hJ
  rw [b', C.face₃, _root_.mul_one] at e
  rw [e, Units.val_mul, v χ y J hJ, v' χ y J hJ]
  exact (map_mul (stalkConst (F := F) y) _ _).symm

def torusPt (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Additive (Multiplicative D.X →* Fˣ) →+ GtPtF D F :=
  AddMonoidHom.mk' (fun t => (exists_isTorusPtF t.toMul).choose) fun t t' =>
    (exists_isTorusPtF (t + t').toMul).choose_spec.unique
      ((exists_isTorusPtF t.toMul).choose_spec.add (exists_isTorusPtF t'.toMul).choose_spec)

theorem isTorusPtF_torusPt (t : Multiplicative D.X →* Fˣ) :
    IsTorusPtF (torusPt D F (Additive.ofMul t)) fun χ => t (Multiplicative.ofAdd χ) := (exists_isTorusPtF t).choose_spec

theorem isTorusPtF_iff_eq (g : GtPtF D F) (t : Multiplicative D.X →* Fˣ) :
    (IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ)) ↔ g = torusPt D F (Additive.ofMul t) :=
  ⟨fun h => h.unique (isTorusPtF_torusPt t), fun h => h ▸ isTorusPtF_torusPt t⟩

theorem torusPt_b (t : Additive (Multiplicative D.X →* Fˣ)) : (torusPt D F t).b = 1 := (isTorusPtF_torusPt t.toMul).1

theorem torusPt_val (t : Multiplicative D.X →* Fˣ) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (torusPt D F (Additive.ofMul t)) χ y J = stalkUnits (F := F) y (t (Multiplicative.ofAdd χ)) :=
  Units.ext (((isTorusPtF_iff_val _ _).1 (isTorusPtF_torusPt t)).2 χ y J hJ)

theorem torusPt_injective : Function.Injective (torusPt D F) := fun t t' e =>
  MonoidHom.ext (f := t.toMul) (g := t'.toMul) fun χ => Units.ext (congrFun
    ((isTorusPtF_torusPt t.toMul).fun_unique ((isTorusPtF_iff_eq _ t'.toMul).2 e)) χ.toAdd)

theorem gt_ext_val_at {g g' : GtPtF D F} (hb : g.b = g'.b) {y J} (hJ : Good D.P.L y J)
    (h : ∀ χ, charVal g χ y J = charVal g' χ y J) : g = g' :=
  gt_ext_val hb fun χ y' J' hJ' => by
    obtain rfl := pt_eq y y'
    exact val_eq_of_val_eq (fun U _ f => by rw [hb]) (g.isGen χ) (g'.isGen χ) hJ hJ' (h χ)

theorem exists_torusPt_eq {g : GtPtF D F} (hb : g.b = 1) :
    ∃ t : Multiplicative D.X →* Fˣ, g = torusPt D F (Additive.ofMul t) := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  refine ⟨MonoidHom.mk' (fun χ => (stalkUnits (F := F) y).symm (charVal g χ.toAdd y J)) fun χ χ' => ?_,
    gt_ext_val_at (hb.trans (torusPt_b _).symm) hJ fun χ =>
      ((torusPt_val _ χ hJ).trans ((stalkUnits (F := F) y).apply_symm_apply _)).symm⟩
  have e := charVal_add g hJ χ.toAdd χ'.toAdd
  rw [hb, C.face₃, _root_.mul_one] at e
  exact (congrArg (stalkUnits (F := F) y).symm e).trans (map_mul (stalkUnits (F := F) y).symm _ _)

theorem exists_isTorusPtF_of_b {g : GtPtF D F} (hb : g.b = 1) :
    ∃ t : Multiplicative D.X →* Fˣ, IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ) :=
  (exists_torusPt_eq hb).imp fun t h => (isTorusPtF_iff_eq g t).2 h

theorem range_torusPt : (torusPt D F).range = (gtProj D F).ker := by
  ext g
  exact ⟨fun ⟨t, e⟩ => e ▸ torusPt_b t, fun h => (exists_torusPt_eq h).elim fun t e => ⟨_, e.symm⟩⟩

section Action

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O)

theorem IsTorusPtF.gtSmul {g : GtPtF D F} {t : D.X → F} (h : IsTorusPtF g t) (a : O) :
    IsTorusPtF (gtSmul hG oa a g) fun χ => t (star a • χ) := by
  have := oa.onB.hom a
  obtain ⟨b, v⟩ := (isTorusPtF_iff_val _ _).1 h
  refine (isTorusPtF_iff_val _ _).2 ⟨by rw [gtSmul_b, b, MonObj.one_comp], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := (rosGen_add hG oa a hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  rw [gtSmul_val hG oa a g χ hJ, b, mul_eq_left.1 e.symm, _root_.mul_one]
  exact v _ y J hJ

include hG in
theorem IsTorusPtF.gtAct_iff {g : GtPtF D F} {t : D.X → F} (h : IsTorusPtF g t) (a : O) (g' : GtPtF D F) :
    GtAct oa a g g' ↔ IsTorusPtF g' fun χ => t (star a • χ) :=
  (gtAct_iff_eq_gtSmul hG oa a g g').trans ⟨fun e => e ▸ h.gtSmul hG oa a, fun e => e.unique (h.gtSmul hG oa a)⟩

end Action

theorem exists_lift (b : TF (R := R) F ⟶ D.P.A) : ∃ g : GtPtF D F, g.b = b := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have hc : IsSymmCocycle fun χ χ' : D.X => th D y J (cP D _ χ) (cP D _ χ') b :=
    ⟨fun χ => by rw [cPoint_zero, C.face], fun _ _ => C.s01 _ _ _, fun _ _ _ => by rw [cPoint_add, cPoint_add, C.coc]⟩
  obtain ⟨f, f₀, hf⟩ := hc.exists_coboundary
  choose v hv vv using fun χ => exists_gen_val (F := F) D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (f χ)
  refine (exists_gt b v hv (fun _ _ _ _ => rfl) (fun y' J' hJ' => ?_) (fun χ χ' y' J' hJ' => ?_)).imp fun _ h => h.1
  · obtain rfl := pt_eq y y'
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) (hv 0) oneGen_isGen hJ hJ'
      ((vv 0).trans (f₀.trans (val_one _).symm))).trans (val_one _)
    rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · obtain rfl := pt_eq y y'
    refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ' _ _ _))).symm.trans
      (Eq.trans (val_eq_of_val_eq (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hv _) (cubAt_isGen _ _ _))
        (mulGen_isGen _ _ _ _ _ _ _ (hv χ) (hv χ')) hJ hJ'
        (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (val_cubAt hJ _ _ _))).trans ((hf χ χ').trans
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (vv _))).symm))) (val_mul hJ' _ _ _))
    refine (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gt b (χ + χ') h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem gtProj_surjective : Function.Surjective (gtProj D F) := fun b =>
  (exists_lift b.toMul).imp fun _ h => congrArg Additive.ofMul h

section Divisible

variable [IsAlgClosed F] {n : ℕ}

theorem exists_nsmul_eq_of_pow_eq (hn : n ≠ 0) (h : GtPtF D F) {b : TF (R := R) F ⟶ D.P.A} (hb : b ^ n = h.b) :
    ∃ g : GtPtF D F, g.b = b ∧ n • g = h := by
  obtain ⟨g₁, rfl⟩ := exists_lift b
  obtain ⟨t, ht⟩ := exists_torusPt_eq (g := h + -(n • g₁)) (by rw [add_b, neg_b, nsmul_b, hb, mul_inv_cancel])
  obtain ⟨s, rfl⟩ := exists_pow_eq_hom hn t
  refine ⟨g₁ + torusPt D F (Additive.ofMul s), by rw [add_b, torusPt_b, _root_.mul_one], ?_⟩
  rw [nsmul_add, ← map_nsmul, ← ofMul_pow, ← ht]
  abel

theorem exists_pow_eq (hM : MulNSt) (hR : IsNoetherianRing R ∨ PolBaseChangeSt) (hn : n ≠ 0)
    (a : TF (R := R) F ⟶ D.P.A) : ∃ b : TF (R := R) F ⟶ D.P.A, b ^ n = a :=
  hR.elim (fun _ => exists_pow_eq_of_noetherian _ hM D.P hn a) fun hP => exists_pow_eq_of_baseChange _ hM hP D.P hn a

theorem exists_nsmul_eq (hM : MulNSt) (hR : IsNoetherianRing R ∨ PolBaseChangeSt) (hn : n ≠ 0) (h : GtPtF D F) :
    ∃ g : GtPtF D F, n • g = h := by
  obtain ⟨b, hb⟩ := exists_pow_eq hM hR hn h.b
  exact (exists_nsmul_eq_of_pow_eq hn h hb).imp fun _ e => e.2

theorem exists_qkPt_of_pow_eq (hB : D.TauBimult) (hn : n ≠ 0) (y : D.X) {b : TF (R := R) F ⟶ D.P.A}
    (hb : b ^ n = DegPre.cF D F y) : ∃ q : QkPt D F n, q.y = y ∧ q.g.b = b := by
  obtain ⟨g, e, h⟩ := exists_nsmul_eq_of_pow_eq hn (iota hB F y) (hb.trans (iota_b hB y).symm)
  exact ⟨qkMk hB y g h, rfl, e⟩

theorem exists_qkPt_of_torsion (hB : D.TauBimult) (hn : n ≠ 0) {b : TF (R := R) F ⟶ D.P.A} (hb : b ^ n = 1) :
    ∃ q : QkPt D F n, q.y = 0 ∧ q.g.b = b := exists_qkPt_of_pow_eq hB hn 0 (hb.trans (cPoint_zero _).symm)

theorem exists_qkPt (hM : MulNSt) (hR : IsNoetherianRing R ∨ PolBaseChangeSt) (hB : D.TauBimult) (hn : n ≠ 0)
    (y : D.X) : ∃ q : QkPt D F n, q.y = y := by
  obtain ⟨g, h⟩ := exists_nsmul_eq hM hR hn (iota hB F y)
  exact ⟨qkMk hB y g h, rfl⟩

end Divisible

theorem torus_lift_divisible (hG : GlobalFnsSt) (hM : MulNSt) {R : Type} [CommRing R] [IsDomain R]
    (hR : IsNoetherianRing R ∨ PolBaseChangeSt) (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] :
    ((∀ t : Multiplicative D.X →* Fˣ, ∃! g : GtPtF D F, IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ)) ∧
      (∀ (g : GtPtF D F) (t t' : D.X → F), IsTorusPtF g t → IsTorusPtF g t' → t = t') ∧
      (∀ (g g' g'' : GtPtF D F) (t t' : D.X → F), IsTorusPtF g t → IsTorusPtF g' t' →
        (g.IsAdd g' g'' ↔ IsTorusPtF g'' (t * t'))) ∧
      (∀ g : GtPtF D F, g.b = DegPre.zeroF D F →
        ∃ t : Multiplicative D.X →* Fˣ, IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ)) ∧
      ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) (g g' : GtPtF D F) (t : D.X → F),
        IsTorusPtF g t → (GtAct oa a g g' ↔ IsTorusPtF g' fun χ => t (star a • χ))) ∧
    (∀ b : TF (R := R) F ⟶ D.P.A, ∃ g : GtPtF D F, g.b = b) ∧
    ∀ n : ℕ, n ≠ 0 → (∀ h : GtPtF D F, ∃ g, GtPtF.IsNsmul n g h) ∧ (∀ y : D.X, ∃ q : QkPt D F n, q.y = y) ∧
      ∀ b : TF (R := R) F ⟶ D.P.A, b ^ n = 1 → ∃ q : QkPt D F n, q.y = 0 ∧ q.g.b = b :=
  ⟨⟨fun t => ⟨_, isTorusPtF_torusPt t, fun g h => (isTorusPtF_iff_eq g t).1 h⟩, fun _ _ _ => IsTorusPtF.fun_unique,
      fun _ _ _ _ _ h h' => (isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ h.add h', fun e => e.unique (h.add h')⟩,
      fun _ => exists_isTorusPtF_of_b, fun _ _ _ _ oa a _ g' _ h => h.gtAct_iff hG oa a g'⟩, exists_lift,
    fun _ hn => ⟨fun h => (exists_nsmul_eq hM hR hn h).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm,
      exists_qkPt hM hR hB hn, fun _ => exists_qkPt_of_torsion hB hn⟩⟩

end GlobalTheory.TorusExt
