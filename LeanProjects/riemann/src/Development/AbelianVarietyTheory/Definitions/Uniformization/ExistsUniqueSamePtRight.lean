import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelModel

theorem finExt_self (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [h : IsAdicComplete (IsLocalRing.maximalIdeal V) V] : FinExt V V :=
  ⟨inferInstance, inferInstance, inferInstance, ⟨fun _ h => h⟩, by
    rw [Algebra.algebraMap_self, Ideal.map_id]; exact h⟩

theorem cdvr_padicInt (p : ℕ) [Fact p.Prime] : CDVR ℤ_[p] := ⟨inferInstance, inferInstance, inferInstance⟩

example (p : ℕ) [Fact p.Prime] : FinExt ℤ_[p] ℤ_[p] := finExt_self _

theorem not_finExt_padic (p : ℕ) [Fact p.Prime] : ¬ FinExt ℤ_[p] ℚ_[p] := fun h => by
  have := h.2.2.2.1.map_nonunit (p : ℤ_[p]) (IsUnit.mk0 _ (by simpa using (Fact.out : p.Prime).ne_zero))
  exact PadicInt.irreducible_p.not_isUnit this

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem existsUnique_samePt_right (U : PreU I D A G) (x : TFK (R := R) F ⟶ A.A) : ∃! y, U.SamePt x y := by
  refine ⟨Over.homMk (x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ?_, rfl, fun y h => Over.OverMorphism.ext h.symm⟩
  have a : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
  have b : x.left ≫ A.A.hom = jFK (R := R) F := Over.w x
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc U.gen.inv.left, a, ← Category.assoc, b]; rfl

theorem existsUnique_samePt_left (U : PreU I D A G) (y : TF (R := R) F ⟶ G) : ∃! x, U.SamePt x y := by
  let l : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift y.left (jFK (R := R) F) (Over.w y)) (pullback.lift_snd _ _ _)
  have e : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id]; rfl
  refine ⟨l ≫ U.gen.hom, ?_, fun x h => ?_⟩
  · show (l.left ≫ U.gen.hom.left) ≫ _ = _
    rw [Category.assoc, ← Category.assoc U.gen.hom.left, e, Category.id_comp]
    exact pullback.lift_fst _ _ _
  · rw [← Iso.comp_inv_eq]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · exact ((Category.assoc _ _ _).trans h).trans (pullback.lift_fst _ _ _).symm
    · exact (Over.w (x ≫ U.gen.inv)).trans (pullback.lift_snd _ _ _).symm

theorem pullB_unique {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α)
    {s s' : Raw D F k} (h : PullB D F φ k f s) (h' : PullB D F φ k f s') (α j) : (s α).f j = (s' α).f j :=
  sec_ext_val D.P.isLB (fun y J hJ => (h α y J hJ).trans (h' α y J hJ).symm) j

theorem pullB_id (k : ℕ) (s : Raw D F k) : PullB D F (𝟙 _) k s s := fun α z J _ => by
  rw [MonoidalCategory.id_whiskerRight]; rfl

theorem gtTors_zero {g h : GtPtF D F} (hz : h.IsZero) : GtTors D 0 g :=
  ⟨h, ⟨fun _ => h, hz, fun i => i.elim0, rfl⟩, hz⟩

theorem gtTors_one {g : GtPtF D F} (h : GtTors D 1 g) : g.b = 1 := by
  obtain ⟨h, ⟨gs, h0, hs, rfl⟩, hz⟩ := h
  have a := (hs 0).1
  have b : (gs 0).b = 1 := h0.1
  have c : (gs (Fin.last 1)).b = 1 := hz.1
  have d : (gs (Fin.last 1)).b = (gs 0).b * g.b := a
  rw [b, c, _root_.one_mul] at d
  exact d.symm

theorem add_formEq (a b : D.X) (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k, h (addφ D a b k) ^ addε k =
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a + b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) (a - b) k) ^ DegPre.famε 2 k) *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * snd D.P.A D.P.A)).left ≫ famφT D (𝟙_ _) a k) ^ DegPre.famε 1 k)⁻¹ *
      (∏ k, h ((lift (toUnit _) (fst D.P.A D.P.A * (snd D.P.A D.P.A)⁻¹)).left ≫ famφT D (𝟙_ _) b k) ^ DegPre.famε 1 k)⁻¹ := by
  have key : ∀ (p : D.P.A ⊗ D.P.A ⟶ D.P.A) (χ : D.X) (n : ℕ),
      ∏ k, h ((lift (toUnit _) p).left ≫ famφT D (𝟙_ _) χ k) ^ DegPre.famε n k =
        h p.left ^ ((n : ℤ) - 1) * h (p * (toUnit _ ≫ D.c χ)).left * (h (toUnit _ ≫ D.c χ).left)⁻¹ *
          h (toUnit (D.P.A ⊗ D.P.A) ≫ η[D.P.A]).left := fun p χ n => by
    have e1 : lift (toUnit _) p ≫ snd (𝟙_ _) D.P.A = p := lift_snd _ _
    have e3 : ∀ q : 𝟙_ _ ⟶ D.P.A, lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ q = toUnit _ ≫ q := fun q => by
      rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    have e2 : lift (toUnit _) p ≫ padd D.P.A (snd (𝟙_ _) D.P.A) (toUnit _ ≫ D.c χ) = p * (toUnit _ ≫ D.c χ) := by
      show _ ≫ (snd (𝟙_ _) D.P.A * (toUnit _ ≫ D.c χ)) = _
      rw [MonObj.comp_mul, e1, e3]
    rw [Fin.prod_univ_four]
    show h (lift (toUnit _) p ≫ snd (𝟙_ _) D.P.A).left ^ ((n : ℤ) - 1) *
      h (lift (toUnit _) p ≫ padd D.P.A (snd (𝟙_ _) D.P.A) (toUnit _ ≫ D.c χ)).left ^ (1 : ℤ) *
      h (lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ D.c χ).left ^ (-1 : ℤ) *
      h (lift (toUnit _) p ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [e1, e2, e3, e3, zpow_one, zpow_one, zpow_neg_one]
  rw [key, key, key, key]
  simp only [Fin.prod_univ_succ, addφ, addε, Matrix.cons_val_zero, Matrix.cons_val_succ, Finset.univ_eq_empty,
    Finset.prod_empty, Fin.prod_univ_zero]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
  norm_num
  abel
end

example (x y a b : ℤ) : ∑ k, addε k * (![x, x + (a + b), a + b, y, y + (a - b), a - b, x + y + a, a, x - y + b, b] k) ^ 2 = 0 := by
  simp [Fin.sum_univ_succ, addε]; ring

open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate in

def zeroU (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : PreU I (zeroData R I).toPre
    (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_unit _)
  gen := (zeroPre R I).gen
  gen_hom := (zeroPre R I).gen_hom
  P := CP.triv _
  wA := ⟨fun _ => 1⟩
  wA_gen := one_isGen_div _ _ _ _
  gt := zeroGt R I
  gt_q := (zeroPre R I).gt_q
  gt_t := (zeroPre R I).gt_t
  w := fun _ => ⟨fun _ => 1⟩
  w_gen := fun _ => one_isGen_div _ _ _ _
  w_vals := fun e T z JG J _ _ W hW => by
    have a : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
    have g1 : ∀ {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens), gm r z V (gv 1 V) = 1 := fun r z V => by
      rw [gv_one, map_one]
    refine ⟨(g1 _ _ _).trans ?_, fun x => ?_, fun x y u => ?_⟩
    · rw [a, _root_.one_mul]; exact (val_unitGen _ _ _ _ _).symm
    · rw [a, a, val_sym_triv, _root_.mul_one, _root_.mul_one]; exact g1 _ _ _
    · simp only [a, _root_.mul_one, _root_.one_mul]
      exact (g1 _ _ _).trans (val_unitGen _ _ _ _ _).symm
  w_compat := fun e Z x z j k _ _ => (map_one _).trans (map_one _).symm

theorem not_allPre_false : ¬ AllPre fun _ => False := fun h =>
  h ℤ_[2] (cdvr_padicInt 2) _ _ _ (zeroU ℤ_[2] _)

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pullG_unique (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ)
    (σ : U.SecGT T k) {t t'} (h : U.PullG F φ k σ t) (h' : U.PullG F φ k σ t') (j) : t.f j = t'.f j := by
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
    A.isLB (fun z JA hA => ?_) j
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  let y : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left := (snd (TFK (R := R) F) A.A ≫ U.gen.inv).left
  have w : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have a : y ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F ⊗ A.A).hom := Over.w (snd (TFK (R := R) F) A.A ≫ U.gen.inv)
    have b : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (TFK (R := R) F ⊗ A.A).hom := Over.w (fst (TFK (R := R) F) A.A)
    have c : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    rw [Category.assoc y, pullback.condition, ← Category.assoc y, a, ← b, Category.assoc, Category.assoc]
    exact congrArg _ c
  let rG : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ w
  have e1 : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y ≫ U.gen.hom.left := by
    rw [Category.id_comp, ← Over.comp_left, Category.assoc, U.gen.inv_hom_id, Category.comp_id]
  have e2 : rG ≫ (snd T G).left = y ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  have e3 : rG ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left :=
    (pullback.lift_fst _ _ _).trans (Category.id_comp _).symm
  have := (h _ _ y rG e1 e2 e3 z JA JG hA hG).trans (h' _ _ y rG e1 e2 e3 z JA JG hA hG).symm
  exact ((Units.isUnit _).pow k).mul_left_cancel this
end

theorem exists_finExt_proper (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (h : CDVR V) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W), FinExt V W ∧
      ¬ Function.Surjective (algebraMap V W) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap V (Kbar V) p) two_pos
  have inj : Function.Injective (algebraMap V (Kbar V)) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) (Kbar V)]
    exact (algebraMap (FractionRing V) (Kbar V)).injective.comp (IsFractionRing.injective V _)
  have : FaithfulSMul V (Kbar V) := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  have : Algebra.IsAlgebraic V (FractionRing V) := IsLocalization.isAlgebraic _ (nonZeroDivisors V)
  have : Algebra.IsAlgebraic V (Kbar V) := Algebra.IsAlgebraic.trans V (FractionRing V) (Kbar V)
  obtain ⟨W, hW, -, c, f, fr, l, -, hi⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V (Kbar V) {x}
  have xi : IsIntegral V x := IsIntegral.of_pow two_pos (hx ▸ isIntegral_algebraMap)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ⟨f, fr, inferInstance, l, c⟩, fun s => ?_⟩
  obtain ⟨a, ha⟩ := s ⟨x, hi x (Finset.mem_singleton_self x) xi⟩
  have e : algebraMap V (Kbar V) a = x := congrArg Subtype.val ha
  have e2 : p = a * a := inj (by rw [← hx, map_mul, e, pow_two])
  exact hp.not_isUnit (e2 ▸ ((hp.isUnit_or_isUnit e2).elim (fun u => u.mul u) fun u => u.mul u))

section
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem sval_cs_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (J) : sval (cs φ ε 1) r z J = 1 := by
  have hm : r z ∈ LB.wchart (trivLB X) φ (fun k => J (r ≫ φ k)) := by rw [GlobalTheory.ToricData.wchart_triv]; trivial
  refine (gs_eq r z _ hm _).trans ?_
  simp only [cs, resTop, map_one]
  erw [map_one, map_one]

variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expF_one : (zeroU R I).ExpF F k (cs _ _ 1) (fun _ => cs _ _ 1) := by
  have g : ∀ {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : Y ⟶ Spec (CommRingCat.of F)), gs r z ⊤ (scal p 1) = 1 :=
    fun r z p => by rw [gs_eq r z ⊤ trivial]; simp only [scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => cs _ _ 1, fun _ _ => cs _ _ 1, fun _ e => ⟨{PUnit.unit}, ?_⟩, ?_, ?_⟩
  · intro Z x rG rB _ _ _ z JG J _ _
    refine ⟨fun α hα => (hα (Finset.mem_singleton_self _)).elim, ?_⟩
    have a : gw ((zeroU R I).w e) x z (J (x ≫ ((zeroU R I).gt e).pG.left)) (fun _ => JG (x ≫ (fstG I e _).left)) = 1 :=
      map_one _
    have b : val (((zeroU R I).gt e).t PUnit.unit) x z J = 1 := (congrArg _ (gv_one _)).trans (map_one _)
    rw [a]
    erw [Finset.sum_singleton, b, sval_cs_one, sval_cs_one]
    simp
  · intro Z rA y rG _ _ z JA JG _ _
    have a : gw (zeroU R I).wA y z (JG (y ≫ pullback.fst _ (jK R))) (fun _ => JA (y ≫ (zeroU R I).gen.hom.left)) = 1 :=
      map_one _
    rw [a, Fin.sum_univ_one, g]
    erw [sval_cs_one, sval_cs_one]
    simp
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_one, g]
    erw [sval_cs_one, sval_cs_one]
    simp

theorem supp_zeroU : (zeroU R I).Supp F k PUnit.unit := by
  refine ⟨_, _, expF_one R I F k, fun _ => PUnit.unit, fun h => ?_⟩
  have : IsIso (fst (TF (R := R) F) (zeroData R I).toPre.P.A).left :=
    (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have e := resTop_inj (GlobalTheory.ToricData.wchart_triv _ _) (h.trans (map_zero _).symm)
  refine one_ne_zero ((scal_bijective (fst (TF (R := R) F) (zeroData R I).toPre.P.A).left).1 (?_ : _ = scal _ (0 : F)))
  rw [scal_zero]
  exact (show scal _ (1 : F) = 1 by simp only [scal, map_one]).trans e

theorem pullG_one {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) :
    (zeroU R I).PullG F φ k (cs _ _ 1) (cs _ _ 1) := by
  intro Z rA y rG _ _ _ z JA JG _ _
  have a : gw (zeroU R I).wA y z (JG (y ≫ pullback.fst _ (jK R))) (fun _ => JA (y ≫ (zeroU R I).gen.hom.left)) = 1 :=
    map_one _
  rw [a]
  erw [sval_cs_one, sval_cs_one]
  simp
end

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem acts_iff_qkToAk (U : PreU I D A G) {k : ℕ} (h : U.FE F k) (p : QkPt D F k) (x : TFK (R := R) F ⟶ A.A) :
    U.Acts F k p.y p.g x ↔ QkToAk D F A k (fun t s => U.ExpF F k t s.s) p x :=
  and_congr_right fun _ => forall₂_congr fun θ _ => exists_congr fun w => and_congr_right fun _ =>
    ⟨fun H t t' s s' a b c => H t t' s.s s'.s a b c,
      fun H t t' s s' a b c => H t t' ⟨s, h t s a⟩ ⟨s', h t' s' b⟩ a b c⟩

theorem samePt_mul (U : PreU I D A G) {x x' : TFK (R := R) F ⟶ A.A} {y y' : TF (R := R) F ⟶ G}
    (h : U.SamePt x y) (h' : U.SamePt x' y') : U.SamePt (x * x') (y * y') := by
  have := U.gen_hom
  have e := (isGrpPullback_pullback G (jK R)).2 _ (x ≫ U.gen.inv) (x' ≫ U.gen.inv) y y'
    (h.symm.trans (Category.assoc _ _ _).symm) (h'.symm.trans (Category.assoc _ _ _).symm)
  rw [← MonObj.mul_comp] at e
  exact (Category.assoc _ _ _).symm.trans e.symm
end

section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

def zeroUq (q : (FractionRing R)ˣ) : PreU I (toricPre R PUnit fun _ => q)
    (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  semi := (zeroU R I).semi
  gen := (zeroU R I).gen
  gen_hom := (zeroU R I).gen_hom
  P := (zeroU R I).P
  wA := (zeroU R I).wA
  wA_gen := (zeroU R I).wA_gen
  gt e := let g := zeroGt R I e
    { q := g.q, q_hom := g.q_hom, q_flat := g.q_flat, q_surj := g.q_surj, q_affine := g.q_affine, i := g.i
      i_hom := g.i_hom, isKernel := g.isKernel, t := g.t, t_gen := g.t_gen, t_mul := g.t_mul, t_unit := g.t_unit
      t_weight := g.t_weight }
  gt_q := (zeroU R I).gt_q
  gt_t := (zeroU R I).gt_t
  w := (zeroU R I).w
  w_gen := (zeroU R I).w_gen
  w_vals := (zeroU R I).w_vals
  w_compat := (zeroU R I).w_compat

theorem fe_zeroUq_iff (q : (FractionRing R)ˣ) : (zeroUq R I q).FE F (k + 1) ↔ q ^ k = 1 := by
  have hf : (DegPre.zF (toricPre R PUnit fun _ => q) F).left ≫
      (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left = 𝟙 _ :=
    congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[(toricPre R PUnit fun _ => q).P.A]))
  have hi : IsIso (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left :=
    (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have hz : IsIso (DegPre.zF (toricPre R PUnit fun _ => q) F).left := IsIso.of_isIso_fac_right hf
  have ht : ∀ mu, DegPre.trF (toricPre R PUnit fun _ => q) F mu = 𝟙 _ := fun mu =>
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  have hm : ∀ mu α, IsConst (DegPre.famMult (toricPre R PUnit fun _ => q) F (k + 1) mu α)
      (pullTop (jFK (R := R) F) (unitOn (q ^ k))) := fun mu α =>
    (isConst_pullGen (isConst_mulGen (isConst_mulGen (isConst_powGen (psi_isConst _ mu) (k + 1))
      (tau_isConst _ mu α)) (isConst_powGen (rigK_isConst _) (k + 1))) _).of_eq (by
        congr 1
        rw [one_pow, _root_.mul_one, ← unitOn_pow, ← unitOn_mul]
        congr 1
        show q ^ (k + 1) * (q * q⁻¹ * q⁻¹) = _
        group)
  constructor
  · intro h
    let v := pullTop (fst (TF (R := R) F) (toricPre R PUnit fun _ => q).P.A).left (pullTop (jFK (R := R) F) (unitOn (q ^ k)))
    have hv : pullTop (DegPre.zF (toricPre R PUnit fun _ => q) F).left v = pullTop (jFK (R := R) F) (unitOn (q ^ k)) := by
      ext
      exact congrArg (fun f => f.appTop.hom (pullTop (jFK (R := R) F) (unitOn (q ^ k))).val) hf
    have H := h _ _ (expF_one R I F (k + 1)) PUnit.unit PUnit.unit (cg _ _ v) (cg_isGen _ _ _)
      (corr_of_isConst ((isConst_pullGen (cg_isConst _ _ v) _).of_eq hv) (hm _ _))
    have v1 : v = 1 := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt (toricPre R PUnit fun _ => q).P.isLB z
      have e := (secRel_iff (toricPre R PUnit fun _ => q).P.isLB _ _ _ _ _ _ _ _ _ _).1 H _ (𝟙 _) z J hJ
      erw [sval_cs_one, sval_cs_one, _root_.one_mul] at e
      rw [map_one]
      exact (gm_res _ z _ (hJ.mem _ _) v).symm.trans (Units.ext e.symm)
    rw [v1, map_one, pullTop_unitOn, ← unitOn_one, unitOn_inj] at hv
    exact Units.map_injective (algebraMap (FractionRing R) F).injective (hv.symm.trans (map_one _).symm)
  · intro h t s _ mu α u _ hu
    obtain ⟨v, hv⟩ := exists_isConst u
    obtain ⟨c, hc⟩ := exists_secConst (s α)
    have hv1 : v = 1 := pullTop_injective (DegPre.zF (toricPre R PUnit fun _ => q) F).left
      ((eq_of_corr (isConst_pullGen hv _) (hm mu α) hu).trans (by rw [h, unitOn_one, map_one, map_one]))
    refine secRel_of hc hc _ (hv.of_eq hv1) ?_
    rw [ht, Over.id_left, Scheme.Hom.id_appTop]
    rfl
end

section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem sval_const {X Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb (trivLB X) φ ε)} {B : Type} [CommRing B] {p : Y ⟶ Spec (CommRingCat.of B)} {a : B}
    (h : SecConst s (scal p a)) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = gs (𝟙 Z) z ⊤ (scal (r ≫ p) a) := by
  have hm : r z ∈ LB.wchart (trivLB X) φ (fun k => J (r ≫ φ k)) := by rw [GlobalTheory.ToricData.wchart_triv]; trivial
  refine (congrArg (gs r z _) (h _)).trans ((gs_res r z le_top hm _).trans ?_)
  rw [← appTop_scal]
  exact ((gs_pull (𝟙 Z) r z ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem gs_scal {Y Z : Scheme.{0}} {B : Type} [CommRing B] (p : Y ⟶ Spec (CommRingCat.of B)) (a : B)
    (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (scal p a) = gs (𝟙 Z) z ⊤ (scal (r ≫ p) a) := by
  rw [← appTop_scal]
  exact ((gs_pull (𝟙 Z) r z ⊤ trivial _).trans (by rw [Category.id_comp])).symm

variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expT_zeroU [IsHausdorff I R] {σ : (zeroU R I).SecGT (𝟙_ _) k} {f} (h : (zeroU R I).ExpT (𝟙_ _) k σ f) {a b : R}
    (ha : SecConst σ (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a))
    (hb : SecConst (f PUnit.unit) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left b)) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := I) _ fun e => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ((scal_bijective (𝟙 _)).1 ?_))
  rw [← scal_specMap, ← scal_specMap, Category.id_comp]
  refine fn_ext fun z _ => ?_
  obtain ⟨s, hs⟩ := h e
  let x : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e (𝟙_ _)).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  let r : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (𝟙_ _ ⊗ 𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    pullback.lift (thick R I e) (thick R I e) rfl
  have hr : r ≫ (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left = thick R I e := pullback.lift_snd _ _ _
  have hx : x ≫ (fstG I e (𝟙_ _)).left = thick R I e := pullback.lift_fst _ _ _
  have hx' : x ≫ ((zeroU R I).gt e).pG.left = thick R I e :=
    (congrArg (x ≫ ·) (zeroGt_pG R I e)).trans (pullback.lift_fst _ _ _)
  obtain ⟨h₁, h₂⟩ := hs _ x r r (hr.trans hx.symm) (hr.trans hx'.symm) rfl z (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ => trivial) (fun _ => trivial)
  have w1 : gw ((zeroU R I).w e) x z PUnit.unit (fun _ => PUnit.unit) = 1 := map_one _
  have t1 : val (((zeroU R I).gt e).t PUnit.unit) x z (fun _ => PUnit.unit) = 1 :=
    (congrArg _ (gv_one _)).trans (map_one _)
  have va := sval_const ha r z (fun _ => PUnit.unit)
  have vb := sval_const hb r z (fun _ => PUnit.unit)
  erw [hr] at va vb
  refine va.symm.trans (Eq.trans ?_ vb)
  erw [w1, Units.val_one, one_pow, _root_.one_mul] at h₂
  refine h₂.trans ((Finset.sum_eq_single PUnit.unit (fun _ _ hb => absurd rfl hb) fun hn => ?_).trans ?_)
  · erw [h₁ _ hn, zero_mul]
  · exact (congrArg (_ * Units.val ·) t1).trans (_root_.mul_one _)

theorem expF_zeroU [IsHausdorff I R] {t s} (h : (zeroU R I).ExpF F k t s) {a b : F}
    (ha : SecConst t (scal (fst (TFK (R := R) F) (𝟙_ _)).left a))
    (hb : SecConst (s PUnit.unit) (scal (fst (TF (R := R) F) (𝟙_ _)).left b)) : a = b := by
  obtain ⟨n, c, σ, f, h₁, h₂, h₃⟩ := h
  have hi : IsIso (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left :=
    (inferInstance : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (𝟙 _)))
  have hσ : ∀ i, ∃ a, SecConst (σ i) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a) := fun i => by
    obtain ⟨a', ha⟩ := exists_secConst (σ i)
    obtain ⟨a, rfl⟩ := (scal_bijective (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left).2 a'
    exact ⟨a, ha⟩
  have hf : ∀ i, ∃ a, SecConst (f i PUnit.unit) (scal (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left a) :=
    fun i => by
    obtain ⟨a', ha⟩ := exists_secConst (f i PUnit.unit)
    obtain ⟨a, rfl⟩ := (scal_bijective (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left).2 a'
    exact ⟨a, ha⟩
  choose p hp using hσ
  choose p' hp' using hf
  obtain rfl : p = p' := funext fun i => expT_zeroU R I k (h₁ i) (hp i) (hp' i)
  refine (scal_bijective (𝟙 _)).1 (fn_ext fun z _ => ?_)
  let j := jFK (R := R) F
  let rA : Spec (CommRingCat.of F) ⟶ (TFK (R := R) F ⊗ 𝟙_ _).left := pullback.lift (𝟙 _) j (by simp [j])
  let rF : Spec (CommRingCat.of F) ⟶ (TF (R := R) F ⊗ 𝟙_ _).left := pullback.lift (𝟙 _) (j ≫ jK R) (by simp [j])
  let y : Spec (CommRingCat.of F) ⟶ ((Over.pullback (jK R)).obj (𝟙_ _)).left := pullback.lift (j ≫ jK R) j (by simp)
  let r : Spec (CommRingCat.of F) ⟶ (𝟙_ _ ⊗ 𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    pullback.lift (j ≫ jK R) (j ≫ jK R) rfl
  have hr : r ≫ (snd (𝟙_ _) (𝟙_ (Over (Spec (CommRingCat.of R))))).left = j ≫ jK R := pullback.lift_snd _ _ _
  have hA : rA ≫ (fst (TFK (R := R) F) (𝟙_ _)).left = 𝟙 _ := pullback.lift_fst _ _ _
  have hF : rF ≫ (fst (TF (R := R) F) (𝟙_ _)).left = 𝟙 _ := pullback.lift_fst _ _ _
  have g : (zeroU R I).gen.hom.left = pullback.snd _ _ :=
    (Category.comp_id _).symm.trans (Over.w (zeroU R I).gen.hom)
  have e₂ := h₂ _ rA y r ((pullback.lift_snd _ _ _).trans ((congrArg (y ≫ ·) g).trans (pullback.lift_snd _ _ _)).symm)
    (hr.trans (pullback.lift_fst _ _ _).symm) z (fun _ => PUnit.unit) (fun _ => PUnit.unit)
    (fun _ => trivial) (fun _ => trivial)
  have e₃ := h₃ PUnit.unit _ rF r (hr.trans (pullback.lift_snd _ _ _).symm) z (fun _ => PUnit.unit) (fun _ => trivial)
  have w1 : gw (zeroU R I).wA y z PUnit.unit (fun _ => PUnit.unit) = 1 := map_one _
  erw [w1, Units.val_one, one_pow, _root_.one_mul] at e₂
  have va := sval_const ha rA z (fun _ => PUnit.unit)
  have vb := sval_const hb rF z (fun _ => PUnit.unit)
  erw [hA] at va
  erw [hF] at vb
  refine va.symm.trans (e₂.trans (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (e₃.symm.trans vb)))
  refine congrArg₂ (· * ·) ?_ ((sval_const (hp i) r z _).trans (sval_const (hp' i) r z _).symm)
  refine (gs_scal _ _ rA z).trans (Eq.trans ?_ (gs_scal _ _ rF z).symm)
  exact (congrArg (fun q => gs (𝟙 _) z ⊤ (scal q (c i))) hA).trans (congrArg (fun q => gs (𝟙 _) z ⊤ (scal q (c i))) hF).symm
end

section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem acts_zeroU [IsHausdorff I R] (g : GtPtF (zeroData R I).toPre F) : (zeroU R I).Acts F k PUnit.unit g 1 := by
  refine ⟨one_pow k, fun θ _ => ?_⟩
  let pA : (TFK (R := R) F ⊗ (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))).A).left ⟶ Spec (CommRingCat.of F) :=
    (fst (TFK (R := R) F) (𝟙_ _)).left
  let pB : (DegPre.BF (zeroData R I).toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) (𝟙_ _)).left
  have iA : IsIso pA := (inferInstance : IsIso (pullback.fst (TFK (R := R) F).hom (𝟙 _)))
  have iB : IsIso pB := (inferInstance : IsIso (pullback.fst (TF (R := R) F).hom (𝟙 _)))
  have hf : (DegPre.zF (zeroData R I).toPre F).left ≫ pB = 𝟙 _ :=
    congrArg Over.Hom.left (lift_fst (𝟙 (TF (R := R) F)) (toUnit _ ≫ η[(zeroData R I).toPre.P.A]))
  have hz : IsIso (DegPre.zF (zeroData R I).toPre F).left := IsIso.of_isIso_fac_right hf
  have tB : DegPre.trPt (zeroData R I).toPre F g.b = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  have tA : translT _ θ.pt = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Category.id_comp _).symm) (toUnit_unique _ _)
  obtain ⟨v, hv⟩ := exists_isConst θ.φ
  obtain ⟨a, ha⟩ := (scal_bijective pA).2 v.val
  have a0 : a ≠ 0 := by
    rintro rfl
    have : (1 : F) = 0 := (scal_bijective pA).1 (by
      have : scal pA (1 : F) = 1 := by simp only [scal, map_one]
      rw [this, ← v.mul_inv, ← ha, scal_zero, zero_mul])
    exact one_ne_zero this
  obtain ⟨ga, hga⟩ := exists_isConst (g.s PUnit.unit)
  have ga1 : ga = 1 := eq_of_corr hga (isConst_oneGen _) g.s_zero
  refine ⟨cg _ _ (unitOn (Units.mk0 a a0)), cg_isGen _ _ _, fun t t' s s' e e' act α u _ hu => ?_⟩
  obtain ⟨x₀, hx⟩ := exists_secConst t
  obtain ⟨x, rfl⟩ := (scal_bijective pA).2 x₀
  obtain ⟨x₀', hx'⟩ := exists_secConst t'
  obtain ⟨x', rfl⟩ := (scal_bijective pA).2 x₀'
  obtain ⟨y₀, hy⟩ := exists_secConst (s PUnit.unit)
  obtain ⟨y, rfl⟩ := (scal_bijective pB).2 y₀
  obtain ⟨y₀', hy'⟩ := exists_secConst (s' PUnit.unit)
  obtain ⟨y', rfl⟩ := (scal_bijective pB).2 y₀'
  obtain rfl := expF_zeroU R I F k e hx hy
  obtain rfl := expF_zeroU R I F k e' hx' hy'
  have xx : x' = a * x := by
    have := act (fun _ => PUnit.unit)
    erw [hx, hx', hv, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, tA] at this
    refine (scal_bijective pA).1 (resTop_inj (wchart_triv _ _) (this.trans ?_))
    rw [scal_mul, resTop_mul, ha]
    rfl
  obtain ⟨b, hb⟩ := exists_isConst u
  have bb : b = pullTop pB (unitOn (Units.mk0 a a0)) := pullTop_injective (DegPre.zF (zeroData R I).toPre F).left (by
    refine (eq_of_corr (isConst_pullGen hb _) (isConst_mulGen (hga.of_eq ga1) (cg_isConst _ _ _)) hu).trans ?_
    rw [_root_.one_mul]
    ext
    exact (congrArg (fun f => f.appTop.hom (unitOn (Units.mk0 a a0)).val) hf).symm)
  intro j₁ j₂ j₃ _
  erw [hy, hy', hb, app_resTop, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, tB, xx, bb, scal_mul, resTop_mul, mul_comm]
  refine congrArg₂ (· * ·) rfl ?_
  exact (map_map _ _ _).symm
end

end GlobalTheory.UU.RelModel
end
