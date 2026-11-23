import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.KerMemAbLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Per

section Defs

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R))

abbrev cT (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def biφ (a b : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(cT D T (a + b)).left, (cT D T a).left, (cT D T b).left, (toUnit T ≫ η[D.P.A]).left]

abbrev BiGen (a b : D.X) : Type := LB.Gen (LB.LinComb D.P.L (biφ D T a b) Oinvε)

variable {D T}

structure IsBiTriv {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (e : ∀ a b, BiGen D T a b) : Prop where
  gen : ∀ a b, (e a b).IsGen
  symm : ∀ a b, LB.Gen.Corr D.P.L _ _ _ _ (e a b) (e b a)
  mul : ∀ a a' b, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (e (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (cT D T a) (lift (cT D T a') (cT D T b))).left))
    (LB.mulGen D.P.L _ _ _ _ (e a b) (e a' b))
  bal : ∀ (x : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act x) (oa.onB.act (star x))) rosatiε)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
    ∀ a b, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (e (x • a) b) (LB.pullGen D.P.L _ _ u (lift (cT D T a) (cT D T b)).left))
      (e a (star x • b))

def CoordAt (D : DegPre R) (χ : D.X) (i : D.P.L.ι) (r : R) : Prop :=
  ∃ (_ : (⊤ : (Sp R).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U i)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U fun _ => i),
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s fun _ => i).val

theorem psiCoord_iff (χ : D.X) (r : R) : PsiCoord D χ r ↔ ∃ i, CoordAt D χ i r :=
  ⟨fun ⟨j, h⟩ => ⟨j PUnit.unit, h⟩, fun ⟨i, h⟩ => ⟨fun _ => i, h⟩⟩

def rigAt (D : DegPre R) (i : D.P.L.ι) : R := valR (𝟙 (Sp R)) _ (D.rig.s fun _ => i).val

variable {C : Type} [NormedField C] [IsUltrametricDist C]

def IsTauVal (g : R →+* intO C) {a b : D.X} (e : BiGen D (Over.mk (spMap g)) a b) (t : C) : Prop :=
  ∀ (j : Fin 4 → D.P.L.ι) (r₁ r₂ r₃ : R), CoordAt D (a + b) (j 0) r₁ → CoordAt D a (j 1) r₂ → CoordAt D b (j 2) r₃ →
    ⊤ ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U (j 3) →
    (g r₁ : C) = t * (valR (𝟙 (Sp (intO C))) _ (e.s j).val : intO C) * g r₂ * g r₃ * g (rigAt D (j 3))

end Defs

section Rel

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def gen (V : Type) [CommRing V] [IsDomain V] : Sp V := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)

theorem gen_mem {U : (Sp V).Opens} {y : Sp V} (h : y ∈ U) : gen V ∈ U :=
  ((PrimeSpectrum.le_iff_specializes (gen V) y).1 bot_le).mem_open U.isOpen h

theorem jK_mem {U : (Sp R).Opens} {y : Sp R} (h : y ∈ U) : jK R (gen (FractionRing R)) ∈ U := by
  refine ((PrimeSpectrum.le_iff_specializes _ y).1 fun r hr => ?_).mem_open U.isOpen h
  have : algebraMap R (FractionRing R) r = 0 := hr
  rw [(IsFractionRing.to_map_eq_zero_iff).1 this]
  exact zero_mem _

theorem gm_inj {U : (Sp V).Opens} (h : gen V ∈ U) {a b : Γ(Sp V, U)ˣ}
    (e : gm (𝟙 (Sp V)) (gen V) U a = gm (𝟙 (Sp V)) (gen V) U b) : a = b := by
  have := congrArg Units.val e
  rw [gm_val _ _ U h, gm_val _ _ U h] at this
  exact Units.ext (germ_injective_of_isIntegral (Sp V) (U := U) (gen V) h this)

theorem gmK_inj {U : (Sp R).Opens} (h : jK R (gen (FractionRing R)) ∈ U) {a b : Γ(Sp R, U)ˣ}
    (e : gm (jK R) (gen _) U a = gm (jK R) (gen _) U b) : a = b := by
  have := congrArg Units.val e
  rw [gm_val _ _ U h, gm_val _ _ U h] at this
  have : IsDominant (jK R) := DVR.isDominant_jK
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  exact Units.ext ((jK R).app_injective U
    (germ_injective_of_isIntegral (Sp (FractionRing R)) (U := jK R ⁻¹ᵁ U) (gen _) h ‹_›))

def Rel (g : R →+* V) (x : ((Sp (FractionRing R)).presheaf.stalk (gen _))ˣ) (y : ((Sp V).presheaf.stalk (gen V))ˣ) : Prop :=
  ∃ (U : (Sp R).Opens) (a : Γ(Sp R, U)ˣ), spMap g (gen V) ∈ U ∧ x = gm (jK R) (gen _) U a ∧ y = gm (spMap g) (gen V) U a

variable {g : R →+* V}

theorem Rel.mul {x x' y y'} (h : Rel g x y) (h' : Rel g x' y') : Rel g (x * x') (y * y') := by
  obtain ⟨U, a, hU, rfl, rfl⟩ := h
  obtain ⟨U', a', hU', rfl, rfl⟩ := h'
  have hm : spMap g (gen V) ∈ U ⊓ U' := ⟨hU, hU'⟩
  refine ⟨U ⊓ U', res inf_le_left a * res inf_le_right a', hm, ?_, ?_⟩
  · rw [map_mul, gm_res _ _ _ (jK_mem hm), gm_res _ _ _ (jK_mem hm)]
  · rw [map_mul, gm_res _ _ _ hm, gm_res _ _ _ hm]

theorem Rel.inv {x y} (h : Rel g x y) : Rel g x⁻¹ y⁻¹ := by
  obtain ⟨U, a, hU, rfl, rfl⟩ := h
  exact ⟨U, a⁻¹, hU, (map_inv _ _).symm, (map_inv _ _).symm⟩

theorem Rel.congr {x x' y} (h : Rel g x y) (e : x = x') : Rel g x' y := e ▸ h

theorem Rel.unique {x y y'} (h : Rel g x y) (h' : Rel g x y') : y = y' := by
  obtain ⟨U, a, hU, rfl, rfl⟩ := h
  obtain ⟨U', a', hU', e, rfl⟩ := h'
  have hm : spMap g (gen V) ∈ U ⊓ U' := ⟨hU, hU'⟩
  have : res (inf_le_left : U ⊓ U' ≤ U) a = res inf_le_right a' := gmK_inj (jK_mem hm) (by
    rw [gm_res _ _ _ (jK_mem hm), gm_res _ _ _ (jK_mem hm), e])
  rw [← gm_res _ _ (inf_le_left : U ⊓ U' ≤ U) hm, this, gm_res _ _ _ hm]

theorem Rel.point {X : Scheme.{0}} (p : Sp R ⟶ X) (U : X.Opens) (h : p (spMap g (gen V)) ∈ U) (a : Γ(X, U)ˣ) :
    Rel g (gm (jK R ≫ p) (gen _) U a) (gm (spMap g ≫ p) (gen V) U a) :=
  ⟨p ⁻¹ᵁ U, pullU p U a, h, (gm_pull _ p _ U (jK_mem (U := p ⁻¹ᵁ U) h) a).symm, (gm_pull _ p _ U h a).symm⟩

def toStk (V : Type) [CommRing V] [IsDomain V] : V →+* (Sp V).presheaf.stalk (gen V) :=
  ((Sp V).presheaf.germ ⊤ (gen V) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom

theorem toStk_injective : Function.Injective (toStk V) :=
  (germ_injective_of_isIntegral (Sp V) (U := ⊤) (gen V) trivial).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1

theorem toStk_map (r : R) : toStk V (g r) = gs (spMap g) (gen V) ⊤ (DegPre.toOpen (R := R) ⊤ r) := by
  rw [gs_eq _ _ ⊤ trivial, BetaAdd.toOpen_top]
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  exact congrArg ((Sp V).presheaf.germ ⊤ (gen V) trivial).hom e

theorem toStk_valR {U : (Sp V).Opens} (h : ⊤ ≤ U) (a : Γ(Sp V, U)) :
    toStk V (valR (𝟙 (Sp V)) U a) = gs (𝟙 (Sp V)) (gen V) U a := by
  rw [valR, dif_pos (show ⊤ ≤ 𝟙 (Sp V) ⁻¹ᵁ U from h), gs_eq _ _ U (h trivial)]
  simp only [toStk, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp V).presheaf (homOfLE h) (gen V) trivial a

theorem isUnit_toStk {v : V} (hv : v ≠ 0) : IsUnit (toStk V v) := by
  have hm : gen V ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v) := by
    rw [basicOpen_eq_of_affine]
    exact hv
  exact ((Sp V).mem_basicOpen_top _ _).1 hm

theorem Rel.elt {r : R} (hr : g r ≠ 0) {x y} (hx : x.val = gs (jK R) (gen _) ⊤ (DegPre.toOpen (R := R) ⊤ r))
    (hy : y.val = toStk V (g r)) : Rel g x y := by
  have hm : spMap g (gen V) ∈ (Sp R).basicOpen (DegPre.toOpen (R := R) ⊤ r) := by
    rw [BetaAdd.toOpen_top, basicOpen_eq_of_affine]
    exact hr
  rw [toStk_map] at hy
  generalize DegPre.toOpen (R := R) ⊤ r = s at hm hx hy
  obtain ⟨a, ha⟩ : IsUnit (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le s)).op).hom s) :=
    (Sp R).toRingedSpace.isUnit_res_basicOpen s
  refine ⟨(Sp R).basicOpen s, a, hm, Units.ext ?_, Units.ext ?_⟩
  · rw [hx, ← gs_unit _ _ _ (jK_mem hm), ha, gs_res _ _ _ (jK_mem hm)]
  · rw [hy, ← gs_unit _ _ _ hm, ha, gs_res _ _ _ hm]

theorem corr_of_val_gen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp V ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp V ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ J, Good L (gen V) J → val t (𝟙 _) (gen V) J = val t' (𝟙 _) (gen V) J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine unit_ext fun y hy₀ => congrArg _ ?_
  have hy := gen_mem hy₀
  refine gm_inj hy ?_
  obtain ⟨J, hJ, e⟩ := exists_good L hL (gen V) (Sum.elim φ φ') (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
  have := h J hJ
  rw [val_of t _ _ J j (fun k => by rw [Category.id_comp]; exact e (.inl k)),
    val_of t' _ _ J j' (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
  exact (gm_res _ _ _ hy _).trans (this.trans (gm_res _ _ _ hy _).symm)

theorem exists_gen_of_top {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j₀ : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j₀) (w : Γ(Y, ⊤)ˣ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∀ y j, y ∈ LB.wchart L φ j →
      gm (𝟙 Y) y (LB.wchart L φ j) (e.s j) = trF φ ε (𝟙 Y) y j j₀ * gm (𝟙 Y) y ⊤ w := by
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀ := fun j => le_inf le_rfl (le_top.trans h)
  let e : LB.Gen (LB.LinComb L φ ε) := ⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀) * res le_top w⟩
  have key : ∀ y j, y ∈ LB.wchart L φ j →
      gm (𝟙 Y) y (LB.wchart L φ j) (e.s j) = trF φ ε (𝟙 Y) y j j₀ * gm (𝟙 Y) y ⊤ w := fun y j hj =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ _ _ hj _).trans (gm_linComb L φ ε _ y j j₀ hj (h trivial)))
      (gm_res _ _ _ hj _))
  refine ⟨e, isGen_of_gm e fun y j j' hj hj' => ?_, key⟩
  rw [key y j hj, key y j' hj', ← trF_trans hL φ ε (𝟙 Y) y hj hj' (h trivial), _root_.mul_assoc]

end Rel

section Main

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {D : DegPre R} {g : R →+* V}

theorem cT_left (χ : D.X) : (cT D (Over.mk (spMap g)) χ).left = spMap g ≫ (D.c χ).left := by simp

theorem xK_eq (χ : D.X) : D.xK χ = jK R ≫ (D.c χ).left := by simp [ptK]

theorem zero_left : (toUnit (Over.mk (spMap g)) ≫ η[D.P.A]).left = spMap g ≫ eSec D.P.A := by simp [eSec]

abbrev trV (D : DegPre R) (x : Sp V ⟶ D.P.A.left) (i i' : D.P.L.ι) : ((Sp V).presheaf.stalk (gen V))ˣ :=
  gm x (gen V) (D.P.L.U i ⊓ D.P.L.U i') (D.P.L.g i i')

theorem rel_psi {χ : D.X} {i i₀ : D.P.L.ι} {r : R} (hi : (D.c χ).left (spMap g (gen V)) ∈ D.P.L.U i)
    (h : CoordAt D χ i₀ r) (hr : g r ≠ 0) {y} (hy : y.val = toStk V (g r)) :
    Rel g (gm (𝟙 _) (gen _) (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) fun _ => i) ((D.psi χ).s fun _ => i))
      ((trV D (spMap g ≫ (D.c χ).left) i i₀)⁻¹ * y) := by
  obtain ⟨hj, h, e⟩ := h
  have hz₀ : (𝟙 (Sp (FractionRing R)) : _ ⟶ _) (gen _) ∈
      LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) fun _ => i₀ := h trivial
  have hz : (𝟙 (Sp (FractionRing R)) : _ ⟶ _) (gen _) ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) fun _ => i :=
    Set.mem_iInter.2 fun _ => by rw [xK_eq]; exact jK_mem (U := (D.c χ).left ⁻¹ᵁ D.P.L.U i) hi
  rw [gen_trans (D.psi_gen χ) (𝟙 (Sp (FractionRing R))) (gen _) hz hz₀]
  refine Rel.mul ?_ (Rel.elt hr ?_ hy)
  · rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp, show ptK (D.c χ) = _ from xK_eq χ]
    exact (Rel.point (D.c χ).left (D.P.L.U i ⊓ D.P.L.U i₀) ⟨hi, hj trivial⟩ _).inv
  · refine (gs_unit _ _ _ hz₀ _).symm.trans ((gs_res (𝟙 _) _ h trivial _).symm.trans ?_)
    refine (congrArg (gs (𝟙 _) _ _) e.symm).trans ?_
    exact (gs_eq (𝟙 (Sp (FractionRing R))) _ (jK R ⁻¹ᵁ ⊤) trivial _).trans (gs_eq (jK R) _ ⊤ trivial _).symm

abbrev rigV (D : DegPre R) (g : R →+* V) (i : D.P.L.ι) : ((Sp V).presheaf.stalk (gen V))ˣ :=
  gm (spMap g) (gen V) (LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) fun _ => i) (D.rig.s fun _ => i)

theorem rigV_val {i : D.P.L.ι} (h : ⊤ ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U i) : (rigV D g i).val = toStk V (g (rigAt D i)) := by
  have ht : (⊤ : (Sp R).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => h hy
  rw [toStk_map, BetaAdd.toOpen_top, rigAt, valR, dif_pos (show ⊤ ≤ 𝟙 (Sp R) ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U fun _ => i from ht), Iso.hom_inv_id_apply]
  exact (gs_unit _ _ _ (ht trivial) _).symm.trans (gs_res (spMap g) _ ht trivial _).symm

theorem isUnit_rigAt {i : D.P.L.ι} (h : ⊤ ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U i) : IsUnit (rigAt D i) := by
  have ht : (⊤ : (Sp R).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => eSec D.P.A) fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => h hy
  rw [rigAt, valR, dif_pos (show ⊤ ≤ 𝟙 (Sp R) ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U fun _ => i from ht)]
  exact ((Units.isUnit _).map _).map _

theorem rigV_trans {i i' : D.P.L.ι} (h : eSec D.P.A (spMap g (gen V)) ∈ D.P.L.U i)
    (h' : eSec D.P.A (spMap g (gen V)) ∈ D.P.L.U i') :
    rigV D g i = trV D (spMap g ≫ eSec D.P.A) i i' * rigV D g i' := by
  have := gen_trans D.rig_gen (spMap g) (gen V) (j := fun _ => i) (j' := fun _ => i')
    (Set.mem_iInter.2 fun _ => h) (Set.mem_iInter.2 fun _ => h')
  rwa [trF, Fintype.prod_unique, zpow_one] at this

theorem exists_goodK {J} (hJ : Good D.P.L (gen V) J) : ∃ JK, Good D.P.L (gen (FractionRing R)) JK ∧
    ∀ x : Sp R ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → JK (jK R ≫ x) = J (spMap g ≫ x) := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have : IsDominant (jK R) := DVR.isDominant_jK
  obtain ⟨JK, h, e⟩ := exists_good D.P.L D.P.isLB (gen (FractionRing R))
    (K := {x : Sp R ⟶ D.P.A.left // x ≫ D.P.A.hom = 𝟙 _}) (fun x => jK R ≫ x.1) (fun x => J (spMap g ≫ x.1))
    (fun a b h => congrArg (fun x => J (spMap g ≫ x))
      (ext_of_isDominant_of_isSeparated D.P.A.hom (a.2.trans b.2.symm) (jK R) h))
    (fun x => jK_mem (U := x.1 ⁻¹ᵁ D.P.L.U (J (spMap g ≫ x.1))) (hJ (spMap g ≫ x.1)))
  exact ⟨JK, h, fun x hx => e ⟨x, hx⟩⟩

theorem rel_val {J JK} (hJ : Good D.P.L (gen V) J)
    (hK : ∀ x : Sp R ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → JK (jK R ≫ x) = J (spMap g ≫ x))
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.P.L φ ε)) (p : Sp R ⟶ Y) (hp : ∀ k, (p ≫ φ k) ≫ D.P.A.hom = 𝟙 _)
    {q q'} (hq : q = jK R ≫ p) (hq' : q' = spMap g ≫ p) :
    Rel g (val t q (gen _) JK) (val t q' (gen V) J) := by
  subst hq hq'
  rw [val_of t _ _ JK (fun k => J ((spMap g ≫ p) ≫ φ k)) (fun k => by
    rw [Category.assoc, Category.assoc]; exact hK _ (hp k))]
  exact Rel.point p _ (hJ.mem φ (spMap g ≫ p)) _

end Main

section Exist

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegPre R}
  {C : Type} [NormedField C] [IsUltrametricDist C]

omit [IsDomain R] [IsLocalRing R] in

theorem exists_unit_of_norm {x : C} (h : ‖x‖ = 1) : ∃ u : (intO C)ˣ, ((u : intO C) : C) = x := by
  have h0 : x ≠ 0 := fun e => by simp [e] at h
  refine ⟨⟨⟨x, h.le⟩, ⟨x⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩
  change ‖x⁻¹‖ ≤ 1
  rw [norm_inv, h, inv_one]

theorem exists_isBiTriv {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (hD : D.TauBimult)
    (g : R →+* intO C) (hex : ∀ χ, ∃ r, PsiCoord D χ r) (hne : ∀ χ r, PsiCoord D χ r → g r ≠ 0)
    (t : D.X → D.X → Cˣ) (hs : ∀ a b, t a b = t b a) (hm : ∀ a a' b, t (a + a') b = t a b * t a' b)
    (hb : ∀ (x : O) a b, t (x • a) b = t a (star x • b))
    (hn : ∀ a b r₁ r₂ r₃, PsiCoord D (a + b) r₁ → PsiCoord D a r₂ → PsiCoord D b r₃ →
      ‖(g r₁ : C)‖ = ‖(t a b : C)‖ * ‖(g r₂ : C)‖ * ‖(g r₃ : C)‖) :
    ∃ e : ∀ a b, BiGen D (Over.mk (spMap g)) a b, IsBiTriv oa e ∧ ∀ a b, IsTauVal g (e a b) (t a b) := by
  have hL := D.P.isLB
  have key : ∀ N t a b r : C, t ≠ 0 → a ≠ 0 → b ≠ 0 → r ≠ 0 → N / (t * a * b * r) * t * a * b * r = N := by
    intros; field_simp
  have gkey : ∀ A B B' Z w k y y' r x : ((Sp (intO C)).presheaf.stalk (gen (intO C)))ˣ, w * k * y * y' * r = x →
      A ^ (-1 : ℤ) * B ^ (1 : ℤ) * B' ^ (1 : ℤ) * Z ^ (-1 : ℤ) * w * k =
        A⁻¹ * x * (B⁻¹ * y)⁻¹ * (B'⁻¹ * y')⁻¹ * (Z * r)⁻¹ := by
    rintro A B B' Z w k y y' r _ rfl
    apply Additive.ofMul.injective
    simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv]
    abel
  have := PeriodLaws.isFractionRing_intO (C := C)
  let κ : C →+* (Sp (intO C)).presheaf.stalk (gen (intO C)) := IsLocalization.lift (M := nonZeroDivisors (intO C))
    (g := toStk (intO C)) fun y => isUnit_toStk (nonZeroDivisors.ne_zero y.2)
  have hκ : ∀ v : intO C, κ v = toStk _ v := fun v => IsLocalization.lift_eq _ v
  let k : Cˣ →* _ := Units.map κ.toMonoidHom
  choose r₀ hr₀ using hex
  choose i₀ hi₀ using fun χ => (psiCoord_iff χ _).1 (hr₀ χ)
  obtain ⟨i, hi⟩ := exists_chart hL (eSec D.P.A (closedPoint R))
  have hi : ⊤ ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U i := (DVR.eq_top_of_closedPoint_mem _ hi).ge
  have hC : ∀ χ, (g (r₀ χ) : C) ≠ 0 := fun χ e => hne χ _ (hr₀ χ) (Subtype.ext e)
  have hρ : ‖(g (rigAt D i) : C)‖ = 1 := by
    obtain ⟨u, hu⟩ := isUnit_rigAt hi
    rw [← hu]
    exact BetaAdd.norm_unit ((intO C).subtype.comp g) (fun a => (g a).2) u
  have hρ0 : (g (rigAt D i) : C) ≠ 0 := fun e => by simp [e] at hρ
  choose u hu using fun a b => exists_unit_of_norm
    (x := (g (r₀ (a + b)) : C) / (t a b * g (r₀ a) * g (r₀ b) * g (rigAt D i))) (by
      rw [norm_div, hn a b _ _ _ (hr₀ _) (hr₀ _) (hr₀ _), norm_mul, norm_mul, norm_mul, hρ, _root_.mul_one]
      exact div_self (by simp [hC]))
  let y : D.X → _ := fun χ => k (Units.mk0 _ (hC χ))
  have hy : ∀ χ, (y χ).val = toStk _ (g (r₀ χ)) := fun χ => hκ _
  have htop : ∀ a b, ⊤ ≤ LB.wchart D.P.L (biφ D (Over.mk (spMap g)) a b) ![i₀ (a + b), i₀ a, i₀ b, i] :=
    fun a b z _ => Set.mem_iInter.2 fun n => by
      fin_cases n
      · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left (a + b))).mpr ((hi₀ _).1 trivial)
      · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left a)).mpr ((hi₀ _).1 trivial)
      · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left b)).mpr ((hi₀ _).1 trivial)
      · exact (congrArg (fun q => q z ∈ D.P.L.U _) (zero_left (D := D) (g := g))).mpr (hi trivial)
  choose e he hev using fun a b => exists_gen_of_top hL _ Oinvε _ (htop a b) (unitOn (u a b))
  let Ψ := fun χ j => (trV D (spMap g ≫ (D.c χ).left) j (i₀ χ))⁻¹ * y χ
  have E : ∀ a b j, gen (intO C) ∈ LB.wchart D.P.L (biφ D (Over.mk (spMap g)) a b) j →
      gm (𝟙 (Sp (intO C))) (gen _) (LB.wchart D.P.L (biφ D (Over.mk (spMap g)) a b) j) ((e a b).s j) * k (t a b) =
        Ψ (a + b) (j 0) * (Ψ a (j 1))⁻¹ * (Ψ b (j 2))⁻¹ * (rigV D g (j 3))⁻¹ := by
    intro a b j hj
    have h3 : eSec D.P.A (spMap g (gen _)) ∈ D.P.L.U (j 3) :=
      (congrArg (fun q => q (gen _) ∈ D.P.L.U _) (zero_left (D := D) (g := g))).mp (Set.mem_iInter.1 hj 3)
    have h1 : gm (𝟙 (Sp (intO C))) (gen _) ⊤ (unitOn (u a b)) * k (t a b) * y a * y b * rigV D g i = y (a + b) := by
      apply Units.ext
      have h2 : (gm (𝟙 (Sp (intO C))) (gen _) ⊤ (unitOn (u a b))).val = toStk (intO C) (u a b : intO C) := gm_val _ _ ⊤ trivial _
      simp only [Units.val_mul, hy, rigV_val hi, h2, ← hκ]
      change κ _ * κ (t a b) * _ * _ * _ = _
      simp only [← map_mul]
      rw [hu]
      refine congrArg κ ?_
      exact key _ _ _ _ _ (t a b).ne_zero (hC a) (hC b) hρ0
    refine (congrArg (· * k (t a b)) (hev a b (gen _) j hj)).trans ?_
    have e0 : trF (L := D.P.L) (biφ D (Over.mk (spMap g)) a b) Oinvε (𝟙 (Sp (intO C))) (gen _) j
        ![i₀ (a + b), i₀ a, i₀ b, i] = trV D (spMap g ≫ (D.c (a + b)).left) (j 0) (i₀ (a + b)) ^ (-1 : ℤ) *
          trV D (spMap g ≫ (D.c a).left) (j 1) (i₀ a) ^ (1 : ℤ) * trV D (spMap g ≫ (D.c b).left) (j 2) (i₀ b) ^ (1 : ℤ) *
          trV D (spMap g ≫ eSec D.P.A) (j 3) i ^ (-1 : ℤ) := by
      rw [← cT_left, ← cT_left, ← cT_left, ← zero_left]
      exact Fin.prod_univ_four _
    rw [rigV_trans h3 (hi trivial)]
    exact (congrArg (fun z => z * gm (𝟙 (Sp (intO C))) (gen _) ⊤ (unitOn (u a b)) * k (t a b)) e0).trans
      (gkey _ _ _ _ _ _ _ _ _ _ h1)
  have T : ∀ {J JK}, Good D.P.L (gen (intO C)) J → Good D.P.L (gen (FractionRing R)) JK →
      (∀ x : Sp R ⟶ D.P.A.left, x ≫ D.P.A.hom = 𝟙 _ → JK (jK R ≫ x) = J (spMap g ≫ x)) → ∀ a b,
      Rel g (val (D.tau a b) (𝟙 (Sp (FractionRing R))) (gen _) JK)
        (val (Z := Sp (intO C)) (e a b) (𝟙 (Sp (intO C))) (gen _) J * k (t a b)) := by
    intro J JK hJ hJK hK a b
    have p : ∀ χ, Rel g (val (D.psi χ) (𝟙 (Sp (FractionRing R))) (gen _) JK) (Ψ χ (J (spMap g ≫ (D.c χ).left))) := fun χ => by
      rw [val_of (D.psi χ) (𝟙 (Sp (FractionRing R))) _ JK (fun _ => J (spMap g ≫ (D.c χ).left)) fun _ =>
        (congrArg JK ((Category.id_comp _).trans (xK_eq χ))).trans (hK _ (Over.w _))]
      exact rel_psi (hJ (spMap g ≫ (D.c χ).left)) (hi₀ χ) (hne χ _ (hr₀ χ)) (hy χ)
    have q : Rel g (val D.rigK (𝟙 (Sp (FractionRing R))) (gen _) JK) (rigV D g (J (spMap g ≫ eSec D.P.A))) := by
      rw [show val D.rigK (𝟙 (Sp (FractionRing R))) (gen _) JK = _ from val_pull hJK _ _ _]
      exact rel_val hJ hK D.rig (𝟙 (Sp R)) (fun _ => (congrArg (· ≫ D.P.A.hom) (Category.id_comp _)).trans (Over.w η[D.P.A]))
        ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.comp_id _).symm
    refine Rel.congr ?_ (PeriodBalance.val_tau D _ hJK a b).symm
    refine (E a b _ (hJ.mem _ (𝟙 (Sp (intO C))))).symm ▸ ?_
    simp only [biφ, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, cT_left, zero_left]
    exact (((p _).mul (p _).inv).mul (p _).inv).mul q.inv
  refine ⟨e, ⟨he, fun a b => corr_of_val_gen hL fun J hJ => ?_, fun a a' b => corr_of_val_gen hL fun J hJ => ?_,
    fun x w hw h₀ a b => corr_of_val_gen hL fun J hJ => ?_⟩, fun a b j r₁ r₂ r₃ h₁ h₂ h₃ h₄ => ?_⟩
  · obtain ⟨JK, hJK, hK⟩ := exists_goodK (g := g) hJ
    have h₁ := T hJ hJK hK a b
    have h₂ := T hJ hJK hK b a
    have : val (D.tau a b) (𝟙 (Sp (FractionRing R))) (gen _) JK =
        val (D.tau b a) (𝟙 (Sp (FractionRing R))) (gen _) JK := by
      refine (PeriodBalance.val_tau D _ hJK a b).trans (Eq.trans ?_ (PeriodBalance.val_tau D _ hJK b a).symm)
      rw [add_comm a b]
      exact congrArg (· * _) (mul_right_comm _ _ _)
    rw [this] at h₁
    have := h₁.unique h₂
    rwa [hs b a, mul_left_inj] at this
  · obtain ⟨JK, hJK, hK⟩ := exists_goodK (g := g) hJ
    have c := rel_val hJ hK D.cub.t (lift (D.c a) (lift (D.c a') (D.c b))).left (fun _ => BetaAdd.over_sec _ _)
      (q := 𝟙 (Sp (FractionRing R)) ≫ D.pt3 a a' b) (q' := 𝟙 (Sp (intO C)) ≫ (lift (cT D (Over.mk (spMap g)) a)
        (lift (cT D (Over.mk (spMap g)) a') (cT D (Over.mk (spMap g)) b))).left)
      (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift]) (by simp [← CartesianMonoidalCategory.comp_lift])
    have h₁ := (T hJ hJK hK (a + a') b).mul c
    have h₂ := (T hJ hJK hK a b).mul (T hJ hJK hK a' b)
    have := (val_mul hJK _ _ _).symm.trans ((val_corr hJK (hD a a' b) (𝟙 (Sp (FractionRing R)))).trans (val_mul hJK _ _ _))
    have := (h₁.congr ((congrArg (_ * ·) (val_pull hJK _ _ _).symm).trans this)).unique h₂
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [hm, map_mul, mul_right_comm] at this
    have := mul_right_cancel (this.trans (_root_.mul_mul_mul_comm _ _ _ _))
    exact (congrArg (_ * ·) (val_pull hJ _ _ _)).trans this
  · obtain ⟨JK, hJK, hK⟩ := exists_goodK (g := g) hJ
    have c := rel_val hJ hK w (lift (D.c a) (D.c b)).left (fun n => by fin_cases n <;> exact BetaAdd.over_sec _ _)
      (q := 𝟙 (Sp (FractionRing R)) ≫ D.pt2 a b) (q' := 𝟙 (Sp (intO C)) ≫ (lift (cT D (Over.mk (spMap g)) a) (cT D (Over.mk (spMap g)) b)).left)
      (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift]) (by simp [← CartesianMonoidalCategory.comp_lift])
    have h₁ := (T hJ hJK hK (x • a) b).mul c
    have h₂ := T hJ hJK hK a (star x • b)
    have := (val_mul hJK _ _ _).symm.trans (val_corr hJK (oa.tau_bal x w hw h₀ a b) (𝟙 (Sp (FractionRing R))))
    have := (h₁.congr ((congrArg (_ * ·) (val_pull hJK _ _ _).symm).trans this)).unique h₂
    refine (val_mul hJ _ _ _).trans ?_
    rw [hb, mul_right_comm, mul_left_inj] at this
    exact (congrArg (_ * ·) (val_pull hJ _ _ _)).trans this
  · have ht : ⊤ ≤ LB.wchart D.P.L (biφ D (Over.mk (spMap g)) a b) j :=
      fun z _ => Set.mem_iInter.2 fun n => by
        fin_cases n
        · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left (a + b))).mpr (h₁.1 trivial)
        · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left a)).mpr (h₂.1 trivial)
        · exact (congrArg (fun q => q z ∈ D.P.L.U _) (cT_left b)).mpr (h₃.1 trivial)
        · exact (congrArg (fun q => q z ∈ D.P.L.U _) (zero_left (D := D) (g := g))).mpr (h₄ trivial)
    have p : ∀ {χ n r}, CoordAt D χ n r → (Ψ χ n).val = κ (g r) := fun {χ n r} h => by
      have h0 := hne χ r ((psiCoord_iff _ _).2 ⟨n, h⟩)
      have := (rel_psi (h.1 trivial) (hi₀ χ) (hne χ _ (hr₀ χ)) (hy χ)).unique
        (rel_psi (h.1 trivial) h h0 (y := (isUnit_toStk h0).unit) rfl)
      rw [show trV D (spMap g ≫ (D.c χ).left) n n = 1 from gm_self hL _ _ (h.1 trivial), inv_one, _root_.one_mul] at this
      exact (congrArg Units.val this).trans (hκ _).symm
    have h₅ := E a b j (ht trivial)
    rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq] at h₅
    have h₆ := congrArg Units.val h₅
    simp only [Units.val_mul, p h₁, p h₂, p h₃, rigV_val h₄, ← hκ] at h₆
    have h₇ := (hκ _).trans ((toStk_valR ht ((e a b).s j).val).trans (gs_unit _ _ _ (ht trivial) _))
    apply κ.injective
    rw [← h₆, map_mul, map_mul, map_mul, map_mul]
    erw [h₇]
    change _ * κ (t a b) * _ * _ * _ = κ (t a b) * _ * _ * _ * _
    ring

theorem IsTauVal.unique {g : R →+* intO C} (hex : ∀ χ, ∃ r, PsiCoord D χ r) (hne : ∀ χ r, PsiCoord D χ r → g r ≠ 0)
    {a b : D.X} {e : BiGen D (Over.mk (spMap g)) a b} {t t' : C} (h : IsTauVal g e t) (h' : IsTauVal g e t') : t = t' := by
  choose r₀ hr₀ using hex
  choose i₀ hi₀ using fun χ => (psiCoord_iff χ _).1 (hr₀ χ)
  obtain ⟨i, hi⟩ := exists_chart D.P.isLB (eSec D.P.A (closedPoint R))
  have hi : ⊤ ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U i := (DVR.eq_top_of_closedPoint_mem _ hi).ge
  have e₁ := h ![i₀ (a + b), i₀ a, i₀ b, i] _ _ _ (hi₀ _) (hi₀ _) (hi₀ _) hi
  have e₂ := h' ![i₀ (a + b), i₀ a, i₀ b, i] _ _ _ (hi₀ _) (hi₀ _) (hi₀ _) hi
  have h0 : (g (r₀ (a + b)) : C) ≠ 0 := fun e => hne _ _ (hr₀ _) (Subtype.ext e)
  simp only [_root_.mul_assoc] at e₁ e₂
  exact mul_right_cancel₀ (right_ne_zero_of_mul (e₁ ▸ h0)) (e₁.symm.trans e₂)

omit [IsUltrametricDist C] in

theorem exists_lift {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (p : ℕ)
    (h : ∀ a b, ∃ c : Cˣ, β a b = -Real.logb p ‖(c : C)‖) :
    ∃ t : X → X → Cˣ, (∀ a b, β a b = -Real.logb p ‖(t a b : C)‖) ∧
      (∀ a b a' b', β a b = β a' b' → t a b = t a' b') ∧ ∀ a a' b, t (a + a') b = t a b * t a' b := by
  let v : Additive Cˣ →ₗ[ℤ] ℝ := (AddMonoidHom.mk' (fun c : Additive Cˣ => -Real.logb p ‖((c.toMul : Cˣ) : C)‖)
    fun c c' => by
      rw [toMul_add, Units.val_mul, norm_mul, Real.logb_mul (by simp) (by simp), neg_add]).toIntLinearMap
  let M := LinearMap.range (TensorProduct.lift β)
  have hle : M ≤ LinearMap.range v := by
    rintro _ ⟨z, rfl⟩
    induction z with
    | zero => simp
    | tmul a b => obtain ⟨c, hc⟩ := h a b; exact ⟨Additive.ofMul c, hc.symm⟩
    | add z w hz hw => rw [map_add]; exact add_mem hz hw
  obtain ⟨s, hs⟩ := Module.projective_lifting_property v.rangeRestrict (Submodule.inclusion hle)
    v.surjective_rangeRestrict
  let m : X → X → M := fun a b => ⟨β a b, a ⊗ₜ b, rfl⟩
  refine ⟨fun a b => (s (m a b)).toMul, fun a b => ?_, fun a b a' b' e => ?_, fun a a' b => ?_⟩
  · exact (congrArg Subtype.val (LinearMap.congr_fun hs (m a b))).symm
  · exact congrArg (fun z => (s z).toMul) (Subtype.ext e : m a b = m a' b')
  · have : m (a + a') b = m a b + m a' b := Subtype.ext (by simp [m])
    simp only [this, map_add, toMul_add]

end Exist

section Point

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

structure Reading (A : DatAt Y P) : Type where
  e : ∀ a b, BiGen A.U.D.toPre (Over.mk (spMap A.f)) a b
  triv : letI := H.starRing; IsBiTriv A.U.oD e
  t : A.Ylat → A.Ylat → (↥C.S)ˣ
  isVal : ∀ a b, IsTauVal A.f (e a b) (t a b)
  symm : ∀ a b, t a b = t b a
  add_left : ∀ a a' b, t (a + a') b = t a b * t a' b
  bal : ∀ (x : 𝓞 E) a b, t (x • a) b = t a (H.bar x • b)
  beta_eq : ∀ a b, A.beta a b = -Real.logb p ‖(t a b : ↥C.S)‖

theorem exists_coord (A : DatAt Y P) (χ : A.Ylat) : ∃ r, PsiCoord A.U.D.toPre χ r := (DatAtCheck.vPsiAt_eq A χ).1

theorem coord_ne (A : DatAt Y P) (χ : A.Ylat) (r : A.R) (h : PsiCoord A.U.D.toPre χ r) : A.f r ≠ 0 :=
  fun e => DatAtCheck.coord_ne_zero A χ r h (congrArg Subtype.val e)

theorem beta_coord (A : DatAt Y P) {a b : A.Ylat} {r₁ r₂ r₃ : A.R} (h₁ : PsiCoord A.U.D.toPre (a + b) r₁)
    (h₂ : PsiCoord A.U.D.toPre a r₂) (h₃ : PsiCoord A.U.D.toPre b r₃) :
    A.beta a b = -Real.logb p ‖(A.f r₁ : ↥C.S) / (A.f r₂ * A.f r₃)‖ := by
  have n₁ := norm_ne_zero_iff.2 (DatAtCheck.coord_ne_zero A _ _ h₁)
  have n₂ := norm_ne_zero_iff.2 (DatAtCheck.coord_ne_zero A _ _ h₂)
  have n₃ := norm_ne_zero_iff.2 (DatAtCheck.coord_ne_zero A _ _ h₃)
  change vPsiAt _ (DatAtCheck.fC A) p _ - vPsiAt _ (DatAtCheck.fC A) p _ - vPsiAt _ (DatAtCheck.fC A) p _ =
    -Real.logb p ‖DatAtCheck.fC A r₁ / (DatAtCheck.fC A r₂ * DatAtCheck.fC A r₃)‖
  rw [(DatAtCheck.vPsiAt_eq A _).2 _ h₁, (DatAtCheck.vPsiAt_eq A _).2 _ h₂, (DatAtCheck.vPsiAt_eq A _).2 _ h₃, norm_div,
    norm_mul, Real.logb_div n₁ (mul_ne_zero n₂ n₃), Real.logb_mul n₂ n₃]
  ring

theorem nonempty_reading (hp : 1 < p) (A : DatAt Y P) : Nonempty (Reading A) := by
  letI := H.starRing
  have nz : ∀ {χ r}, PsiCoord A.U.D.toPre χ r → (A.f r : ↥C.S) ≠ 0 := fun h => DatAtCheck.coord_ne_zero A _ _ h
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_lift (C := ↥C.S) (A.beLin (DatAtCheck.betaAdd Y p)) p fun a b => by
    obtain ⟨r₁, h₁⟩ := exists_coord A (a + b)
    obtain ⟨r₂, h₂⟩ := exists_coord A a
    obtain ⟨r₃, h₃⟩ := exists_coord A b
    exact ⟨Units.mk0 _ (div_ne_zero (nz h₁) (mul_ne_zero (nz h₂) (nz h₃))), beta_coord A h₁ h₂ h₃⟩
  have hs : ∀ a b, t a b = t b a := fun a b => h₂ _ _ _ _ (A.beta_symm a b)
  have hb : ∀ (x : 𝓞 E) a b, t (x • a) b = t a (H.bar x • b) := fun x a b => h₂ _ _ _ _ (DatAtCheck.beta_balanced A x a b)
  obtain ⟨e, he, hv⟩ := exists_isBiTriv A.U.oD A.U.D.tau_bimult A.f (exists_coord A) (coord_ne A) t hs h₃ hb
    fun a b r₁ r₂ r₃ k₁ k₂ k₃ => by
      have hp' : (1 : ℝ) < p := by exact_mod_cast hp
      have e := neg_injective ((h₁ a b).symm.trans (beta_coord A k₁ k₂ k₃))
      have e' := Real.logb_injOn_pos hp' (norm_pos_iff.2 (t a b).ne_zero)
        (norm_pos_iff.2 (div_ne_zero (nz k₁) (mul_ne_zero (nz k₂) (nz k₃)))) e
      have n₂ := norm_ne_zero_iff.2 (nz k₂)
      have n₃ := norm_ne_zero_iff.2 (nz k₃)
      rw [e', norm_div, norm_mul]
      field_simp
  exact ⟨⟨e, he, t, hv, hs, h₃, hb, h₁⟩⟩

theorem Reading.eq_of_isTauVal {A : DatAt Y P} (ρ : Reading A) {a b : A.Ylat} {s : ↥C.S} (h : IsTauVal A.f (ρ.e a b) s) :
    s = ρ.t a b := h.unique (exists_coord A) (coord_ne A) (ρ.isVal a b)

theorem Reading.add_right {A : DatAt Y P} (ρ : Reading A) (a b b' : A.Ylat) : ρ.t a (b + b') = ρ.t a b * ρ.t a b' := by
  rw [ρ.symm, ρ.add_left, ρ.symm b, ρ.symm b']

end Point

end GlobalTheory.LocM.Per
