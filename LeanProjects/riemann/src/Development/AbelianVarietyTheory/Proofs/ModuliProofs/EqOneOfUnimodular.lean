import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.MatrixBundle

section Algebra

variable {H M : Type*} [CommGroup H] [AddCommGroup M] {n : ℕ}

def form (B : H → H → M) (W : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) : M :=
  ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.1) (y uv.2)

variable {B : H → H → M} (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x)

theorem form_add (W W' : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) :
    form B (W + W') x y = form B W x y + form B W' x y := by
  simp only [form, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

include hs in
theorem form_transpose (W : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) :
    form B W.transpose x y = form B W y x := by
  unfold form
  rw [← Equiv.sum_comp (Equiv.prodComm _ _)]
  exact Finset.sum_congr rfl fun uv _ => congrArg (W uv.1 uv.2 • ·) (hs _ _)

include hB in
theorem form_mul_left (W : Matrix (Fin n) (Fin n) ℤ) (x x' y : Fin n → H) :
    form B W (x * x') y = form B W x y + form B W x' y := by
  simp only [form, Pi.mul_apply, hB, smul_add, Finset.sum_add_distrib]

include hB in
theorem one_left (y : H) : B 1 y = 0 := by
  have := hB 1 1 y
  rw [_root_.mul_one] at this
  exact left_eq_add.1 this

include hB in
theorem form_one_left (W : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → H) : form B W 1 y = 0 := by
  simp only [form, Pi.one_apply, one_left hB, smul_zero, Finset.sum_const_zero]

include hB hs

theorem form_mul_right (W : Matrix (Fin n) (Fin n) ℤ) (x y y' : Fin n → H) :
    form B W x (y * y') = form B W x y + form B W x y' := by
  rw [← form_transpose hs, form_mul_left hB, form_transpose hs, form_transpose hs]

theorem form_one_right (W : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → H) : form B W x 1 = 0 := by
  rw [← form_transpose hs, form_one_left hB]

theorem form_mul_self (W : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) :
    form B W (x * y) (x * y) = form B W x x + form B W y y + form B (W + W.transpose) x y := by
  rw [form_mul_left hB, form_mul_right hB hs, form_mul_right hB hs, form_add, form_transpose hs]
  abel

theorem form_inv_self (W : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → H) : form B W x⁻¹ x⁻¹ = form B W x x := by
  have a := form_mul_left hB W x⁻¹ x x⁻¹
  have b := form_mul_right hB hs W x x⁻¹ x
  rw [inv_mul_cancel] at a b
  rw [form_one_left hB] at a
  rw [form_one_right hB hs] at b
  rw [eq_neg_of_add_eq_zero_left a.symm, eq_neg_of_add_eq_zero_right b.symm]

theorem form_subst_right (W c : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) :
    form B W x (fun v => ∏ j, y j ^ c v j) = form B (W * c) x y := by
  have e : ∀ u v, B (x u) (∏ j, y j ^ c v j) = ∑ j, c v j • B (x u) (y j) := fun u v =>
    BilinCalc.map_prod_zpow (fun z => B (x u) z) (fun a b => by simp only [hs (x u), hB]) _ _
  simp only [form, e, Fintype.sum_prod_type, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_comm

theorem form_subst_left (W c : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → H) :
    form B W (fun u => ∏ j, x j ^ c u j) y = form B (c.transpose * W) x y := by
  rw [← form_transpose hs, form_subst_right hB hs, ← form_transpose hs, Matrix.transpose_mul,
    Matrix.transpose_transpose]

theorem form_single_right (W : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → H) (v : Fin n) (y : H) :
    form B W x (Pi.mulSingle v y) = B (∏ u, x u ^ W u v) y := by
  rw [BilinCalc.map_prod_zpow (fun z => B z y) (fun a b => hB a b y), form, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single v (fun b _ hb => by rw [Pi.mulSingle_eq_of_ne hb, hs, one_left hB, smul_zero]) (by simp),
    Pi.mulSingle_eq_same]

omit hB hs in
theorem eq_one_of_unimodular {E : Matrix (Fin n) (Fin n) ℤ} (hE : E.det = 1) (x : Fin n → H)
    (h : ∀ v, ∏ u, x u ^ E u v = 1) (u : Fin n) : x u = 1 := by
  have e : E * E.adjugate = 1 := by rw [Matrix.mul_adjugate, hE, one_smul]
  have e₁ : ∏ v, (∏ w, x w ^ E w v) ^ E.adjugate v u = ∏ w, x w ^ (E * E.adjugate) w u := by
    simp only [← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact (map_sum (zpowersHom H (x w)).toAdditiveRight _ _).symm
  simp only [h, one_zpow, Finset.prod_const_one, e, Matrix.one_apply] at e₁
  rw [Finset.prod_eq_single u (fun b _ hb => by rw [if_neg hb, zpow_zero]) (by simp), if_pos rfl, zpow_one] at e₁
  exact e₁.symm

end Algebra

open CechPic

variable {S : Scheme.{0}} {A G : Over S} {n : ℕ}

def pairCls (p : Pic (A ⊗ A).left) {T : Over S} (x y : T ⟶ A) : Pic T.left := pull (lift x y).left p

theorem pull_pairCls (p : Pic (A ⊗ A).left) {T T' : Over S} (h : T' ⟶ T) (x y : T ⟶ A) :
    pull h.left (pairCls p x y) = pairCls p (h ≫ x) (h ≫ y) := by
  rw [pairCls, ← pull_comp, ← Over.comp_left, comp_lift]; rfl

abbrev matLB (P : LB (A ⊗ A).left) (pr : Fin n → (G ⟶ A)) (W : Matrix (Fin n) (Fin n) ℤ) : LB G.left :=
  LB.LinComb P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

variable [GrpObj A] [IsCommMonObj A] [GrpObj G] {P : LB (A ⊗ A).left} (hP : P.IsLB) {pr : Fin n → (G ⟶ A)}
  {W : Matrix (Fin n) (Fin n) ℤ}

def coord (pr : Fin n → (G ⟶ A)) {T : Over S} (x : T ⟶ G) : Fin n → (T ⟶ A) := fun u => x ≫ pr u

omit [GrpObj G] in
theorem pull_matLB (h : (matLB P pr W).IsLB) {T : Over S} (x : T ⟶ G) :
    pull x.left (cls _ h) = form (pairCls (cls P hP)) W (coord pr x) (coord pr x) := by
  rw [cls_linComb hP, map_sum]
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [map_zsmul]
  exact congrArg (W uv.1 uv.2 • ·) (pull_pairCls _ x _ _)

omit [IsCommMonObj A] in
theorem coord_mul (hpr : ∀ u, IsMonHom (pr u)) {T : Over S} (x y : T ⟶ G) :
    coord pr (x * y) = coord pr x * coord pr y := funext fun u => by
  have := hpr u
  exact MonObj.mul_comp _ _ _

theorem coord_one (hpr : ∀ u, IsMonHom (pr u)) {T : Over S} : coord pr (1 : T ⟶ G) = 1 := funext fun u => by
  have := hpr u
  exact MonObj.one_comp _

theorem coord_inv (hpr : ∀ u, IsMonHom (pr u)) {T : Over S} (x : T ⟶ G) : coord pr x⁻¹ = (coord pr x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← coord_mul hpr, inv_mul_cancel, coord_one hpr])

structure IsSymBilin (p : Pic (A ⊗ A).left) : Prop where
  mul : ∀ (T : Over S) (x x' y : T ⟶ A), pairCls p (x * x') y = pairCls p x y + pairCls p x' y
  symm : ∀ (T : Over S) (x y : T ⟶ A), pairCls p x y = pairCls p y x

theorem isSymBilin_of_gen
    (hbi : ∀ (T : Over S) (x x' y : T ⟶ A), ∃ t : (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen)
    (hsym : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) : IsSymBilin (cls P hP) := by
  refine ⟨fun T a a' b => ?_, fun T a b => ?_⟩
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T a a' b)
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    unfold pairCls
    rw [← sub_eq_zero, ← e]
    abel
  · have e : cls P hP = pairCls (cls P hP) (snd A A) (fst A A) := (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k := congrArg (pull (lift b a).left) e
    rw [pull_pairCls, lift_fst, lift_snd] at k
    exact k.symm

variable (hb : IsSymBilin (cls P hP)) (hpr : ∀ u, IsMonHom (pr u))
include hb hpr

theorem lam_matLB (h : (matLB P pr W).IsLB) {T : Over S} (x y : T ⟶ G) :
    lam (cls _ h) x y = form (pairCls (cls P hP)) (W + W.transpose) (coord pr x) (coord pr y) := by
  rw [lam, pull_matLB hP, pull_matLB hP, pull_matLB hP, pull_matLB hP, coord_mul hpr, coord_one hpr,
    form_mul_self (hb.mul T) (hb.symm T), form_one_left (hb.mul T)]
  abel

theorem rigidified_matLB : Out.Rigidified G (matLB P pr W) := by
  have h := LB.isLB_linComb hP (fun uv : Fin n × Fin n => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)
  refine (cls_eq_zero_iff (pull_isLB h _)).1 ?_
  have e : η[G] = (1 : 𝟙_ (Over S) ⟶ G) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  refine (pull_matLB hP h η[G]).trans ?_
  rw [e, coord_one hpr, form_one_left (hb.mul _)]

theorem sym_matLB : Out.Sym G (matLB P pr W) := by
  have h := LB.isLB_linComb hP (fun uv : Fin n × Fin n => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)
  refine fun s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb h _ _)).1 ?_⟩
  have e : (GrpObj.inv : G ⟶ G) = (𝟙 G)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have e₁ : pull (GrpObj.inv : G ⟶ G).left (cls _ h) = cls _ h := by
    rw [e, pull_matLB hP, coord_inv hpr, form_inv_self (hb.mul _) (hb.symm _), ← pull_matLB hP h]
    exact pull_id _
  rw [cls_linComb h, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
  rw [pull_comp, e₁, add_neg_cancel]

theorem kTriv_matLB (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
    (hW : (W + W.transpose).det = 1)
    (hnd : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv G (matLB P pr W) := by
  have h := LB.isLB_linComb hP (fun uv : Fin n × Fin n => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)
  intro R _ t x hx
  have key : ∀ v, ∏ u, coord pr x u ^ (W + W.transpose) u v = 1 := fun v => by
    choose V hV c hc using hx
    let 𝒰 : (Spec (CommRingCat.of R)).OpenCover := Scheme.Cover.mkOfCovers _ (fun p => (V p).toScheme) (fun p => (V p).ι)
      (fun p => ⟨p, ⟨p, hV p⟩, rfl⟩) (fun _ => inferInstance)
    refine Over.OverMorphism.ext (𝒰.hom_ext _ _ fun p => ?_)
    let i : Out.overRes (T := Over.mk t) (V p) ⟶ Over.mk t := Out.overResι (T := Over.mk t) (V p)
    have hd : (Out.translDiff G (matLB P pr W) x).IsLB := LB.isLB_linComb h _ _
    have c₀ := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    have loc : ∀ (Z : Over S) (r : Z ⟶ Out.overRes (T := Over.mk t) (V p)) (a : Z ⟶ G),
        pull ((r ≫ i ≫ x) * a).left (cls _ h) - pull a.left (cls _ h) = 0 := fun Z r a => by
      have hr : Set.range (lift (r ≫ i) a).left ⊆ Set.range ((fst (Over.mk t) G).left ⁻¹ᵁ V p).ι := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨z, rfl⟩
        have e : (lift (r ≫ i) a ≫ fst (Over.mk t) G).left z = (r ≫ i).left z := by rw [lift_fst]
        have m : (r ≫ i).left z ∈ V p := (r.left z).2
        exact (congrArg (· ∈ V p) e).mpr m
      have c₁ := congrArg (pull (IsOpenImmersion.lift _ _ hr)) c₀
      rw [cls_pull hd, ← pull_comp, IsOpenImmersion.lift_fac, map_zero] at c₁
      replace c₁ := (congrArg _ (cls_linComb h _ _ hd)).symm.trans c₁
      rw [Fin.sum_univ_two] at c₁
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, map_add, map_neg, ← pull_comp,
        ← Over.comp_left, lift_snd] at c₁
      rw [show lift (r ≫ i) a ≫ lift (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) ≫ μ = (r ≫ i ≫ x) * a from
        (CommutatorPairing.lift_translPt x (r ≫ i) a).trans (by rw [Category.assoc])] at c₁
      rw [sub_eq_add_neg]
      exact c₁
    obtain ⟨a, ha, -⟩ := hu (A ⊗ Out.overRes (T := Over.mk t) (V p)) (Pi.mulSingle v (fst _ _))
    have l₁ := loc _ (snd A _) a
    have l₂ := loc _ (snd A _) 1
    rw [_root_.mul_one] at l₂
    have l₃ := lam_matLB hP hb hpr h (snd A _ ≫ i ≫ x) a
    have ha' : coord pr a = _ := funext ha
    rw [lam, ha',
      form_single_right (hb.mul _) (hb.symm _), sub_eq_zero.1 l₁, sub_eq_zero.1 l₂] at l₃
    let F : (Over.mk t ⟶ A) →* (A ⊗ Out.overRes (T := Over.mk t) (V p) ⟶ A) :=
      MonoidHom.mk' (fun z => snd A _ ≫ i ≫ z) fun x y => by simp only [MonObj.comp_mul]
    have e : ∏ u, coord pr (snd A _ ≫ i ≫ x) u ^ (W + W.transpose) u v =
        snd A _ ≫ i ≫ ∏ u, coord pr x u ^ (W + W.transpose) u v := by
      refine Eq.trans ?_ (map_prod F _ _).symm
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [map_zpow]
      simp only [coord, Category.assoc]
      rfl
    rw [e] at l₃
    have l₄ := hnd _ (i ≫ ∏ u, coord pr x u ^ (W + W.transpose) u v)
      ((cls_eq_zero_iff (pull_isLB hP _)).1 (l₃.symm.trans (by abel)))
    exact congrArg CommaMorphism.left (l₄.trans (MonObj.comp_one i).symm)
  refine (hu _ 1).unique (fun u => eq_one_of_unimodular hW (coord pr x) key u) fun u => ?_
  exact congrFun (coord_one hpr) u

theorem sq_eq_of_weilIs (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) {k : ℤ} {T : Over S} {Λ : Type}
    [AddCommGroup Λ] (l : Λ → (T ⟶ A)) (hl : ∀ a b, l (a + b) = l a * l b) (ω : Λ → Λ → ℤ)
    (hω₁ : ∀ a a' b, ω (a + a') b = ω a b + ω a' b) (hω₂ : ∀ a b b', ω a (b + b') = ω a b + ω a b')
    (ξ : Γ(T.left, ⊤)ˣ)
    (hw : ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (l a) (l b) (ξ ^ (2 * ω a b)))
    {x y : T ⟶ G} {α β : Fin n → Λ} (hx : ∀ u, x ≫ pr u = l (α u)) (hy : ∀ u, y ≫ pr u = l (β u))
    {c : Γ(T.left, ⊤)ˣ} (hc : Out.WeilIs G (matLB P pr W) k x y c) :
    c ^ 2 = ξ ^ (2 * ∑ u, ∑ v, (W + W.transpose) u v * ω (α u) (β v)) := by
  have h := LB.isLB_linComb hP (fun uv : Fin n × Fin n => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have := hA.comm
  let φ : (Fin n × Fin n) × Fin 3 → (G ⟶ A) := fun i => ![pr i.1.1 * pr i.1.2, pr i.1.1, pr i.1.2] i.2
  let e : (Fin n × Fin n) × Fin 3 → ℤ := fun i => ![W i.1.1 i.1.2, -W i.1.1 i.1.2, -W i.1.1 i.1.2] i.2
  let m : (Fin n → Λ) → (Fin n × Fin n) × Fin 3 → Λ := fun α i => ![α i.1.1 + α i.1.2, α i.1.1, α i.1.2] i.2
  have hφ : ∀ i, IsMonHom (φ i) := by
    rintro ⟨⟨u, v⟩, j⟩
    have := hpr u
    have := hpr v
    fin_cases j
    · show IsMonHom (lift (pr u) (pr v) ≫ μ)
      infer_instance
    · exact hpr u
    · exact hpr v
  have hm : ∀ (x : T ⟶ G) (α : Fin n → Λ), (∀ u, x ≫ pr u = l (α u)) → ∀ i, x ≫ φ i = l (m α i) := by
    rintro x α hx ⟨⟨u, v⟩, j⟩
    fin_cases j
    · exact (MonObj.comp_mul _ _ _).trans ((congrArg₂ (· * ·) (hx u) (hx v)).trans (hl _ _).symm)
    · exact hx u
    · exact hx v
  have hM := PairingComb.weilIs_linComb hG hA hD φ hφ e (n := k) (x := x) (y := y)
    (fun i => ξ ^ (2 * ω (m α i) (m β i))) fun i => by rw [hm x α hx, hm y β hy]; exact hw _ _
  have hM' := LB.isLB_linComb hD (fun i => (φ i).left) e
  have h2 : (lbPow (matLB P pr W) 2).IsLB := LB.isLB_linComb h _ _
  have d : ∀ f : G ⟶ A, pull f.left (cls _ hD) = pairCls (cls P hP) f f := fun f =>
    (pull_pairCls (cls P hP) f (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have iso : LBIso (lbPow (matLB P pr W) 2)
      ((LB.LinComb (P.pull (lift (𝟙 A) (𝟙 A)).left) (fun i => (φ i).left) e).pull (𝟙 G :).left) := by
    refine (cls_eq_iff h2 (pull_isLB hM' _)).1 ?_
    rw [cls_lbPow h, cls_pull hM', cls_linComb hD, cls_linComb hP]
    refine Eq.trans ?_ (pull_id _).symm
    rw [Fintype.sum_prod_type (f := fun i => e i • pull (φ i).left (cls _ hD)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [Fin.sum_univ_three, d, d, d]
    show 2 • W uv.1 uv.2 • pairCls (cls P hP) (pr uv.1) (pr uv.2) =
      W uv.1 uv.2 • pairCls (cls P hP) (pr uv.1 * pr uv.2) (pr uv.1 * pr uv.2) +
        (-W uv.1 uv.2) • pairCls (cls P hP) (pr uv.1) (pr uv.1) + (-W uv.1 uv.2) • pairCls (cls P hP) (pr uv.2) (pr uv.2)
    rw [hb.mul, hb.symm _ (pr uv.1) (_ * _), hb.symm _ (pr uv.2) (_ * _), hb.mul, hb.mul, hb.symm _ (pr uv.2) (pr uv.1)]
    module
  have w := WeilIsogeny.weilIs_pull_hom hG hA h hM' (𝟙 G) iso (n := k) (x := x) (y := y)
    (by rw [Category.comp_id, Category.comp_id]; exact hM)
  refine (CommutatorPairing.weilIs_unique hG hA h (WeilIsogeny.weilIs_pow hG hA h 2 hc) w).trans ?_
  simp only [← zpow_mul]
  have z : ∀ f : (Fin n × Fin n) × Fin 3 → ℤ, ∏ i, ξ ^ f i = ξ ^ ∑ i, f i := fun f =>
    (map_sum (zpowersHom _ ξ).toAdditiveRight f _).symm
  rw [z]
  congr 1
  have s : ∑ u, ∑ v, W.transpose u v * ω (α u) (β v) = ∑ u, ∑ v, W u v * ω (α v) (β u) := Finset.sum_comm
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  rw [s, ← Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fin.sum_univ_three]
  show 2 * ω (α u + α v) (β u + β v) * W u v + 2 * ω (α u) (β u) * -W u v + 2 * ω (α v) (β v) * -W u v = _
  rw [hω₁, hω₂, hω₂]
  ring

theorem lam_subst {L : LB G.left} (hL : L.IsLB) (hi : LBIso L (matLB P pr W)) {T : Over S} (x y : T ⟶ G)
    {f f' : G ⟶ G} {m m' : Matrix (Fin n) (Fin n) ℤ} (hf : ∀ u, f ≫ pr u = ∏ v, pr v ^ m u v)
    (hf' : ∀ u, f' ≫ pr u = ∏ v, pr v ^ m' u v) :
    lam (cls L hL) (x ≫ f) (y ≫ f') =
      form (pairCls (cls P hP)) (m.transpose * (W + W.transpose) * m') (coord pr x) (coord pr y) := by
  have h := LB.isLB_linComb hP (fun uv : Fin n × Fin n => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)
  have e : ∀ (x : T ⟶ G) (f : G ⟶ G) (m : Matrix (Fin n) (Fin n) ℤ), (∀ u, f ≫ pr u = ∏ v, pr v ^ m u v) →
      coord pr (x ≫ f) = fun u => ∏ v, coord pr x v ^ m u v := fun x f m hf => funext fun u => by
    let F : (G ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
    refine (Category.assoc _ _ _).trans ((congrArg F (hf u)).trans ((map_prod F _ _).trans ?_))
    exact Finset.prod_congr rfl fun v _ => map_zpow F _ _
  rw [(cls_eq_iff hL h).2 hi, lam_matLB hP hb hpr, e x f m hf, e y f' m' hf', form_subst_left (hb.mul _) (hb.symm _),
    form_subst_right (hb.mul _) (hb.symm _)]

end GlobalTheory.MatrixBundle
