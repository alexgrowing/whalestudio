import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.LeafAugInjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity.TubeCut

namespace UpperTheory.Cb.ConeDifferentials

variable {R : Type} [CommRing R]

abbrev Sx (E : Spc) (n : ℕ) (T : Scheme.{0}ᵒᵖ) : Type := (E.obj (op (SimplexCategory.mk n))).obj T

def gen (E : Spc) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (s : Sx E n T) : ((((chainsP R).obj E).X n).obj T) :=
  Finsupp.single (ULift.up s) 1

theorem res_gen (E : Spc) (n : ℕ) {T T' : Scheme.{0}ᵒᵖ} (f : T ⟶ T') (s : Sx E n T) :
    ((((chainsP R).obj E).X n).map f).hom (gen E n T s) = gen E n T' (((E.obj (op (SimplexCategory.mk n))).map f) s) :=
  Finsupp.mapDomain_single

theorem aug_gen {E E' : Spc} (g : E ⟶ E') (n : ℕ) (T : Scheme.{0}ᵒᵖ) (s : Sx E n T) :
    ((((chainsP R).map g).f n).app T).hom (gen E n T s) = gen E' n T (((g.app _).app T) s) :=
  Finsupp.mapDomain_single

theorem d_gen (E : Spc) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (s : Sx E (n+1) T) :
    (((((chainsP R).obj E).d (n+1) n).app T).hom (gen E (n+1) T s)) =
      ∑ i : Fin (n+2), ((-1 : ℤ)^(i:ℕ)) • gen E n T (((E.δ i).app T) s) := by
  have hd : ((chainsP R).obj E).d (n+1) n =
      ∑ i : Fin (n+2), ((-1 : ℤ)^(i:ℕ)) • (freeP R).map (E.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ n
  rw [hd, NatTrans.app_sum]
  erw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [NatTrans.app_zsmul]
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply]
  congr 1
  exact Finsupp.mapDomain_single

section Elt
variable {J : Type} [Preorder J] (Z : J ⥤ PSh)

abbrev ch {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) n T) : Fin (n+1) ⥤ (Z.flip.obj T).Elements :=
  chn (n := op (SimplexCategory.mk n)) x

theorem ch_δ_obj {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) (n+1) T) (i : Fin (n+2)) (k : Fin (n+1)) :
    (ch Z (((hoc Z).δ i).app T x)).obj k = (ch Z x).obj (i.succAbove k) := rfl

instance {T : Scheme.{0}ᵒᵖ} : Quiver.IsThin (Z.flip.obj T).Elements := fun a b => by
  change Subsingleton {f : a.1 ⟶ b.1 // _}
  infer_instance

theorem sx_ext {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x y : Sx (hoc Z) n T)
    (h : ∀ k, (ch Z x).obj k = (ch Z y).obj k) : x = y := by
  have ht : Quiver.IsThin (Z.flip.obj T).Elements := inferInstance
  exact ComposableArrows.ext (F := ch Z x) (G := ch Z y) h (fun _ _ => (ht _ _).elim _ _)

def cone {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) n T) (e : (Z.flip.obj T).Elements)
    (φ : e ⟶ (ch Z x).obj 0) : Sx (hoc Z) (n+1) T :=
  ComposableArrows.precomp (n := n) (ch Z x) φ

def pt {T : Scheme.{0}ᵒᵖ} (e : (Z.flip.obj T).Elements) : Sx (hoc Z) 0 T :=
  ComposableArrows.mk₀ e

theorem cone_δ_zero {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) n T) (e : (Z.flip.obj T).Elements)
    (φ : e ⟶ (ch Z x).obj 0) : ((hoc Z).δ 0).app T (cone Z x e φ) = x := by
  exact sx_ext Z _ _ fun k => rfl

theorem cone_δ_succ {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) (n+1) T) (e : (Z.flip.obj T).Elements)
    (φ : e ⟶ (ch Z x).obj 0) (i : Fin (n+2)) (φ' : e ⟶ (ch Z (((hoc Z).δ i).app T x)).obj 0) :
    ((hoc Z).δ i.succ).app T (cone Z x e φ) = cone Z (((hoc Z).δ i).app T x) e φ' := by
  apply sx_ext
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · change (ch Z (cone Z x e φ)).obj (i.succ.succAbove j.succ) = (ch Z x).obj (i.succAbove j)
    rw [Fin.succ_succAbove_succ]
    rfl

theorem cone_δ_one {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) 0 T) (e : (Z.flip.obj T).Elements)
    (φ : e ⟶ (ch Z x).obj 0) : ((hoc Z).δ 1).app T (cone Z x e φ) = pt Z e := by
  apply sx_ext
  intro k
  rw [Fin.fin_one_eq_zero k]
  rfl

def under {n : ℕ} {T : Scheme.{0}ᵒᵖ} (x : Sx (hoc Z) (n+1) T) (e : (Z.flip.obj T).Elements)
    (φ : e ⟶ (ch Z x).obj 0) (i : Fin (n+2)) : e ⟶ (ch Z (((hoc Z).δ i).app T x)).obj 0 :=
  φ ≫ (ch Z x).map (homOfLE (Fin.zero_le _))

end Elt

section Abs
variable {J : Type} [Preorder J] (Z : J ⥤ PSh) {T W : Scheme.{0}ᵒᵖ} (f : T ⟶ W)
  {Y : Type} (π : ∀ n, Sx (hoc Z) n T → Y) (e : Y → (Z.flip.obj W).Elements)

abbrev rs {n : ℕ} (s : Sx (hoc Z) n T) : Sx (hoc Z) n W := ((hoc Z).obj (op (SimplexCategory.mk n))).map f s

def Good {n : ℕ} (s : Sx (hoc Z) n T) : Prop := Nonempty (e (π n s) ⟶ (ch Z (rs Z f s)).obj 0)

open Classical in

def L (R : Type) [CommRing R] (n : ℕ) (s : Sx (hoc Z) n T) : (((chainsP R).obj (hoc Z)).X (n+1)).obj W :=
  if h : Good Z f π e s then gen (hoc Z) (n+1) W (cone Z (rs Z f s) (e (π n s)) h.some) else 0

def Lh (R : Type) [CommRing R] (n : ℕ) : (((chainsP R).obj (hoc Z)).X n).obj T →ₗ[ULift.{1} R] (((chainsP R).obj (hoc Z)).X (n+1)).obj W :=
  Finsupp.linearCombination (ULift.{1} R) (fun s : ULift (Sx (hoc Z) n T) => L Z f π e R n s.down)

theorem Lh_gen (R : Type) [CommRing R] (n : ℕ) (s : Sx (hoc Z) n T) : Lh Z f π e R n (gen (hoc Z) n T s) = L Z f π e R n s := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul _ _)

theorem rs_δ {n : ℕ} (s : Sx (hoc Z) (n+1) T) (i : Fin (n+2)) :
    rs Z f (((hoc Z).δ i).app T s) = ((hoc Z).δ i).app W (rs Z f s) := by
  exact (FunctorToTypes.naturality ((hoc Z).δ i) f s).symm

theorem good_δ (hπ : ∀ n (s : Sx (hoc Z) (n+1) T) i, π n (((hoc Z).δ i).app T s) = π (n+1) s)
    {n : ℕ} {s : Sx (hoc Z) (n+1) T} (h : Good Z f π e s) (i : Fin (n+2)) : Good Z f π e (((hoc Z).δ i).app T s) := by
  unfold Good
  rw [hπ, rs_δ]
  exact ⟨h.some ≫ (ch Z (rs Z f s)).map (homOfLE (Fin.zero_le _))⟩

end Abs

section Key
variable {J : Type} [Preorder J] (Z : J ⥤ PSh) {T W : Scheme.{0}ᵒᵖ} (f : T ⟶ W)
  {Y : Type} (π : ∀ n, Sx (hoc Z) n T → Y) (e : Y → (Z.flip.obj W).Elements)

theorem cone_congr {n : ℕ} {x x' : Sx (hoc Z) n W} {a a' : (Z.flip.obj W).Elements} (hx : x = x') (ha : a = a')
    (φ : a ⟶ (ch Z x).obj 0) (φ' : a' ⟶ (ch Z x').obj 0) : cone Z x a φ = cone Z x' a' φ' := by
  subst hx
  subst ha
  have ht : Quiver.IsThin (Z.flip.obj W).Elements := inferInstance
  rw [(ht _ _).elim φ φ']

theorem L_good (R : Type) [CommRing R] {n : ℕ} {s : Sx (hoc Z) n T} (h : Good Z f π e s) :
    L Z f π e R n s = gen (hoc Z) (n+1) W (cone Z (rs Z f s) (e (π n s)) h.some) := dif_pos h

theorem key_succ (R : Type) [CommRing R]
    (hπ : ∀ n (s : Sx (hoc Z) (n+1) T) i, π n (((hoc Z).δ i).app T s) = π (n+1) s)
    {n : ℕ} (s : Sx (hoc Z) (n+1) T) (h : Good Z f π e s) :
    (((((chainsP R).obj (hoc Z)).d (n+2) (n+1)).app W).hom (L Z f π e R (n+1) s)) +
      Lh Z f π e R n (((((chainsP R).obj (hoc Z)).d (n+1) n).app T).hom (gen (hoc Z) (n+1) T s)) =
    gen (hoc Z) (n+1) W (rs Z f s) := by
  rw [L_good Z f π e R h, d_gen, Fin.sum_univ_succ, d_gen, map_sum, cone_δ_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, map_zsmul, Lh_gen]
  rw [add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
  intro j _
  have hg := good_δ Z f π e hπ h j
  rw [L_good Z f π e R hg, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_add_eq_zero,
    cone_δ_succ Z (rs Z f s) _ _ j (under Z (rs Z f s) _ h.some j)]
  congr 2
  apply cone_congr
  · exact (rs_δ Z f s j).symm
  · rw [hπ]

theorem key_zero (R : Type) [CommRing R] (s : Sx (hoc Z) 0 T) (h : Good Z f π e s) :
    (((((chainsP R).obj (hoc Z)).d 1 0).app W).hom (L Z f π e R 0 s)) =
    gen (hoc Z) 0 W (rs Z f s) - gen (hoc Z) 0 W (pt Z (e (π 0 s))) := by
  rw [L_good Z f π e R h, d_gen, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, cone_δ_zero,
    cone_δ_one, ← sub_eq_add_neg]

end Key

section Lin
variable {R : Type} [CommRing R]

def Sup (E : Spc) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (z : (((chainsP R).obj E).X n).obj T) (G : Set (Sx E n T)) : Prop :=
  ∀ u : ULift (Sx E n T), (show ULift (Sx E n T) →₀ ULift.{1} R from z) u ≠ 0 → u.down ∈ G

theorem eq_on_sup {E : Spc} {n : ℕ} {T : Scheme.{0}ᵒᵖ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} R) M]
    (A B : (((chainsP R).obj E).X n).obj T →ₗ[ULift.{1} R] M) {G : Set (Sx E n T)}
    (h : ∀ s ∈ G, A (gen E n T s) = B (gen E n T s)) (z : (((chainsP R).obj E).X n).obj T)
    (hz : Sup E n T z G) : A z = B z := by
  let w : ULift (Sx E n T) →₀ ULift.{1} R := z
  have hw : z = ∑ u ∈ w.support, w u • gen E n T u.down := by
    change w = _
    conv_lhs => rw [← Finsupp.sum_single w]
    simp only [Finsupp.sum, gen]
    refine Finset.sum_congr rfl fun u _ => ?_
    change Finsupp.single u (w u) = w u • Finsupp.single u (1 : ULift.{1} R)
    rw [Finsupp.smul_single_one]
  rw [hw, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, map_smul, h _ (hz u (Finsupp.mem_support_iff.mp hu))]

theorem disc_d (P : PSh) (T : Scheme.{0}ᵒᵖ) (y : (((chainsP R).obj (disc.obj P)).X 1).obj T) :
    ((((chainsP R).obj (disc.obj P)).d 1 0).app T).hom y = 0 := by
  have hd : ((chainsP R).obj (disc.obj P)).d (0+1) 0 =
      ∑ i : Fin (0+2), ((-1 : ℤ)^(i:ℕ)) • (freeP R).map ((disc.obj P).δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ 0
  have h0 : ((chainsP R).obj (disc.obj P)).d 1 0 = 0 := by
    rw [hd, Fin.sum_univ_two]
    simp [SimplicialObject.δ, disc]
    rfl
  rw [h0]
  rfl

end Lin

section Bd
variable {J : Type} [Preorder J] (Z : J ⥤ PSh) {T W : Scheme.{0}ᵒᵖ} (f : T ⟶ W) {R : Type} [CommRing R]
  {Y : Type} (π : ∀ n, Sx (hoc Z) n T → Y) (e : Y → (Z.flip.obj W).Elements)

theorem bdy_succ (hπ : ∀ n (s : Sx (hoc Z) (n+1) T) i, π n (((hoc Z).δ i).app T s) = π (n+1) s)
    {n : ℕ} (z : (((chainsP R).obj (hoc Z)).X (n+1)).obj T) (hc : Cyc _ (n+1) T z)
    (hz : Sup (hoc Z) (n+1) T z {s | Good Z f π e s}) :
    Bdy ((chainsP R).obj (hoc Z)) (n+1) W (((((chainsP R).obj (hoc Z)).X (n+1)).map f).hom z) := by
  have hgen : ∀ s ∈ {s | Good Z f π e s},
      ((((((chainsP R).obj (hoc Z)).d (n+2) (n+1)).app W).hom ∘ₗ Lh Z f π e R (n+1)) +
        Lh Z f π e R n ∘ₗ ((((chainsP R).obj (hoc Z)).d (n+1) n).app T).hom) (gen (hoc Z) (n+1) T s) =
      ((((chainsP R).obj (hoc Z)).X (n+1)).map f).hom (gen (hoc Z) (n+1) T s) := by
    intro s hs
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Lh_gen,
      key_succ Z f π e R hπ s hs, res_gen]
  have hA := eq_on_sup _ _ hgen z hz
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hc n, map_zero, add_zero] at hA
  exact ⟨_, hA⟩

def Qh {P : PSh} (e : P.obj T → (Z.flip.obj W).Elements) :
    (((chainsP R).obj (disc.obj P)).X 0).obj T →ₗ[ULift.{1} R] (((chainsP R).obj (hoc Z)).X 0).obj W :=
  Finsupp.linearCombination (ULift.{1} R) (fun s : ULift (P.obj T) => gen (hoc Z) 0 W (pt Z (e s.down)))

theorem Qh_gen {P : PSh} (e : P.obj T → (Z.flip.obj W).Elements) (y : P.obj T) :
    Qh (R := R) Z (T := T) e (gen (disc.obj P) 0 T y) = gen (hoc Z) 0 W (pt Z (e y)) := by
  exact (Finsupp.linearCombination_single _ _ _).trans (one_smul _ _)

abbrev pa {P : PSh} (a : hoc Z ⟶ disc.obj P) (T : Scheme.{0}ᵒᵖ) (n : ℕ) (s : Sx (hoc Z) n T) : P.obj T :=
  (a.app (op (SimplexCategory.mk n))).app T s

theorem pa_δ {P : PSh} (a : hoc Z ⟶ disc.obj P) (T : Scheme.{0}ᵒᵖ) (n : ℕ) (s : Sx (hoc Z) (n+1) T) (i : Fin (n+2)) :
    pa Z a T n (((hoc Z).δ i).app T s) = pa Z a T (n+1) s :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality (SimplexCategory.δ i).op) T) s

theorem bdy_abs {P : PSh} (a : hoc Z ⟶ disc.obj P) (e : P.obj T → (Z.flip.obj W).Elements)
    {n : ℕ} (z : (((chainsP R).obj (hoc Z)).X n).obj T) (hc : Cyc _ n T z)
    (hb : Bdy _ n T ((((chainsP R).map a).f n).app T |>.hom z))
    (hz : Sup (hoc Z) n T z {s | Good Z f (pa Z a T) e s}) :
    Bdy ((chainsP R).obj (hoc Z)) n W (((((chainsP R).obj (hoc Z)).X n).map f).hom z) := by
  cases n with
  | succ k => exact bdy_succ Z f (pa Z a T) e (fun k s i => pa_δ Z a T k s i) z hc hz
  | zero =>
    obtain ⟨y, hy⟩ := hb
    have ha0 : ((((chainsP R).map a).f 0).app T).hom z = 0 := by
      rw [← hy]
      exact disc_d P T y
    have hgen : ∀ s ∈ {s | Good Z f (pa Z a T) e s},
        ((((((chainsP R).obj (hoc Z)).d 1 0).app W).hom ∘ₗ Lh Z f (pa Z a T) e R 0) +
          Qh (R := R) Z e ∘ₗ ((((chainsP R).map a).f 0).app T).hom) (gen (hoc Z) 0 T s) =
        ((((chainsP R).obj (hoc Z)).X 0).map f).hom (gen (hoc Z) 0 T s) := by
      intro s hs
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Lh_gen,
        key_zero Z f _ e R s hs, aug_gen, Qh_gen, res_gen, sub_add_cancel]
    have hA := eq_on_sup _ _ hgen z hz
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, ha0, map_zero,
      add_zero] at hA
    exact ⟨_, hA⟩

end Bd

section Geo

theorem exists_below {J : Type} [Preorder J] {X : Scheme.{0}} (r : J → Set X)
    (hcov : ∀ x : X, ∃ j, x ∈ r j)
    (hdir : ∀ (x : X) j k, x ∈ r j → x ∈ r k → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ r l)
    (y : X) (S : Finset J) (hS : ∀ j ∈ S, y ∈ r j) : ∃ l, y ∈ r l ∧ ∀ j ∈ S, l ≤ j := by
  classical
  induction S using Finset.induction_on with
  | empty => obtain ⟨j, hj⟩ := hcov y; exact ⟨j, hj, by simp⟩
  | insert a S _ ih =>
    obtain ⟨l, hl, hb⟩ := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    obtain ⟨m, hma, hml, hm⟩ := hdir y a l (hS a (Finset.mem_insert_self _ _)) hl
    refine ⟨m, hm, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hma
    · exact hml.trans (hb j hj)

theorem exists_open {T : Scheme.{0}} (t : T) {Y : Type} (F : Finset Y) (O : Y → T.Opens) (h : ∀ p ∈ F, t ∈ O p) :
    ∃ V : T.Opens, t ∈ V ∧ ∀ p ∈ F, V ≤ O p := by
  classical
  refine ⟨F.inf O, ?_, fun p hp => Finset.inf_le hp⟩
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a F), ih fun p hp => h p (Finset.mem_insert_of_mem hp)⟩

theorem coc_eq {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {j k : J} (g : j ⟶ k) : D.map g ≫ c k = c j := by
  apply yoneda.map_injective
  simpa using hc j k g

theorem aug_val {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) {T : Scheme.{0}ᵒᵖ} {n : ℕ} (s : Sx (hoc (D ⋙ yoneda)) n T) :
    pa (D ⋙ yoneda) (aug _ hc) T n s =
      (show T.unop ⟶ D.obj ((ch _ s).obj 0).1 from ((ch _ s).obj 0).2) ≫ c ((ch _ s).obj 0).1 := rfl

end Geo

theorem main : EtaleAugInjAt := by
  classical
  intro J _ D X c hopen hcov hdir hc R _ n T x hx hb t
  let Z := D ⋙ yoneda
  let xs : ULift (Sx (hoc Z) n T) →₀ ULift.{1} R := x
  let v : ULift (Sx (hoc Z) n T) → (Z.flip.obj T).Elements := fun u => (ch Z u.down).obj 0
  let g : ULift (Sx (hoc Z) n T) → (T.unop ⟶ X) := fun u => pa Z (aug _ hc) T n u.down
  have hg : ∀ u, g u = (show T.unop ⟶ D.obj (v u).1 from (v u).2) ≫ c (v u).1 :=
    fun u => aug_val D c hc u.down
  let S : (T.unop ⟶ X) → Finset J := fun g' =>
    ((xs.support).filter (fun u => g u = g')).image (fun u => (v u).1)
  have hS : ∀ g', ∀ j ∈ S g', g' t ∈ Set.range (c j) := by
    intro g' j hj
    simp only [S, Finset.mem_image, Finset.mem_filter] at hj
    obtain ⟨u, ⟨-, rfl⟩, rfl⟩ := hj
    rw [hg u]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  choose l hl1 hl2 using fun g' =>
    exists_below (fun j => Set.range (c j)) hcov hdir (g' t) (S g') (hS g')
  obtain ⟨V, htV, hVO⟩ := exists_open t (xs.support.image g) (fun g' => g' ⁻¹ᵁ (c (l g')).opensRange)
    (fun g' _ => hl1 g')
  refine ⟨V, htV, ?_⟩
  rcases xs.support.eq_empty_or_nonempty with hF | ⟨u0, -⟩
  · have hx0 : x = 0 := Finsupp.support_eq_empty.mp hF
    rw [hx0, map_zero]
    exact ⟨0, map_zero _⟩
  let e : (T.unop ⟶ X) → (Z.flip.obj (op V)).Elements := fun g' =>
    if h : Set.range (V.ι ≫ g').base ⊆ Set.range (c (l g')).base then
      ⟨l g', IsOpenImmersion.lift (c (l g')) (V.ι ≫ g') h⟩
    else ⟨(v u0).1, V.ι ≫ (show T.unop ⟶ D.obj (v u0).1 from (v u0).2)⟩
  refine bdy_abs Z V.ι.op (aug _ hc) e x hx hb ?_
  intro u hu
  have hsu : u ∈ xs.support := Finsupp.mem_support_iff.mpr hu
  have hmem : g u ∈ xs.support.image g := Finset.mem_image_of_mem g hsu
  have hrange : Set.range (V.ι ≫ g u).base ⊆ Set.range (c (l (g u))).base := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ V := by
      exact (Scheme.Opens.range_ι V).le ⟨w, rfl⟩
    exact hVO _ hmem hw
  have hle : l (g u) ≤ (v u).1 :=
    hl2 _ _ (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hsu, rfl⟩, rfl⟩)
  have he : e (g u) = ⟨l (g u), IsOpenImmersion.lift (c (l (g u))) (V.ι ≫ g u) hrange⟩ :=
    dif_pos hrange
  show Nonempty (e (g u) ⟶ _)
  rw [he]
  refine ⟨⟨homOfLE hle, ?_⟩⟩
  change IsOpenImmersion.lift (c (l (g u))) (V.ι ≫ g u) hrange ≫ D.map (homOfLE hle) =
    V.ι ≫ (show T.unop ⟶ D.obj (v u).1 from (v u).2)
  rw [← cancel_mono (c (v u).1), Category.assoc, coc_eq D c hc, IsOpenImmersion.lift_fac,
    Category.assoc, ← hg u]

end UpperTheory.Cb.ConeDifferentials

theorem UpperTheory.Cb.hocolimAugmentation_injective_of_purity_inputs :
    LateralTheory.CohomologicalPurity.LeafAW → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.LeafHens → LateralTheory.CohomologicalPurity.LeafIndExc → LateralTheory.CohomologicalPurity.LeafThom → LateralTheory.CohomologicalPurity.LeafChart → LateralTheory.CohomologicalPurity.LeafCl → LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInjAt :=
  fun _ _ _ _ _ _ _ _ => UpperTheory.Cb.ConeDifferentials.main
