import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.FieldBaseChange

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Fn

variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}

def constHom (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : R →+* Γ(Y, U) :=
  ((Y.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem constHom_apply (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) (c : R) :
    constHom π U c = resTop U (scal π c) := rfl

def constVal (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (c : R) : Z.presheaf.stalk z :=
  gs π z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)

theorem gs_scal (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal π c) = constVal (r ≫ π) z c := gs_pull r π z ⊤ trivial _

theorem gs_const (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (resTop U (scal π c)) = constVal (r ≫ π) z c :=
  (gs_res r z le_top h _).trans (gs_scal π r z c)

theorem constVal_specMap (π : Z ⟶ Spec (CommRingCat.of R')) (φ : R →+* R') (z : Z) (c : R) :
    constVal (π ≫ Spec.map (CommRingCat.ofHom φ)) z c = constVal π z (φ c) := by
  refine (gs_pull π (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial _).symm.trans (congrArg (gs π z ⊤) ?_)
  have := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

theorem gs_zero' (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  simp only [gs_eq r z U h, map_zero]

def FnOver (_π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : Type := Γ(Y, U)

instance (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : CommRing (FnOver π U) :=
  inferInstanceAs (CommRing Γ(Y, U))

instance (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : Algebra R (FnOver π U) :=
  (constHom π U).toAlgebra

theorem gs_smul (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R)
    (a : FnOver π U) : gs r z U (c • a : FnOver π U) = constVal (r ≫ π) z c * gs r z U a :=
  (gs_mul r z U h _ _).trans (congrArg (· * _) (gs_const π r z U h c))

def pullFn {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')} {φ : R →+* R'}
    {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom φ)) {U : Y.Opens} {U' : Y'.Opens}
    (h : U' ≤ p ⁻¹ᵁ U) : FnOver π U →ₛₗ[φ] FnOver π' U' where
  toFun a := (Y'.presheaf.map (homOfLE h).op).hom ((p.app U).hom a)
  map_add' a b := by erw [map_add, map_add]; rfl
  map_smul' c a := fn_ext fun y hy => by
    have v : ∀ b : Γ(Y, U), gs (𝟙 Y') y U' ((Y'.presheaf.map (homOfLE h).op).hom ((p.app U).hom b)) =
        gs p y U b := fun b => (gs_res _ y h hy _).trans ((gs_pull _ p y U (h hy) b).trans (by rw [Category.id_comp]))
    refine (v _).trans ((gs_smul π p y U (h hy) c a).trans (Eq.trans ?_ (gs_smul π' _ y U' hy _ _).symm))
    rw [hp, constVal_specMap, Category.id_comp]
    exact congrArg _ (v a).symm

theorem gs_pullFn {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')} {φ : R →+* R'}
    {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom φ)) {U : Y.Opens} {U' : Y'.Opens}
    (h : U' ≤ p ⁻¹ᵁ U) (a : FnOver π U) (r : Z ⟶ Y') (z : Z) (hz : r z ∈ U') :
    gs r z U' (pullFn hp h a) = gs (r ≫ p) z U a :=
  (gs_res r z h hz _).trans (gs_pull r p z U (h hz) a)

def resFn (π : Y ⟶ Spec (CommRingCat.of R)) {U V : Y.Opens} (h : V ≤ U) : FnOver π U →ₗ[R] FnOver π V where
  toFun a := (Y.presheaf.map (homOfLE h).op).hom a
  map_add' a b := map_add _ _ _
  map_smul' c a := fn_ext fun y hy =>
    (gs_res _ y h hy _).trans ((gs_smul π _ y U (h hy) c a).trans
      (Eq.trans (congrArg _ (gs_res _ y h hy _).symm) (gs_smul π _ y V hy _ _).symm))

end Fn

section Sec

variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}

def SecOver (_π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) : Type := LB.Sec M

variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)

instance : Zero (SecOver π M) := ⟨SecOps.secZero⟩
instance : Add (SecOver π M) := ⟨SecOps.secAdd⟩
instance : Neg (SecOver π M) := ⟨SecOps.secNeg⟩
instance : SMul R (SecOver π M) := ⟨fun c => SecOps.secScale (scal π c)⟩

def chartFun (j : M.ι) (s : SecOver π M) : FnOver π (M.U j) := LB.Sec.f s j

theorem SecOver.ext {s t : SecOver π M} (h : ∀ j, chartFun π M j s = chartFun π M j t) : s = t :=
  SecOps.sec_ext h

instance : AddCommGroup (SecOver π M) where
  add_assoc a b c := SecOver.ext π M fun j => add_assoc (chartFun π M j a) _ _
  zero_add a := SecOver.ext π M fun j => zero_add (chartFun π M j a)
  add_zero a := SecOver.ext π M fun j => add_zero (chartFun π M j a)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := SecOver.ext π M fun j => neg_add_cancel (chartFun π M j a)
  add_comm a b := SecOver.ext π M fun j => add_comm (chartFun π M j a) _

instance : Module R (SecOver π M) where
  one_smul a := SecOver.ext π M fun j => one_smul R (chartFun π M j a)
  mul_smul x y a := SecOver.ext π M fun j => mul_smul x y (chartFun π M j a)
  smul_zero x := SecOver.ext π M fun j => smul_zero (A := FnOver π (M.U j)) x
  smul_add x a b := SecOver.ext π M fun j => smul_add x (chartFun π M j a) _
  add_smul x y a := SecOver.ext π M fun j => add_smul x y (chartFun π M j a)
  zero_smul a := SecOver.ext π M fun j => zero_smul R (chartFun π M j a)

def chartLin (j : M.ι) : SecOver π M →ₗ[R] FnOver π (M.U j) where
  toFun := chartFun π M j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

section Val

variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem sval_add' (s t : SecOver π (LB.LinComb L φ ε)) :
    sval (s + t : SecOver π _) r z J = sval s r z J + sval t r z J := gs_add r z _ (hJ.mem φ r) _ _

theorem sval_smul' (c : R) (s : SecOver π (LB.LinComb L φ ε)) :
    sval (c • s : SecOver π _) r z J = constVal (r ≫ π) z c * sval s r z J :=
  gs_smul π r z _ (hJ.mem φ r) c _

theorem sval_zero' : sval (0 : SecOver π (LB.LinComb L φ ε)) r z J = 0 :=
  (gs_eq r z _ (hJ.mem φ r) _).trans (by erw [map_zero, map_zero])

theorem sval_sum' {I : Type} (S : Finset I) (s : I → SecOver π (LB.LinComb L φ ε)) :
    sval (∑ i ∈ S, s i : SecOver π _) r z J = ∑ i ∈ S, sval (s i) r z J := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, sval_zero' hJ]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add' hJ, ih]

end Val

theorem sec_ext' (hL : L.IsLB) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = sval s' (𝟙 Y) y J) : s = s' :=
  SecOps.sec_ext (sec_ext_val hL h)

theorem mem_wchart {j : K → L.ι} {y : Y} : y ∈ LB.wchart L φ j ↔ ∀ k, φ k y ∈ L.U (j k) :=
  Set.mem_iInter

theorem wchart_eq {φ' : K → (Y' ⟶ X)} {p : Y' ⟶ Y} (hφ : ∀ k, φ' k = p ≫ φ k) (j : K → L.ι) :
    LB.wchart L φ' j = p ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : φ' = fun k => p ≫ φ k := funext hφ
  ext y
  exact (mem_wchart (φ := fun k => p ≫ φ k)).trans (mem_wchart (φ := φ) (y := p y)).symm

theorem trF_comp {φ' : K → (Y' ⟶ X)} {p : Y' ⟶ Y} (hφ : ∀ k, φ' k = p ≫ φ k) (r : Z ⟶ Y') (z : Z)
    (j j' : K → L.ι) : Geo.Tor.trF φ' ε r z j j' = Geo.Tor.trF φ ε (r ≫ p) z j j' :=
  Finset.prod_congr rfl fun k _ => by rw [hφ, Category.assoc]

variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)

variable (L ε) in

def pullOver : SecOver π (LB.LinComb L φ ε) →ₛₗ[f] SecOver π' (LB.LinComb L φ' ε) where
  toFun s :=
    { f := fun j => pullFn hp (wchart_eq hφ j).le (chartFun π (LB.LinComb L φ ε) j s)
      compat := fun j j' => fn_ext fun y hy => by
        refine ((gs_res _ y _ hy _).trans (gs_pullFn hp _ _ _ y hy.1)).trans (Eq.trans ?_
          ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
            (congrArg Units.val (gm_linComb L φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
            ((gs_res _ y _ hy _).trans (gs_pullFn hp _ _ _ y hy.2)))).symm)
        exact (sec_trans s (𝟙 Y' ≫ p) y ((wchart_eq hφ j).le hy.1) ((wchart_eq hφ j').le hy.2)).trans
          (congrArg (fun u : (Y'.presheaf.stalk y)ˣ => u.val * _) (trF_comp hφ _ y j j').symm) }
  map_add' s t := SecOver.ext _ _ fun j => map_add (pullFn hp (wchart_eq hφ j).le) _ _
  map_smul' c s := SecOver.ext _ _ fun j => map_smulₛₗ (pullFn hp (wchart_eq hφ j).le) _ _

theorem sval_pullOver (s : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullOver L ε hp hφ s) r z J = sval s (r ≫ p) z J := by
  rw [sval_of s (r ≫ p) z J (fun k => J (r ≫ φ' k)) (fun k => by rw [hφ, Category.assoc])]
  exact gs_pullFn hp _ _ r z (hJ.mem φ' r)

theorem secLin_iff_val (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c ↔ ∀ y J, Good L y J →
      sval s₁ (𝟙 Y') y J = ∑ i, gs (𝟙 Y') y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ h) y J := by
  have key : ∀ (y : Y') (j₁ : K' → L.ι) (j₂ : K → L.ι)
      (hm : y ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ j₂),
      gs (𝟙 Y') y _ (∑ i, resTop _ (c i) * (Y'.presheaf.map (homOfLE a₂).op).hom
        ((h.app (LB.wchart L φ j₂)).hom ((s i).f j₂))) =
        ∑ i, gs (𝟙 Y') y ⊤ (c i) * gs (𝟙 Y' ≫ h) y (LB.wchart L φ j₂) ((s i).f j₂) := fun y j₁ j₂ hm a₂ => by
    refine ((gs_eq _ y _ hm _).trans (by rw [map_sum, map_sum])).trans (Finset.sum_congr rfl fun i _ =>
      (gs_eq _ y _ hm _).symm.trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hm _)
        ((gs_res _ y a₂ hm _).trans (gs_pull _ h y _ (a₂ hm) _)))))
  constructor
  · intro H y J hJ
    simp only [sval_of (s _) (𝟙 Y' ≫ h) y J (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ₁ (fun k => J (𝟙 Y' ≫ φ₁ k)) ⊓
        LB.wchart L (fun k => h ≫ φ k) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) :=
      ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
    have e := H (fun k => J (𝟙 Y' ≫ φ₁ k)) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (𝟙 Y' ≫ q)) e)
    exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs (𝟙 Y') y _) e).trans (key y _ _ hm _))
  · intro H j₁ j₂ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a)
      exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k))] at this
    simp only [sval_of (s _) (𝟙 Y' ≫ h) y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
    exact (gs_res _ y _ hy _).trans (this.trans (key y _ _ hy _).symm)

theorem secScal_iff_val (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Γ(Y', ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ ε s h c ↔ ∀ y J, Good L y J →
      sval s (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J := by
  have key : ∀ (y : Y') (j₁ : K' → L.ι) (j₂ : K → L.ι)
      (hm : y ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂)
      (a₁ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ LB.wchart L φ₁ j₁)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ j₂),
      gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE a₂).op).hom ((h.app (LB.wchart L φ j₂)).hom (s.f j₂))) =
        gs (𝟙 Y' ≫ h) y (LB.wchart L φ j₂) (s.f j₂) ∧
      gs (𝟙 Y') y _ (resTop _ c * (Y'.presheaf.map (homOfLE a₁).op).hom (s₁.f j₁)) =
        gs (𝟙 Y') y ⊤ c * gs (𝟙 Y') y (LB.wchart L φ₁ j₁) (s₁.f j₁) := fun y j₁ j₂ hm a₁ a₂ =>
    ⟨(gs_res _ y a₂ hm _).trans (gs_pull _ h y _ (a₂ hm) _),
      (gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hm _) (gs_res _ y a₁ hm _))⟩
  constructor
  · intro H y J hJ
    rw [sval_of s (𝟙 Y' ≫ h) y J (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L φ₁ (fun k => J (𝟙 Y' ≫ φ₁ k)) ⊓
        LB.wchart L (fun k => h ≫ φ k) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) :=
      ⟨hJ.mem φ₁ _, hJ.mem (fun k => h ≫ φ k) _⟩
    have e := H (fun k => J (𝟙 Y' ≫ φ₁ k)) (fun k => J (𝟙 Y' ≫ h ≫ φ k)) (by
      rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (𝟙 Y' ≫ q)) e)
    obtain ⟨k₁, k₂⟩ := key y _ _ hm _ _
    exact k₁.symm.trans ((congrArg (gs (𝟙 Y') y _) e).trans k₂)
  · intro H j₁ j₂ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a)
      exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
      sval_of s _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr k))] at this
    obtain ⟨k₁, k₂⟩ := key y _ _ hy _ _
    exact k₁.trans (this.trans k₂.symm)

theorem secScal_iff (hL : L.IsLB) (s₁ : SecOver π' (LB.LinComb L φ' ε)) (s : SecOver π (LB.LinComb L φ ε))
    {S : Type} [CommRing S] (π₀ : Y' ⟶ Spec (CommRingCat.of S)) (g : S →+* R')
    (h₀ : π₀ = π' ≫ Spec.map (CommRingCat.ofHom g)) (c : S) :
    GeneratorPullback.SecScal L φ' ε s₁ φ ε s p (scal π₀ c) ↔ pullOver L ε hp hφ s = g c • s₁ := by
  refine (secScal_iff_val hL s₁ s p _).trans ?_
  have e : ∀ y J, Good L y J → (sval s (𝟙 Y' ≫ p) y J = gs (𝟙 Y') y ⊤ (scal π₀ c) * sval s₁ (𝟙 Y') y J ↔
      sval (pullOver L ε hp hφ s) (𝟙 Y') y J = sval (g c • s₁ : SecOver π' _) (𝟙 Y') y J) := fun y J hJ => by
    rw [sval_pullOver hp hφ s _ hJ, sval_smul' hJ, gs_scal, h₀, ← Category.assoc, constVal_specMap]
  exact ⟨fun H => sec_ext' hL fun y J hJ => (e y J hJ).1 (H y J hJ),
    fun H y J hJ => (e y J hJ).2 (by rw [H])⟩

theorem secLin_iff (hL : L.IsLB) {φ₁ : K' → (Y' ⟶ X)} {ε₁ : K' → ℤ} (s₁ : SecOver π' (LB.LinComb L φ₁ ε₁))
    {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (c : Fin n → R')
    (t : Fin n → SecOver π' (LB.LinComb L φ₁ ε₁))
    (ht : ∀ i y J, Good L y J → sval (t i) (𝟙 Y') y J = sval (s i) (𝟙 Y' ≫ h) y J) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h (fun i => scal π' (c i)) ↔ s₁ = ∑ i, c i • t i := by
  refine (secLin_iff_val hL s₁ s h _).trans ?_
  have e : ∀ y J, Good L y J → ∑ i, gs (𝟙 Y') y ⊤ (scal π' (c i)) * sval (s i) (𝟙 Y' ≫ h) y J =
      sval (∑ i, c i • t i : SecOver π' _) (𝟙 Y') y J := fun y J hJ => by
    rw [sval_sum' hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, gs_scal, ht i y J hJ]
  exact ⟨fun H => sec_ext' hL fun y J hJ => (H y J hJ).trans (e y J hJ),
    fun H y J hJ => by rw [e y J hJ, H]⟩

end Sec

section Field

variable {K F : Type} [Field K] [Field F] [Algebra K F] {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F)))) [NoetherianSpace Y]

theorem isExtension_pullFn {U : Y.Opens} {U' : Y'.Opens} (h : U' = p ⁻¹ᵁ U) :
    IsExtension (pullFn H.w h.le) := by
  subst h
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (NoetherianSpace.isCompact _) (fun _ _ _ _ _ _ _ _ => NoetherianSpace.isCompact _))
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom (algebraMap K F)) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra K (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower K (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have : Algebra.IsPushout K F (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  refine isExtension_of_isPushout _ fun x => ?_
  show (Y'.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]; rfl

variable {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} (ε : I → ℤ) {φ' : I → (Y' ⟶ X)}
  (hφ : ∀ k, φ' k = p ≫ φ k)

include hL in

theorem isExtension_pullOver : IsExtension (pullOver L ε H.w hφ) := by
  obtain ⟨T, hT⟩ := (NoetherianSpace.isCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun j : I → L.ι => (LB.wchart L φ j : Set Y)) (fun j => (LB.wchart L φ j).isOpen) (fun y _ => by
      choose j hj using fun k => exists_chart hL (φ k y)
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iInter.2 hj⟩)
  refine IsExtension.of_proj (J := I → L.ι) _ (fun j => pullFn H.w (wchart_eq hφ j).le)
    (fun j => isExtension_pullFn H (wchart_eq hφ j)) (chartLin π (LB.LinComb L φ ε))
    (chartLin π' (LB.LinComb L φ' ε)) (fun _ _ => rfl) (fun x hx => SecOver.ext _ _ hx) T
    (fun v hv => SecOver.ext _ _ fun j => fn_ext fun y hy => ?_) fun ℓ Λ hΛ x => ?_
  · obtain ⟨t, ht, hy'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    refine (sec_trans v (𝟙 Y) y hy hy').trans ?_
    have z : gs (𝟙 Y) y (LB.wchart L φ t) (LB.Sec.f v t) = 0 :=
      (congrArg (gs (𝟙 Y) y (LB.wchart L φ t)) (hv t ht)).trans (gs_zero' _ y _ hy')
    exact ((congrArg _ z).trans (mul_zero _)).trans (gs_zero' _ y _ hy).symm
  · refine ⟨⟨fun j => Λ j (chartFun π' (LB.LinComb L φ' ε) j x), fun (i j : I → L.ι) => ?_⟩, fun j => rfl⟩
    have e : LB.wchart L φ' i ⊓ LB.wchart L φ' j = p ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j) := by
      rw [wchart_eq hφ, wchart_eq hφ]; rfl
    obtain ⟨Λ', hΛ'⟩ := (isExtension_pullFn H e).coord ℓ
    have e₁ := IsCoord.natural (isExtension_pullFn H (wchart_eq hφ i)).span (hΛ i) hΛ'
      (resFn π inf_le_left) (resFn π' inf_le_left) (fun v => fn_ext fun y hy =>
        ((gs_res _ y _ hy _).trans (gs_pullFn H.w _ _ _ y hy.1)).trans
          ((gs_pullFn H.w _ _ _ y hy).trans (gs_res (𝟙 Y' ≫ p) y _ (e.le hy) _)).symm) (chartFun π' (LB.LinComb L φ' ε) i x)
    have e₂ := IsCoord.natural (isExtension_pullFn H (wchart_eq hφ j)).span (hΛ j) hΛ'
      (LinearMap.mulLeft K (show FnOver π _ from ((LB.LinComb L φ ε).g i j).val) ∘ₗ resFn π inf_le_right)
      (LinearMap.mulLeft F (show FnOver π' _ from ((LB.LinComb L φ' ε).g i j).val) ∘ₗ resFn π' inf_le_right)
      (fun v => fn_ext fun y hy => by
        refine ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
            (congrArg Units.val (gm_linComb L φ' ε (𝟙 Y') y i j hy.1 hy.2)))
            ((gs_res _ y _ hy _).trans (gs_pullFn H.w _ _ _ y hy.2)))).trans (Eq.symm ?_)
        have hy' : (𝟙 Y' ≫ p) y ∈ LB.wchart L φ i ⊓ LB.wchart L φ j := e.le hy
        refine (gs_pullFn H.w _ _ _ y hy).trans ((gs_mul _ y _ hy' _ _).trans (congrArg₂ (· * ·)
          ((gs_unit _ y _ hy' _).trans (congrArg Units.val
            ((gm_linComb L φ ε (𝟙 Y' ≫ p) y i j hy'.1 hy'.2).trans (trF_comp hφ _ y i j).symm)))
          (gs_res _ y _ hy' _)))) (chartFun π' (LB.LinComb L φ' ε) j x)
    exact e₁.symm.trans ((congrArg Λ' (LB.Sec.compat x i j)).trans e₂)

end Field

end GlobalTheory.FieldBaseChange
