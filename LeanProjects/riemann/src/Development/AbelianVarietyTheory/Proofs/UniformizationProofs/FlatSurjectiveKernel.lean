import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CanonicalRigidImages

namespace GlobalTheory.GtCoordCompare

section Calc

variable {Y W W' Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {ψ : K → (W ⟶ Y)} {ψ' : K → (W' ⟶ Y)}
  {ε ε' : K → ℤ} {r : Z ⟶ W} {r' : Z ⟶ W'}

theorem trF_congr (h : ∀ k, r ≫ ψ k = r' ≫ ψ' k) (ε : K → ℤ) (z : Z) (j j' : K → L.ι) :
    trF ψ ε r z j j' = trF ψ' ε r' z j j' :=
  Finset.prod_congr rfl fun k _ => by rw [h k]

theorem trF_cancel (h : ∀ k, r ≫ ψ k = r' ≫ ψ' k) (hε : ∀ k, ε' k = -ε k) (z : Z) (j j' : K → L.ι) :
    trF ψ ε r z j j' * trF ψ' ε' r' z j j' = 1 := by
  rw [trF_congr h, trF, trF, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ => by rw [hε, zpow_neg, mul_inv_cancel]

theorem mem_congr (h : ∀ k, r ≫ ψ k = r' ≫ ψ' k) {z : Z} {j : K → L.ι} (hz : r z ∈ LB.wchart L ψ j) :
    r' z ∈ LB.wchart L ψ' j :=
  Set.mem_iInter.2 fun k => (congrArg (fun f => f z ∈ L.U (j k)) (h k)).mp (Set.mem_iInter.1 hz k)

theorem exists_wchart (hL : L.IsLB) (ψ : K → (W ⟶ Y)) (w : W) : ∃ j, w ∈ LB.wchart L ψ j := by
  choose j hj using fun k => exists_chart hL (ψ k w)
  exact ⟨j, Set.mem_iInter.2 hj⟩

theorem sval_mul_val (s : LB.Sec (LB.LinComb L ψ ε)) {x : LB.Gen (LB.LinComb L ψ' ε')} (hx : x.IsGen)
    (hε : ∀ k, ε' k = -ε k) (h : ∀ k, r ≫ ψ k = r' ≫ ψ' k) {z : Z} {J} (hJ : Good L z J) {j : K → L.ι}
    (hj : r z ∈ LB.wchart L ψ j) : sval s r z J * (val x r' z J).val =
      gs r z (LB.wchart L ψ j) (s.f j) * (gm r' z (LB.wchart L ψ' j) (x.s j)).val := by
  rw [val_of x r' z J (fun k => J (r ≫ ψ k)) (fun k => by rw [h k]), sec_trans s r z hj (hJ.mem ψ r),
    gen_trans hx r' z (mem_congr h hj) (mem_congr h (hJ.mem ψ r)), Units.val_mul, _root_.mul_mul_mul_comm,
    ← Units.val_mul, trF_cancel h hε, Units.val_one, _root_.one_mul]
  rfl

def toTop (U : W.Opens) : Γ(W, U) →+* Γ(U.toScheme, ⊤) := (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom

theorem toTop_bijective (U : W.Opens) : Function.Bijective (toTop U) := by
  have e : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]; rfl
  rw [toTop, e]
  exact ConcreteCategory.bijective_of_isIso U.topIso.inv

theorem gs_toTop (U : W.Opens) (r : Z ⟶ U.toScheme) (z : Z) (a : Γ(W, U)) :
    gs r z ⊤ (toTop U a) = gs (r ≫ U.ι) z U a := gs_appLE U.ι U ⊤ _ r z trivial a

theorem ext_open {U : W.Opens} {a b : Γ(W, U)} (h : ∀ y : U.toScheme, gs U.ι y U a = gs U.ι y U b) : a = b :=
  (toTop_bijective U).1 (fn_ext fun y _ => by rw [gs_toTop, gs_toTop, Category.id_comp, h])

theorem ext_pull (q : W' ⟶ W) [Flat q] [Surjective q] {U : W.Opens} {a b : Γ(W, U)}
    (h : ∀ y, q y ∈ U → gs q y U a = gs q y U b) : a = b :=
  FunDescent.app_injective q U (fn_ext fun y hy => by
    rw [gs_pull (𝟙 _) q y U hy, gs_pull (𝟙 _) q y U hy, Category.id_comp]; exact h y hy)

theorem gs_zero' (r : Z ⟶ W) (z : Z) (U : W.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  rw [gs_eq r z U h, map_zero, map_zero]

end Calc

section Image

variable {Y G B : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] (q : G ⟶ B) {φ : K → (B ⟶ Y)} {φ' : K → (G ⟶ Y)}
  {ε ε' : K → ℤ}

def Img (x : LB.Gen (LB.LinComb L φ' ε')) (V : B.Opens) (s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε))
    (a : Γ(G, q ⁻¹ᵁ V)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ V.toScheme) (g : Z ⟶ G), r ≫ V.ι = g ≫ q → ∀ (z : Z) (j : K → L.ι),
    r z ∈ LB.wchart L (fun k => V.ι ≫ φ k) j → gs g z (q ⁻¹ᵁ V) a =
      gs r z (LB.wchart L (fun k => V.ι ≫ φ k) j) (s.f j) * (gm g z (LB.wchart L φ' j) (x.s j)).val

variable {q} {x : LB.Gen (LB.LinComb L φ' ε')} {V : B.Opens}

omit [Fintype K] in
theorem comp_φ (hφ : ∀ k, φ' k = q ≫ φ k) {Z : Scheme.{0}} {r : Z ⟶ V.toScheme} {g : Z ⟶ G} (e : r ≫ V.ι = g ≫ q)
    (k : K) : r ≫ V.ι ≫ φ k = g ≫ φ' k := by
  rw [hφ, reassoc_of% e]

theorem mem_of_comp {Z : Scheme.{0}} {r : Z ⟶ V.toScheme} {g : Z ⟶ G} (e : r ≫ V.ι = g ≫ q) (z : Z) :
    g z ∈ q ⁻¹ᵁ V := (congrArg (fun f => f z ∈ V) e).mp (r z).2

theorem secRel_iff_img (hL : L.IsLB) (hx : x.IsGen) (hε : ∀ k, ε' k = -ε k) (hφ : ∀ k, φ' k = q ≫ φ k)
    (s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε)) (a : Γ(G, q ⁻¹ᵁ V)) :
    GeneratorPullback.SecRel L _ _ (fnSec L (toTop _ a)) _ _ s (q ∣_ V) _ _ (LB.pullGen L _ _ x (q ⁻¹ᵁ V).ι) ↔ Img q x V s a := by
  have f : ∀ {Z : Scheme.{0}} (l : Z ⟶ (q ⁻¹ᵁ V).toScheme) (z : Z) (J), Good L z J →
      sval (fnSec L (toTop _ a)) l z J = gs (l ≫ (q ⁻¹ᵁ V).ι) z _ a := fun l z J hJ =>
    (gs_res l z le_top (hJ.mem PEmpty.elim l) _).trans (gs_toTop _ l z a)
  have p := isPullback_morphismRestrict q V
  obtain ⟨h₁, h₂⟩ := secRel_iff hL _ _ (fnSec L (toTop _ a)) _ _ s (q ∣_ V) _ _ (LB.pullGen L _ _ x (q ⁻¹ᵁ V).ι)
  refine ⟨fun H Z r g e z j hj => ?_, fun H => h₂ fun y J hJ => ?_⟩
  · obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
    have E := h₁ H Z (p.lift r g e) z J hJ
    rw [f _ z J hJ, val_pull hJ, p.lift_fst, p.lift_snd] at E
    exact E.trans (sval_mul_val s hx hε (comp_φ hφ e) hJ hj)
  · rw [f _ y J hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact H _ _ _ p.w y _ (hJ.mem _ _) |>.trans (sval_mul_val s hx hε (comp_φ hφ p.w) hJ (hJ.mem _ _)).symm

theorem Img.eq_zero [Flat q] [Surjective q] {s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε)} (H : Img q x V s 0)
    (j : K → L.ι) : s.f j = 0 := by
  have p := isPullback_morphismRestrict q V
  have : Flat (q ∣_ V) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : Surjective (q ∣_ V) := MorphismProperty.of_isPullback (P := @Surjective) p.flip ‹_›
  refine ext_pull (q ∣_ V) fun y hy => ?_
  have E := H _ _ _ p.w y j hy
  rw [gs_zero' _ y _ (mem_of_comp p.w y)] at E
  exact ((Units.mul_left_eq_zero _).1 E.symm).trans (gs_zero' _ y _ hy).symm

theorem preimage_le (hφ : ∀ k, φ' k = q ≫ φ k) {j : K → L.ι} (h : V ≤ LB.wchart L φ j) :
    q ⁻¹ᵁ V ≤ LB.wchart L φ' j := fun y hy =>
  mem_congr (r := q) (r' := 𝟙 G) (fun k => by rw [hφ, Category.id_comp]) (h hy)

def locU (hφ : ∀ k, φ' k = q ≫ φ k) (x : LB.Gen (LB.LinComb L φ' ε')) {j : K → L.ι} (h : V ≤ LB.wchart L φ j) :
    Γ(G, q ⁻¹ᵁ V)ˣ := res (preimage_le hφ h) (x.s j)

theorem gm_locU (hφ : ∀ k, φ' k = q ≫ φ k) (x : LB.Gen (LB.LinComb L φ' ε')) {j : K → L.ι} (h : V ≤ LB.wchart L φ j)
    {Z : Scheme.{0}} (g : Z ⟶ G) (z : Z) (m : g z ∈ q ⁻¹ᵁ V) :
    gm g z (q ⁻¹ᵁ V) (locU hφ x h) = gm g z (LB.wchart L φ' j) (x.s j) := gm_res g z _ m _

theorem mem_wchart_ι {j : K → L.ι} (h : V ≤ LB.wchart L φ j) (y : V.toScheme) :
    y ∈ LB.wchart L (fun k => V.ι ≫ φ k) j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h y.2) k

theorem Img.exists_fn (hφ : ∀ k, φ' k = q ≫ φ k) {s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε)}
    {a : Γ(G, q ⁻¹ᵁ V)} (H : Img q x V s a) {j : K → L.ι} (h : V ≤ LB.wchart L φ j) :
    ∃ c, a = (q.app V).hom c * (locU hφ x h).val := by
  have p := isPullback_morphismRestrict q V
  obtain ⟨c, hc⟩ := (toTop_bijective V).2 ((V.toScheme.presheaf.map (homOfLE
    (fun y _ => mem_wchart_ι h y : ⊤ ≤ LB.wchart L (fun k => V.ι ≫ φ k) j)).op).hom (s.f j))
  refine ⟨c, ext_open fun y => ?_⟩
  have m := mem_of_comp p.w y
  rw [H _ _ _ p.w y j (mem_wchart_ι h _), gs_mul _ y _ m, gs_pull _ q y V m, gs_unit _ y _ m, gm_locU _ _ _ _ y m,
    ← p.w, ← gs_toTop, hc]
  exact congrArg (· * _) (gs_res (q ∣_ V) y (V := ⊤) _ trivial _).symm

theorem exists_img_of_fn (hL : L.IsLB) (hx : x.IsGen) (hε : ∀ k, ε' k = -ε k) (hφ : ∀ k, φ' k = q ≫ φ k)
    {j₀ : K → L.ι} (h : V ≤ LB.wchart L φ j₀) (c : Γ(B, V)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε),
      Img q x V s ((q.app V).hom c * (locU hφ x h).val) ∧ (s.f j₀ = 0 → c = 0) := by
  obtain ⟨f, hf⟩ : ∃ f : ∀ j, Γ(V.toScheme, LB.wchart L (fun k => V.ι ≫ φ k) j), ∀ (Z : Scheme.{0})
      (r : Z ⟶ V.toScheme) (z : Z) j, r z ∈ LB.wchart L (fun k => V.ι ≫ φ k) j →
      gs r z _ (f j) = (trF (fun k => V.ι ≫ φ k) ε r z j j₀).val * gs (r ≫ V.ι) z V c :=
    ⟨fun j => (res (V := LB.wchart L (fun k => V.ι ≫ φ k) j) (le_inf le_rfl fun y _ => mem_wchart_ι h y)
        ((LB.LinComb L (fun k => V.ι ≫ φ k) ε).g j j₀)).val * (V.ι.appLE V _ (fun y _ => y.2)).hom c,
      fun Z r z j hj => (gs_mul r z _ hj _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hj _).trans
        (congrArg Units.val ((gm_res r z _ hj _).trans (gm_linComb L _ ε r z j j₀ hj (mem_wchart_ι h _)))))
        (gs_appLE V.ι V _ _ r z hj c))⟩
  refine ⟨⟨f, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r g e z j hj => ?_, fun h0 => ext_open fun y => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (hf _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ ε (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 _) y _ hy _).trans (hf _ _ y j' hy.2)))).symm)
    rw [← trF_trans hL _ ε (𝟙 _) y hy.1 hy.2 (mem_wchart_ι h _), Units.val_mul, _root_.mul_assoc]
    rfl
  · have m := mem_of_comp e z
    refine Eq.trans ?_ (congrArg (· * _) (hf Z r z j hj)).symm
    rw [gs_mul _ z _ m, gs_pull _ q z V m, gs_unit _ z _ m, gm_locU _ _ _ _ z m,
      gen_trans hx g z (mem_congr (comp_φ hφ e) hj) (preimage_le hφ h m), Units.val_mul, mul_comm _ (gs (r ≫ _) z V c),
      _root_.mul_assoc, ← _root_.mul_assoc (Units.val _), ← Units.val_mul, trF_cancel (comp_φ hφ e) hε,
      Units.val_one, _root_.one_mul, e]
  · have E := hf _ (𝟙 _) y j₀ (mem_wchart_ι h _)
    have h0' : f j₀ = 0 := h0
    rw [h0', gs_zero' _ y _ (mem_wchart_ι h _), Category.id_comp] at E
    exact ((Units.mul_right_eq_zero _).1 E.symm).trans (gs_zero' V.ι y V y.2).symm

end Image

section Group

variable {S Y : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B] {q : G ⟶ B}
  {i : splitTorus S X ⟶ G} {L : LB Y} {K : Type} [Fintype K] {ε ε' : K → ℤ}

def WtGen (i : splitTorus S X ⟶ G) {φ' : K → (G.left ⟶ Y)} (x : LB.Gen (LB.LinComb L φ' ε')) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
    val x ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val x g.left z J

theorem act_comp [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hi, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  exact congrArg (fun f => f.left) e

theorem act_mem [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
    (z : Z.left) {W : B.left.Opens} (h : g.left z ∈ q.left ⁻¹ᵁ W) : ((t ≫ i) * g).left z ∈ q.left ⁻¹ᵁ W :=
  (congrArg (fun f => f z ∈ W) (act_comp hi t g)).mpr h

theorem isWt_of_gs {V : G.left.Opens} {a : Γ(G.left, V)} {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ∀ z : Z.left,
      gs ((t ≫ i) * g).left z V a = (gm t.left z ⊤ (charUnit S X χ)).val * gs g.left z V a) : IsWt i V a χ :=
  fun Z t g h₁ h₂ => fn_ext fun z hz => by
    rw [gs_mul _ z _ hz, gs_appLE _ _ _ _ _ z hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp, Category.id_comp,
      h Z t g h₂ z]
    congr 1
    refine ((gs_pull (𝟙 _) t.left z ⊤ trivial _).trans ?_).symm
    rw [Category.id_comp, gs_unit _ z ⊤ trivial]

theorem isWt_app [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (W : B.left.Opens) (c : Γ(B.left, W)) :
    IsWt i (q.left ⁻¹ᵁ W) ((q.left.app W).hom c) 0 := isWt_of_gs fun Z t g h z => by
  rw [gs_pull _ _ z W (act_mem hi t g z (h trivial)), gs_pull _ _ z W (h trivial), act_comp hi, gm_charUnit, chV_zero,
    map_one, Units.val_one, _root_.one_mul]

section One

variable [IsMonHom q] (hi : i ≫ q = toUnit _ ≫ η[B]) (hL : L.IsLB) {φ : K → (B.left ⟶ Y)} {φ' : K → (G.left ⟶ Y)}
  (hφ : ∀ k, φ' k = q.left ≫ φ k) {x : LB.Gen (LB.LinComb L φ' ε')} (hx : x.IsGen) {χ : X} (hw : WtGen i x χ)
include hi hL hφ hx hw

theorem gm_wt {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) {j : K → L.ι}
    (hj : g.left z ∈ LB.wchart L φ' j) : gm ((t ≫ i) * g).left z (LB.wchart L φ' j) (x.s j) =
      gm t.left z ⊤ (charUnit S X χ) * gm g.left z (LB.wchart L φ' j) (x.s j) := by
  have e : ∀ k, g.left ≫ φ' k = ((t ≫ i) * g).left ≫ φ' k := fun k => by
    rw [hφ, reassoc_of% (act_comp hi t g)]
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
  have v := hw Z t g z J hJ
  rw [val_of x _ z J (fun k => J (g.left ≫ φ' k)) (fun k => by rw [e k])] at v
  rw [gen_trans hx _ z (mem_congr e hj) (mem_congr e (hJ.mem φ' g.left)), gen_trans hx _ z hj (hJ.mem φ' g.left), v,
    ← trF_congr e, mul_left_comm]
  rfl

theorem isWt_locU {V : B.left.Opens} {j : K → L.ι} (h : V ≤ LB.wchart L φ j) : IsWt i _ (locU hφ x h).val χ :=
  isWt_of_gm _ _ fun Z t g z hz => by
    rw [gm_locU _ _ _ _ z hz, gm_locU _ _ _ _ z (act_mem hi t g z hz)]
    exact gm_wt hi hL hφ hx hw t g z (preimage_le hφ h hz)

theorem Img.isWt {V : B.left.Opens} {s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε)} {a : Γ(G.left, q.left ⁻¹ᵁ V)}
    (H : Img q.left x V s a) : IsWt i _ a χ := isWt_of_gs fun Z t g h z => by
  obtain ⟨r, e⟩ : ∃ r, r ≫ V.ι = g.left ≫ q.left := ⟨_, IsOpenImmersion.lift_fac V.ι (g.left ≫ q.left) (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h (Set.mem_univ w))⟩
  obtain ⟨j, hj⟩ := exists_wchart hL (fun k => V.ι ≫ φ k) (r z)
  rw [H _ r _ e z j hj, H _ r _ (e.trans (act_comp hi t g).symm) z j hj,
    gm_wt hi hL hφ hx hw t g z (mem_congr (comp_φ hφ e) hj), Units.val_mul, mul_left_comm]

omit hi in
theorem exists_img [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q η[B]) (hε : ∀ k, ε' k = -ε k) {V : B.left.Opens}
    {a : Γ(G.left, q.left ⁻¹ᵁ V)} (ha : IsWt i _ a χ) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ k) ε), Img q.left x V s a := by
  have ex : ∀ j, ∃ c : Γ(B.left, V ⊓ LB.wchart L φ j), (q.left.app _).hom c =
      (G.left.presheaf.map (homOfLE (q.left.preimage_mono inf_le_left)).op).hom a *
        ((locU hφ x (inf_le_right : V ⊓ LB.wchart L φ j ≤ _))⁻¹).val := fun j =>
    (invariant_functions_descend S G B _ q i ‹_› ‹_› ‹_› ‹_› ‹_› hk _).2.2 _ fun Z t g h₁ h₂ => by
      have := (ha.res (q.left.preimage_mono (inf_le_left : V ⊓ LB.wchart L φ j ≤ V))).mul
        (isWt_locU hk.w hL hφ hx hw (inf_le_right : V ⊓ LB.wchart L φ j ≤ _)).inv
      rw [this Z t g h₁ h₂, add_neg_cancel, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  choose c hc using ex
  have le : ∀ j, LB.wchart L (fun k => V.ι ≫ φ k) j ≤ V.ι ⁻¹ᵁ (V ⊓ LB.wchart L φ j) := fun j y hy =>
    ⟨y.2, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ V.toScheme) (g : Z ⟶ G.left), r ≫ V.ι = g ≫ q.left → ∀ (z : Z) j,
      r z ∈ LB.wchart L (fun k => V.ι ≫ φ k) j → gs r z _ ((V.ι.appLE _ _ (le j)).hom (c j)) =
        gs g z (q.left ⁻¹ᵁ V) a * ((gm g z (LB.wchart L φ' j) (x.s j))⁻¹).val := fun Z r g e z j hj => by
    have m : g z ∈ q.left ⁻¹ᵁ (V ⊓ LB.wchart L φ j) :=
      (congrArg (fun f => f z ∈ V ⊓ LB.wchart L φ j) e).mp (le j hj)
    rw [gs_appLE _ _ _ _ r z hj, e, ← gs_pull g q.left z _ m, hc, gs_mul g z _ m, gs_res g z _ m, gs_unit g z _ m,
      map_inv, gm_locU _ _ _ g z m]
  have p := isPullback_morphismRestrict q.left V
  have : Flat (q.left ∣_ V) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : Surjective (q.left ∣_ V) := MorphismProperty.of_isPullback (P := @Surjective) p.flip ‹_›
  refine ⟨⟨fun j => (V.ι.appLE _ _ (le j)).hom (c j), fun j j' => ext_pull (q.left ∣_ V) fun y hy => ?_⟩,
    fun Z r g e z j hj => ?_⟩
  · refine ((gs_res _ y _ hy _).trans (key _ _ _ p.w y j hy.1)).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ ε (q.left ∣_ V) y j j' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (key _ _ _ p.w y j' hy.2)))).symm)
    rw [gen_trans hx _ y (mem_congr (comp_φ hφ p.w) hy.1) (mem_congr (comp_φ hφ p.w) hy.2), mul_inv,
      ← eq_inv_of_mul_eq_one_left (trF_cancel (comp_φ hφ p.w) hε y j j'), Units.val_mul, mul_left_comm]
    rfl
  · refine Eq.trans ?_ (congrArg (· * _) (key Z r g e z j hj)).symm
    rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end One

theorem isWt_monomial {κ : Type} (b : Module.Basis κ ℤ X) {V : G.left.Opens} (u : κ → Γ(G.left, V)ˣ)
    (hu : ∀ k, IsWt i V (u k).val (b k)) :
    ∃ m : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, IsWt i V (m (Multiplicative.ofAdd χ)).val χ := by
  let m : Multiplicative X →* Γ(G.left, V)ˣ :=
    AddMonoidHom.toMultiplicativeLeft (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hm : ∀ k, m (Multiplicative.ofAdd (b k)) = u k := fun k =>
    congrArg Additive.toMul (b.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  refine ⟨m, fun χ => ?_⟩
  have hχ : χ ∈ AddSubgroup.closure (Set.range b) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, b.span_eq]; trivial
  refine AddSubgroup.closure_induction (p := fun x _ => IsWt i V (m (Multiplicative.ofAdd x)).val x) ?_ ?_ ?_ ?_ hχ
  · rintro _ ⟨k, rfl⟩
    rw [hm]; exact hu k
  · rw [ofAdd_zero, map_one]; exact isWt_one
  · intro x y _ _ hx hy
    rw [ofAdd_add, map_mul]; exact hx.mul hy
  · intro x _ hx
    rw [ofAdd_neg, map_inv]; exact hx.inv

section All

variable [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] (hL : L.IsLB) (hε : ∀ k, ε' k = -ε k)
  {φ : X → K → (B.left ⟶ Y)} {φ' : X → K → (G.left ⟶ Y)} (hφ : ∀ χ k, φ' χ k = q.left ≫ φ χ k)
  {x : ∀ χ, LB.Gen (LB.LinComb L (φ' χ) ε')} (hx : ∀ χ, (x χ).IsGen) (hw : ∀ χ, WtGen i (x χ) χ)
include hL hε hφ hx hw

theorem exists_sum_img [Flat q.left] [Surjective q.left] (hk : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens}
    (hV : IsAffineOpen V) (f : Γ(G.left, q.left ⁻¹ᵁ V)) :
    ∃ (F : Finset X) (s : ∀ χ, LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ χ k) ε)) (a : X → Γ(G.left, q.left ⁻¹ᵁ V)),
      (∀ χ, Img q.left (x χ) V (s χ) (a χ)) ∧ f = ∑ χ ∈ F, a χ := by
  obtain ⟨a, ha, e⟩ := (functions_graded_by_weights S G X i ‹_› (q.left ⁻¹ᵁ V) (hV.preimage q.left)
    (fun z hz => act_mem hk.w (fst _ _) (snd _ _) z hz)).1 f
  choose s hs using fun χ => exists_img hL (hφ χ) (hx χ) (hw χ) hk hε (ha χ)
  exact ⟨a.support, s, a, hs, e⟩

omit hL hε hφ hx hw [IsMonHom i] in

theorem eq_zero_of_sum_isWt (hi : i ≫ q = toUnit _ ≫ η[B]) {V : B.left.Opens} (hV : IsAffineOpen V) {F : Finset X}
    {a : X → Γ(G.left, q.left ⁻¹ᵁ V)}
    (H : ∀ χ ∈ F, IsWt i _ (a χ) χ) (e : ∑ χ ∈ F, a χ = 0) {χ : X} (hχ : χ ∈ F) : a χ = 0 := by
  classical
  have := TorusGrading.eq_zero_of_sum_isWt (i := i) (hV.preimage q.left)
    (fun z hz => act_mem hi (fst _ _) (snd _ _) z hz) (s := F) (a := fun χ => if χ ∈ F then a χ else 0)
    (fun χ => by
      by_cases h : χ ∈ F
      · rw [if_pos h]; exact H χ h
      · rw [if_neg h]; exact isWt_zero χ)
    ((Finset.sum_congr rfl fun χ h => if_pos h).trans e) hχ
  rwa [if_pos hχ] at this

theorem flat_surjective_kernel [Module.Free ℤ X] [Module.Finite ℤ X] (hi : i ≫ q = toUnit _ ≫ η[B])
    (span : ∀ V : B.left.Opens, IsAffineOpen V → ∀ f : Γ(G.left, q.left ⁻¹ᵁ V),
      ∃ (F : Finset X) (s : ∀ χ, LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ χ k) ε)) (a : X → Γ(G.left, q.left ⁻¹ᵁ V)),
        (∀ χ ∈ F, Img q.left (x χ) V (s χ) (a χ)) ∧ f = ∑ χ ∈ F, a χ)
    (indep : ∀ V : B.left.Opens, IsAffineOpen V → ∀ s : LB.Sec (LB.LinComb L (fun k => V.ι ≫ φ 0 k) ε),
      Img q.left (x 0) V s 0 → ∀ j, s.f j = 0) :
    Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit _) q η[B] := by
  classical
  obtain ⟨mono, fl, su, -, fib⟩ := LocTriv.main S X G B i q ‹_› ‹_› fun y => by
    let b := Module.Free.chooseBasis ℤ X
    choose j hj using fun χ => exists_wchart hL (φ χ) y
    obtain ⟨V, hV, hy, le⟩ := exists_isAffineOpen_mem_and_subset (x := y)
      (U := LB.wchart L (φ 0) (j 0) ⊓ ⨅ k, LB.wchart L (φ (b k)) (j (b k)))
      ⟨hj 0, (TopologicalSpace.Opens.coe_iInf _).ge (Set.mem_iInter.2 fun k => hj (b k))⟩
    have le₀ : V ≤ LB.wchart L (φ 0) (j 0) := fun _ h => (le h).1
    have le₁ : ∀ k, V ≤ LB.wchart L (φ (b k)) (j (b k)) := fun k _ h =>
      iInf_le (fun k => LB.wchart L (φ (b k)) (j (b k))) k (le h).2
    refine ⟨V, hy, hV, fun a => ⟨fun ha => ?_, ?_⟩, (injective_iff_map_eq_zero _).2 fun c hc => ?_,
      fun z hz => act_mem hi (fst _ _) (snd _ _) z hz,
      isWt_monomial b _ fun k => isWt_locU hi hL (hφ _) (hx _) (hw _) (le₁ k)⟩
    · obtain ⟨F, s, d, hd, e⟩ := span V hV (a * (locU (hφ 0) (x 0) le₀).val)
      have w := ha.mul (isWt_locU hi hL (hφ _) (hx _) (hw _) le₀)
      rw [add_zero] at w
      generalize hf : a * (locU (hφ 0) (x 0) le₀).val = f at e w
      have z := eq_zero_of_sum_isWt hi hV (F := insert 0 F)
        (a := fun χ => (if χ ∈ F then d χ else 0) - if χ = 0 then f else 0) (fun χ _ Z t g h₁ h₂ => by
          have a₁ : IsWt i _ (if χ ∈ F then d χ else 0) χ := by
            by_cases h : χ ∈ F
            · rw [if_pos h]; exact (hd χ h).isWt hi hL (hφ χ) (hx χ) (hw χ)
            · rw [if_neg h]; exact isWt_zero χ
          have a₂ : IsWt i _ (if χ = 0 then f else 0) χ := by
            by_cases h : χ = 0
            · rw [if_pos h, h]; exact w
            · rw [if_neg h]; exact isWt_zero χ
          rw [map_sub, map_sub, a₁ Z t g h₁ h₂, a₂ Z t g h₁ h₂, mul_sub])
        (by
          rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_eq', if_pos (Finset.mem_insert_self _ _),
            Finset.inter_eq_right.2 (Finset.subset_insert _ _), ← e, sub_self])
        (Finset.mem_insert_self _ _)
      rw [if_pos rfl, sub_eq_zero] at z
      by_cases h : (0 : X) ∈ F
      · rw [if_pos h] at z
        obtain ⟨c, hc⟩ := (hd 0 h).exists_fn (hφ 0) le₀
        exact ⟨c, (Units.mul_left_inj _).1 (hc.symm.trans (z.trans hf.symm))⟩
      · rw [if_neg h] at z
        exact ⟨0, (map_zero _).trans ((Units.mul_left_eq_zero _).1 (hf.trans z.symm)).symm⟩
    · rintro ⟨c, rfl⟩
      exact isWt_app hi V c
    · obtain ⟨s, hs, h0⟩ := exists_img_of_fn hL (hx 0) hε (hφ 0) le₀ c
      rw [hc, zero_mul] at hs
      exact h0 (indep V hV s hs _)
  refine ⟨fl, su, ⟨hi⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => ((fib _ 1 c.fst).1 (by
    rw [MonObj.one_comp, c.condition, Hom.one_def, toUnit_unique c.snd])).choose) (fun c => ?_)
    (fun c => toUnit_unique _ _) fun c m h _ => ?_⟩⟩
  · exact (_root_.mul_one _).symm.trans (Exists.choose_spec (p := fun t => c.fst = (t ≫ i) * 1) _).symm
  · rw [← cancel_mono i, h]
    exact (Exists.choose_spec (p := fun t => c.fst = (t ≫ i) * 1) _).trans (_root_.mul_one _)

end All

end Group

end GlobalTheory.GtCoordCompare
