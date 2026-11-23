import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

section Reg

variable {X X' Y W : Scheme.{0}} (L : LB X) (L' : LB X')

def tr {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (I : (Y ⟶ X) → L.ι) (ψ : Y ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U (I ψ)) (L.g (J (r ≫ ψ)) (I ψ))

def Reg (F : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ)
    (c : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U) : Prop :=
  ∀ (y : Y) I I', Good L y I → Good L' y I' → ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' →
      F Z r z J J' = c _ (tr L r z J I) (tr L' r z J' I') * gm r z V u

variable {L L'}
variable {F G : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ}
  {c d : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U}

theorem Reg.mul (hF : Reg L L' F c) (hG : Reg L L' G d) :
    Reg L L' (fun Z r z J J' => F Z r z J J' * G Z r z J J') (fun U _ h h' => c U h h' * d U h h') := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  obtain ⟨V', hV', u', hu'⟩ := hG y I I' hI hI'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, res inf_le_left u * res inf_le_right u', fun Z r z J J' hz hJ hJ' => ?_⟩
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz]
  show F Z r z J J' * G Z r z J J' = _
  rw [hu Z r z J J' hz.1 hJ hJ', hu' Z r z J J' hz.2 hJ hJ', _root_.mul_mul_mul_comm]

theorem Reg.inv (hF : Reg L L' F c) :
    Reg L L' (fun Z r z J J' => (F Z r z J J')⁻¹) (fun U _ h h' => (c U h h')⁻¹) := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  refine ⟨V, hV, u⁻¹, fun Z r z J J' hz hJ hJ' => ?_⟩
  show (F Z r z J J')⁻¹ = _
  rw [map_inv, hu Z r z J J' hz hJ hJ', mul_inv]

theorem good_exists {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem Reg.glue (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      F Z r z J J' = gm r z ⊤ a := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' → F Z r z J J' = gm r z V u := by
    intro y
    obtain ⟨I, hI⟩ := good_exists hL y
    obtain ⟨I', hI'⟩ := good_exists hL' y
    obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
    exact ⟨V, hV, u, fun Z r z J J' hz hJ hJ' => by rw [hu Z r z J J' hz hJ hJ', hc, _root_.one_mul]⟩
  choose V hV u hu using H
  obtain ⟨a, ha⟩ := glue_unit ⊤ V (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩) u
    (fun i j x hx => by
      obtain ⟨I, hI⟩ := good_exists hL x
      obtain ⟨I', hI'⟩ := good_exists hL' x
      exact (hu i _ (𝟙 Y) x I I' hx.1 hI hI').symm.trans (hu j _ (𝟙 Y) x I I' hx.2 hI hI'))
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hu (r z) Z r z J J' (hV _) hJ hJ', ← ha, gm_res r z _ (hV _)]

theorem Reg.rigid (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) {S : Scheme.{0}} (p : Y ⟶ S)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') : F Z r z J J' = F Z r' z J J' := by
  obtain ⟨a, ha⟩ := hF.glue hL hL' hc
  obtain ⟨a₀, e⟩ := hp a.val
  rw [ha Z r z J J' hJ hJ', ha Z r' z J J' hJ hJ']
  apply Units.ext
  have k : ∀ q : Z ⟶ Y, (gm q z ⊤ a).val = gs (q ≫ p) z ⊤ a₀ := fun q => by
    rw [← gs_unit q z ⊤ trivial, ← e]
    exact gs_pull q p z ⊤ trivial a₀
  rw [k, k, hr]

variable {K : Type} [Fintype K]

theorem reg_val {φ : K → (W ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z J _ => val t (r ≫ p) z J) (fun _ _ h _ => ∏ k, h (p ≫ φ k) ^ ε k) := by
  intro y I I' hI _
  refine ⟨p ⁻¹ᵁ LB.wchart L φ (fun k => I (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz hJ _ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

theorem reg_val' {φ : K → (W ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z _ J' => val t (r ≫ p) z J') (fun _ _ _ h' => ∏ k, h' (p ≫ φ k) ^ ε k) := by
  intro y I I' _ hI
  refine ⟨p ⁻¹ᵁ LB.wchart L' φ (fun k => I' (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz _ hJ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

def wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} (w : LB.Iso L' (LB.LinComb L pr ε)) {Z : Scheme.{0}} (q : Z ⟶ X') (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gv w q z (fun k => J (q ≫ pr k)) (J' q)

theorem reg_wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) (p : Y ⟶ X') :
    Reg L L' (fun _ r z J J' => wv w (r ≫ p) z J J') (fun _ _ h h' => (∏ k, h (p ≫ pr k) ^ ε k) * (h' p)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (LB.wchart L pr (fun k => I (p ≫ pr k)) ⊓ L'.U (I' p)), ⟨hI.mem pr p, hI' p⟩,
    pullU p _ (w.s (fun k => I (p ≫ pr k), I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gm_isGen hw (r ≫ p) z _ (fun k => I (p ≫ pr k)) _ (I' p) (hJ.mem pr (r ≫ p)) hz.1 (hJ' _) hz.2).trans
    (congrArg (· * _) (congrArg₂ (· * ·) ?_ rfl))
  refine (gm_linComb L pr ε (r ≫ p) z _ _ (hJ.mem pr (r ≫ p)) hz.1).trans ?_
  rfl

end Reg

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg in
theorem reg_lam {S S' Y : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)} (hw : w.IsGen) (p : Y ⟶ (G2 B').left) :
    Reg M M' (fun _ r z J J' => lamVal w (r ≫ p) z J J')
      (fun _ _ h h' => (∏ k, h ((p ≫ β₂) ≫ lamφ B k) ^ lamε k) * (∏ k, h' (p ≫ lamφ B' k) ^ lamε k)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (((abelian₂ B M).pull β₂).U (fun _ => ind B I (p ≫ β₂)) ⊓ (abelian₂ B' M').U (ind B' I' p)),
    ⟨mem_pull.2 (good_ind hI (p ≫ β₂)), good_ind hI' p⟩,
    pullU p _ (w.s (fun _ => ind B I (p ≫ β₂), ind B' I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (lamVal_eq w (r ≫ p) z J J').trans ?_
  refine ((isGen_iff w).1 hw Z (r ≫ p) z _ (ind B I (p ≫ β₂)) _ (ind B' I' p) (good_ind hJ ((r ≫ p) ≫ β₂))
    (mem_pull.1 hz.1) (good_ind hJ' _) hz.2).trans (congrArg (· * _) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)))
  · refine (gm_linComb M (lamφ B) lamε ((r ≫ p) ≫ β₂) z _ _ (good_ind hJ ((r ≫ p) ≫ β₂)) (mem_pull.1 hz.1)).trans ?_
    rfl
  · refine (gm_linComb M' (lamφ B') lamε (r ≫ p) z _ _ (good_ind hJ' _) hz.2).trans ?_
    rfl

section Scale

variable {Y : Scheme.{0}} {M : LB Y}

def scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun i => res le_top a * t.s i⟩

theorem gm_scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scale a t).s i) = gm r z ⊤ a * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ h a))

theorem scale_isGen (a : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scale a t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := congrArg (gm (𝟙 Y) y _) (ht i j)
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_scale a t _ y i hy.1, gm_scale a t _ y j hy.2, e, mul_left_comm]

end Scale

theorem mapsAtExp_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {K : Type}
    [Fintype K] {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) {p : Y ⟶ X'} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))} (ha : a.IsGen)
    {b : LB.Gen (LB.LinComb L (K := K) (fun i => p ≫ pr i) (fun i => n * ε i))} (hb : b.IsGen)
    (H : ∀ (y : Y) J J', Good L y J → Good L' y J' → val b (𝟙 Y) y J = wv w p y J J' ^ n * val a (𝟙 Y) y J') :
    MapsAtExp L L' pr ε w p n a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := good_exists hL y
  obtain ⟨J', hJ'⟩ := good_exists hL' y
  have e := H y J J' hJ hJ'
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])] at e
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => p ≫ pr i) (fun i => J (p ≫ pr i)) := Set.mem_iInter.2 fun i => hJ _
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun _ : PUnit => p) (fun _ => J' p) := Set.mem_iInter.2 fun i => hJ' _
  have eb := gen_trans hb (𝟙 Y) y (mapsAtExp_le_b L L' pr ε p jN jL hy) m₁
  have ea := gen_trans ha (𝟙 Y) y (mapsAtExp_le_a L L' pr ε p jN jL hy) m₂
  have ew := gm_isGen hw p y jN (fun i => J (p ≫ pr i)) jL (J' p) hy.1 (hJ.mem pr p) hy.2 (hJ' p)
  have el := gm_linComb L pr ε p y jN (fun i => J (p ≫ pr i)) hy.1 (hJ.mem pr p)
  refine (gm_res _ y _ hy _).trans (eb.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans
      ((congrArg (fun q : Y ⟶ X' => gv w q y jN jL) (Category.id_comp p)).trans
        (ew.trans (congrArg (fun x => x * _ * _) el)))))) ((gm_res _ y _ hy _).trans ea))).symm))
  rw [e]
  simp only [trF, wv, Category.id_comp, Fintype.prod_unique, mul_zpow, ← Finset.prod_zpow, inv_zpow, ← zpow_mul,
    mul_comm n]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp.Point
