import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxQk

open GlobalTheory.BoxFamily

section General

variable {X X' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem exists_box_maps (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} (p : Fin j → (Y' ⟶ Y)) (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (p i) (φ i) ε φ' (hφ i) (t i))) := by
  obtain ⟨s, hs⟩ := exists_boxPull w hw hM hM' p hφ (fun i => Geo.Tor.genSec (t i) (ht i))
  have hv : ∀ (y : Y') (J J'), Good M y J → Good M' y J' →
      (∏ a, om w y J J' (𝟙 Y' ≫ φ' a) ^ ε a).val * sval s (𝟙 Y') y J' = (∏ i, val (t i) (𝟙 Y' ≫ p i) y J).val :=
    fun y J J' hJ hJ' => (boxPull_val hs _ y hJ hJ').trans
      ((Finset.prod_congr rfl fun i _ => sval_genSec (t i) (ht i) _ y hJ).trans (Units.coe_prod _ _).symm)
  have hu : ∀ c, IsUnit (s.f c) := fun c => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hM' s y c hy
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have h₁ : IsUnit (sval s (𝟙 Y') y J') :=
      isUnit_of_mul_isUnit_right ((hv y J J' hJ hJ').symm ▸ Units.isUnit _)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart M' φ' c) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul h₁)
  refine ⟨⟨fun c => (hu c).unit⟩, fun a b => Units.ext (s.compat a b), ?_⟩
  rintro ⟨jN, jM⟩
  refine Units.ext (Eq.trans ?_ (hs jN jM).symm)
  refine fn_ext (V := LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM) fun y hy => ?_
  refine Eq.trans ?_ (gs_prod (𝟙 Y') y _ hy _ _).symm
  refine (gs_unit (𝟙 Y') y _ hy _).trans ((congrArg Units.val ((gm_res (𝟙 Y') y inf_le_left hy _).trans
    (map_prod (gm (𝟙 Y') y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
    (fun i => res (GeneratorPullback.box_le M pr φ' jN i)
      ((GeneratorPullback.pullAlong M (pr i) (p i) (φ i) ε φ' (hφ i) (t i)).s (fun a _ => jN a i))) Finset.univ))).trans
      ((Units.coe_prod _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  have hle := box_le_of_comp M pr φ' (φ i) (p i) i (hφ i) jN
  refine (congrArg Units.val ((gm_res (𝟙 Y') y (GeneratorPullback.box_le M pr φ' _ i) hy.1 _).trans
    (gm_rp₁ (p i) y _ _ _ (GeneratorPullback.box_le M pr φ' _ i hy.1) _))).trans ?_
  refine Eq.trans ?_ ((gs_res (𝟙 Y') y (inf_le_left.trans hle) hy _).trans (gs_pull (𝟙 Y') (p i) y _ (hle hy.1) _)).symm
  rw [Category.id_comp]
  exact (gs_unit (p i) y _ (hle hy.1) _).symm

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pt_ext {T : Over (Spec (CommRingCat.of R))} {a b : T ⟶ D'.P.A}
    (h : ∀ i, a ≫ pD.pw.pr i = b ≫ pD.pw.pr i) : a = b :=
  pD.pw.lim.hom_ext fun ⟨i⟩ => h i

theorem gtφ_pr (b' : TF (R := R) F ⟶ D'.P.A) (b : Fin j → (TF (R := R) F ⟶ D.P.A))
    (hb : ∀ i, b' ≫ pD.pw.pr i = b i) (χ : D'.X) (i : Fin j) (a : Fin 4) :
    DegPre.gtφ D' F b' χ a ≫ (pD.pw.pr i).left = 𝟙 _ ≫ DegPre.gtφ D F (b i) (pD.xe χ i) a := by
  haveI := pD.pw.hom i
  rw [Category.id_comp]
  fin_cases a
  · refine congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
      (?_ : (cP D' _ χ * b') ≫ pD.pw.pr i = cP D _ (pD.xe χ i) * b i)
    rw [MonObj.mul_comp, cPoint_pr, hb]
  · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (cPoint_pr pD _ χ i)
  · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (hb i)
  · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.one_comp (pD.pw.pr i))

section Values

variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
  {J' : ((TF (R := R) F).left ⟶ D'.P.A.left) → D'.P.L.ι}

variable (y J J') in

def omP (x : TF (R := R) F ⟶ D'.P.A) : ((TF (R := R) F).left.presheaf.stalk y)ˣ := om pD.w y J J' x.left

variable (y J J') in

def omL (x b : TF (R := R) F ⟶ D'.P.A) : ((TF (R := R) F).left.presheaf.stalk y)ˣ :=
  (omP pD y J J' (x * b))⁻¹ * omP pD y J J' x * omP pD y J J' b * (omP pD y J J' 1)⁻¹

theorem omL_one (x : TF (R := R) F ⟶ D'.P.A) : omL pD y J J' x 1 = 1 := by
  rw [omL, _root_.mul_one]; simp

theorem omL_one' (x : TF (R := R) F ⟶ D'.P.A) : omL pD y J J' 1 x = 1 := by
  rw [omL, _root_.one_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

variable (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
include hJ hJ'

theorem maps_val {b' : TF (R := R) F ⟶ D'.P.A} {b : Fin j → (TF (R := R) F ⟶ D.P.A)} {χ : D'.X}
    (hψ : ∀ i a, DegPre.gtφ D' F b' χ a ≫ (pD.pw.pr i).left = 𝟙 _ ≫ DegPre.gtφ D F (b i) (pD.xe χ i) a)
    (t' : LB.Gen (LB.LinComb D'.P.L (DegPre.gtφ D' F b' χ) DegPre.gtε))
    (t : ∀ i, LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F (b i) (pD.xe χ i)) DegPre.gtε))
    (H : LB.Gen.Maps (LB.linCombIso pD.w _ DegPre.gtε) t'
        (GeneratorPullback.boxGen D.P.L (fun i => (pD.pw.pr i).left) _ DegPre.gtε (fun i =>
          GeneratorPullback.pullAlong D.P.L (pD.pw.pr i).left (𝟙 _) _ DegPre.gtε _ (hψ i) (t i)))) :
    omL pD y J J' (cP D' _ χ) b' * val t' (𝟙 _) y J' = ∏ i, val (t i) (𝟙 _) y J :=
  (congrArg₂ (· * ·) (prod_gt b' χ (om pD.w y J J')).symm rfl).trans (box_gen_val pD.w hψ t' t H y hJ hJ')

theorem th_box (hG : GlobalFnsSt) (x x' b : TF (R := R) F ⟶ D'.P.A) :
    th D' y J' x x' b * (omL pD y J J' x b * omL pD y J J' x' b) =
      omL pD y J J' (x * x') b * ∏ i, th D y J (x ≫ pD.pw.pr i) (x' ≫ pD.pw.pr i) (b ≫ pD.pw.pr i) := by
  have e : th D' y J' x x' b * (omP pD y J J' (x * x' * b) * (omP pD y J J' (x * x'))⁻¹ * (omP pD y J J' (x * b))⁻¹ *
      (omP pD y J J' (x' * b))⁻¹ * omP pD y J J' x * omP pD y J J' x' * omP pD y J J' b * (omP pD y J J' 1)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD _ y J J' hJ hJ' x x' b
  rw [← e]
  unfold omL
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem th_box' (hG : GlobalFnsSt) (x b b' : TF (R := R) F ⟶ D'.P.A) :
    th D' y J' x b b' * (omL pD y J J' x b * omL pD y J J' x b') =
      omL pD y J J' x (b * b') * ∏ i, th D y J (x ≫ pD.pw.pr i) (b ≫ pD.pw.pr i) (b' ≫ pD.pw.pr i) := by
  have e : th D' y J' x b b' * (omP pD y J J' (x * b * b') * (omP pD y J J' (x * b))⁻¹ * (omP pD y J J' (x * b'))⁻¹ *
      (omP pD y J J' (b * b'))⁻¹ * omP pD y J J' x * omP pD y J J' b * omP pD y J J' b' * (omP pD y J J' 1)⁻¹) = _ :=
    GlobalTheory.CubBox.cubV_box hG R j D D' pD _ y J J' hJ hJ' x b b'
  rw [← e]
  unfold omL
  rw [← _root_.mul_assoc x]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_box (a b : D'.X) :
    omL pD y J J' (cP D' _ b) (cP D' _ a) * val (D'.tau a b) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J' =
      ∏ i, val (D.tau (pD.xe a i) (pD.xe b i)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D'.xK χ = (cP D' (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D'.P.A =
      (1 : TF (R := R) F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ : ∀ χ, (omP pD y J J' (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J' = _ :=
    fun χ => (congrArg (fun q => (om pD.w y J J' q)⁻¹ *
    val (D'.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J') (a₁ χ)).symm.trans
    (psi_val pD hJ hJ' χ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F))
  have b₂ : omP pD y J J' 1 * val D'.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J' = _ :=
    (congrArg (fun q => om pD.w y J J' q *
    val D'.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J') a₂).symm.trans
    (rig_val pD hJ hJ' (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F))
  have b₃ := (b₁ (a + b)).trans (Finset.prod_congr rfl fun i _ => congrArg
    (fun χ => val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J)
    (show pD.xe (a + b) i = pD.xe a i + pD.xe b i by rw [map_add]; rfl))
  have e : ∀ (E : DegPre R) (I), Good E.P.L y I → ∀ a b : E.X,
      val (E.tau a b) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y I =
      val (E.psi (a + b)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y I *
        (val (E.psi a) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y I)⁻¹ *
        (val (E.psi b) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y I)⁻¹ *
        (val E.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y I)⁻¹ := fun E I hI a b =>
    (val_mul hI _ _ _).trans (congrArg₂ (· * ·) ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  refine (congrArg₂ (· * ·) rfl (e D' J' hJ' a b)).trans (Eq.trans ?_
    (Finset.prod_congr rfl fun i _ => e D J hJ (pD.xe a i) (pD.xe b i)).symm)
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [← b₃, ← b₁ a, ← b₁ b, ← b₂, omL, ← cPoint_add, add_comm b a]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem box_val {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (χ : D'.X) :
    omL pD y J J' (cP D' _ χ) g'.b * val (g'.s χ) (𝟙 _) y J' = ∏ i, val ((g i).s (pD.xe χ i)) (𝟙 _) y J := by
  obtain ⟨hψ, H⟩ := h.2 χ
  exact maps_val pD hJ hJ' hψ _ _ H

end Values

theorem alg_mul {U : Type} [CommGroup U] {a b c s t u θ Θ S T V : U} (h₁ : a * s = S) (h₂ : b * t = T) (h₃ : c * u = V)
    (h₄ : θ * (a * b) = c * Θ) (h₅ : V * Θ = S * T) : u * θ = s * t := by
  subst h₁ h₂ h₃
  refine mul_left_cancel (a := a * b) ?_
  calc a * b * (u * θ) = u * (θ * (a * b)) := by ac_rfl
    _ = c * u * Θ := by rw [h₄]; ac_rfl
    _ = _ := by rw [h₅]; ac_rfl

theorem exists_boxGt (hG : GlobalFnsSt) (g : Fin j → GtPtF D F) : ∃ g' : GtPtF D' F, IsBoxGtF pD F g' g := by
  let b' : TF (R := R) F ⟶ D'.P.A := pD.pw.lim.lift (Fan.mk _ fun i => (g i).b)
  have hb : ∀ i, b' ≫ pD.pw.pr i = (g i).b := fun i => pD.pw.lim.fac (Fan.mk _ fun i => (g i).b) ⟨i⟩
  choose s hs hm using fun χ : D'.X => exists_box_maps pD.w pD.w_gen D.P.isLB D'.P.isLB (fun _ => 𝟙 _)
    (gtφ_pr pD b' (fun i => (g i).b) hb χ) (fun i => (g i).s (pD.xe χ i)) (fun i => (g i).isGen _)
  refine ⟨⟨b', s, hs, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun χ χ' => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩,
    hb, fun χ => ⟨_, hm χ⟩⟩
  · obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have e := maps_val pD hJ hJ' _ _ _ (hm 0)
    rw [cPoint_zero, omL_one', _root_.one_mul] at e
    refine e.trans ((Finset.prod_eq_one fun i _ => ?_).trans (val_one _).symm)
    have z : pD.xe 0 i = 0 := by rw [map_zero]; rfl
    exact (congrArg (fun χ => val ((g i).s χ) (𝟙 _) y J) z).trans
      ((val_corr hJ (g i).s_zero _).trans (val_one _))
  · obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    refine (val_mul hJ' _ _ _).trans ((congrArg₂ (· * ·) rfl (val_cubAt hJ' _ _ _)).trans
      (Eq.trans ?_ (val_mul hJ' _ _ _).symm))
    have e := th_box pD hJ hJ' hG (cP D' _ χ) (cP D' _ χ') b'
    rw [← cPoint_add] at e
    refine alg_mul (maps_val pD hJ hJ' _ _ _ (hm χ)) (maps_val pD hJ hJ' _ _ _ (hm χ'))
      (maps_val pD hJ hJ' _ _ _ (hm (χ + χ'))) e ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have z : pD.xe (χ + χ') i = pD.xe χ i + pD.xe χ' i := by rw [map_add]; rfl
    have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ (g i) (pD.xe χ i) (pD.xe χ' i)
    rw [Category.id_comp, Over.id_left] at e₂
    rw [cPoint_pr, cPoint_pr, hb]
    exact (congrArg₂ (· * ·) (congrArg (fun χ => val ((g i).s χ) (𝟙 _) y J) z) rfl).trans e₂

theorem box_isZero {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (hz : ∀ i, (g i).IsZero) :
    g'.IsZero := by
  have hb : g'.b = 1 := pt_ext pD fun i => by
    haveI := pD.pw.hom i
    rw [h.1, ((isZero_iff _).1 (hz i)).1, MonObj.one_comp]
  refine (isZero_iff _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have e := box_val pD hJ hJ' h χ
  have o : omL pD y J J' (cP D' _ χ) g'.b = 1 := by rw [hb, omL_one]
  rw [o, _root_.one_mul] at e
  exact e.trans (Finset.prod_eq_one fun i _ => ((isZero_iff _).1 (hz i)).2 _ y J hJ)

theorem box_isAdd (hG : GlobalFnsSt) {g₁' g₂' g₃' : GtPtF D' F} {g₁ g₂ g₃ : Fin j → GtPtF D F}
    (h₁ : IsBoxGtF pD F g₁' g₁) (h₂ : IsBoxGtF pD F g₂' g₂) (h₃ : IsBoxGtF pD F g₃' g₃)
    (ha : ∀ i, (g₁ i).IsAdd (g₂ i) (g₃ i)) : g₁'.IsAdd g₂' g₃' := by
  have hb : g₃'.b = g₁'.b * g₂'.b := pt_ext pD fun i => by
    haveI := pD.pw.hom i
    rw [h₃.1, ((isAdd_iff _ _ _).1 (ha i)).1, MonObj.mul_comp, h₁.1, h₂.1]
  refine (isAdd_iff _ _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have e := th_box' pD hJ hJ' hG (cP D' _ χ) g₁'.b g₂'.b
  rw [← hb] at e
  refine alg_mul (box_val pD hJ hJ' h₁ χ) (box_val pD hJ hJ' h₂ χ) (box_val pD hJ hJ' h₃ χ) e ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [cPoint_pr, h₁.1, h₂.1]
  exact ((isAdd_iff _ _ _).1 (ha i)).2 _ y J hJ

theorem box_isIota {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (x : D'.X)
    (hι : ∀ i, GtPtF.IsIota (pD.xe x i) (g i)) : GtPtF.IsIota x g' := by
  have hb : g'.b = cP D' _ x := pt_ext pD fun i => by
    rw [h.1, ((isIota_iff _ _).1 (hι i)).1, cPoint_pr]
  refine (isIota_iff _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have e := tau_box pD hJ hJ' x χ
  rw [← hb] at e
  exact mul_left_cancel ((box_val pD hJ hJ' h χ).trans
    ((Finset.prod_congr rfl fun i _ => ((isIota_iff _ _).1 (hι i)).2 _ y J hJ).trans e.symm))

end Deg

theorem exists_isBoxQk : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (p : Fin j → QkPt D F k),
    ∃ p' : QkPt D' F k, IsBoxQk pD F k p' p := by
  intro hG R _ _ j D D' pD F _ _ k p
  choose box hbox using fun g : Fin j → GtPtF D F => exists_boxGt pD hG g
  choose h hn hι using fun i => (p i).eq
  choose gs g₀ gst gl using hn
  have hy : pD.xe (pD.xe.symm fun i => (p i).y) = fun i => (p i).y := pD.xe.apply_symm_apply _
  refine ⟨⟨pD.xe.symm fun i => (p i).y, box fun i => (p i).g, box h,
    ⟨fun n => box fun i => gs i n, box_isZero pD (hbox _) g₀,
      fun n => box_isAdd pD hG (hbox _) (hbox _) (hbox _) fun i => gst i n, congrArg box (funext gl)⟩,
    box_isIota pD (hbox _) _ fun i => ?_⟩, hy, hbox _⟩
  rw [hy]
  exact hι i

end GlobalTheory.BoxQk
