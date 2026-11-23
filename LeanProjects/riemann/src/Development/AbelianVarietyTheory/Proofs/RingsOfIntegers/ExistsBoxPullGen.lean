import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamily

section General

variable {X X' Y Y' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

def om (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (y : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι)
    (ψ : Z ⟶ X') : (Z.presheaf.stalk y)ˣ := bw w ψ y (fun i => J (ψ ≫ pr i)) (J' ψ)

def IsBoxPull (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} (p : Fin j → (Y' ⟶ Y)) (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) : Prop :=
  ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
    (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
      ∏ i, rs (inf_le_left.trans (box_le_of_comp M pr φ' (φ i) (p i) i (hφ i) jN))
        (((p i).app _).hom ((s i).f (fun a => jN a i)))

theorem exists_boxPull (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} (p : Fin j → (Y' ⟶ Y)) (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) : ∃ s', IsBoxPull w p hφ s' s := by
  refine ⟨secOfIso (u := LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ s) (linCombIso_isGen w hw _ _)
    (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _), fun jN jM => ?_⟩
  set V := LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM with hVdef
  have hVab : V ≤ LB.wchart M' φ' jM ⊓ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN :=
    fun _ hy => ⟨hy.2, hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ s)
    (linCombIso_isGen w hw _ _) (linComb_isLB _ hM' _ _) (linComb_isLB _ (linComb_isLB _ hM _ _) _ _) jM jN)
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ s) jM jN hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (LB.LinComb M pr (fun _ => 1)) φ' ε) (LB.LinComb M' φ' ε)).U (jN, jM) :=
    fun _ hy => ⟨hy.1, hy.2⟩
  have hu : res hVd ((LB.linCombIso w φ' ε).s (jN, jM)) =
      @id (Γ(Y', V)ˣ) ((LB.linCombIso w φ' ε).s (jN, jM)) := res_refl' _
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((Y'.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

theorem boxPull_val {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {p : Fin j → (Y' ⟶ Y)} {hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a}
    {s' : LB.Sec (LB.LinComb M' φ' ε)} {s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)} (H : IsBoxPull w p hφ s' s)
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, om w y J J' (q ≫ φ' a) ^ ε a).val * sval s' q y J' = ∏ i, sval (s i) (q ≫ p i) y J := by
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  refine ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit q y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w φ' ε q y _ _ hm))) (gs_res q y _ hm _))).symm.trans (E.trans ((gs_prod q y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (s i) _ y J (fun a => J ((q ≫ φ' a) ≫ pr i))
    (fun a => by rw [Category.assoc, ← hφ, Category.assoc])]
  have hle : LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) ≤ _ :=
    inf_le_left.trans (box_le_of_comp M pr φ' (φ i) (p i) i (hφ i) (fun a i => J ((q ≫ φ' a) ≫ pr i)))
  exact (gs_res q y hle hm _).trans (gs_pull q (p i) y _ (hle hm) _)

theorem exists_good_at (hM : M.IsLB) (y : Z) : ∃ J, Good M y J := by
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hM (ψ y)
  exact ⟨J, hJ⟩

theorem exists_boxPull_gen (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} (p : Fin j → (Y' ⟶ Y)) (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (y : Z) (J J'),
      Good M y J → Good M' y J' →
      (∏ a, om w y J J' (q ≫ φ' a) ^ ε a) * val t' q y J' = ∏ i, val (t i) (q ≫ p i) y J := by
  obtain ⟨s, hs⟩ := exists_boxPull w hw hM hM' p hφ (fun i => Geo.Tor.genSec (t i) (ht i))
  have hv : ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (y : Z) (J J'), Good M y J → Good M' y J' →
      (∏ a, om w y J J' (q ≫ φ' a) ^ ε a).val * sval s q y J' = (∏ i, val (t i) (q ≫ p i) y J).val :=
    fun Z q y J J' hJ hJ' => (boxPull_val hs q y hJ hJ').trans
      ((Finset.prod_congr rfl fun i _ => sval_genSec (t i) (ht i) _ y hJ).trans (Units.coe_prod _ _).symm)
  have hu : ∀ c, IsUnit (s.f c) := fun c => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hM' s y c hy
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have h₁ : IsUnit (sval s (𝟙 Y') y J') :=
      isUnit_of_mul_isUnit_right ((hv _ (𝟙 Y') y J J' hJ hJ').symm ▸ Units.isUnit _)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart M' φ' c) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul h₁)
  refine ⟨⟨fun c => (hu c).unit⟩, fun a b => Units.ext (s.compat a b), fun Z q y J J' hJ hJ' => Units.ext ?_⟩
  refine Eq.trans ?_ (hv Z q y J J' hJ hJ')
  rw [Units.val_mul]
  exact congrArg₂ (· * ·) rfl (gs_unit q y _ (hJ'.mem φ' q) _).symm

theorem mapsAt_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n)))
    (H : GeneratorPullback.MapsAt M M' pr w p n a b) (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    val b r y J = om w y J J' (r ≫ p) ^ n * val a r y J' := by
  have hm : r y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J ((r ≫ p) ≫ pr i), J' (r ≫ p)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((r ≫ p) ≫ pr i), hJ' (r ≫ p)⟩
  have E := congrArg (gm r y _) (H (fun i => J ((r ≫ p) ≫ pr i)) (J' (r ≫ p)))
  rw [val_of b r y J (fun i => J ((r ≫ p) ≫ pr i)) (fun i => by rw [Category.assoc])]
  refine (gm_res r y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p y _ hm _))) (gm_res r y _ hm _))))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) (r : Z ⟶ Y) (y : Z) {J} (hJ : Good M y J) :
    val (GeneratorPullback.finProdGen M φ ε t) r y J = ∏ i, val (t i) r y J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ =>
    gm_res r y _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem val_powGen {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε)) (n : ℕ)
    (r : Z ⟶ Y) (y : Z) (J) : val (GeneratorPullback.powGen M φ ε t n) r y J = val t r y J ^ n := map_pow _ _ _

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem cPoint_pr (T : Over (Spec (CommRingCat.of R))) (x : D'.X) (i : Fin j) :
    cP D' T x ≫ pD.pw.pr i = cP D T (pD.xe x i) := by
  rw [cP, Category.assoc, pD.c_pr]; rfl

theorem prB_pr (i : Fin j) : DegPre.prB D' F ≫ pD.pw.pr i = (TF (R := R) F ◁ pD.pw.pr i) ≫ DegPre.prB D F :=
  (whiskerLeft_snd _ _).symm

theorem shift_pr (x : D'.X) (i : Fin j) : (DegPre.prB D' F * cP D' _ x) ≫ pD.pw.pr i =
    (TF (R := R) F ◁ pD.pw.pr i) ≫ (DegPre.prB D F * cP D _ (pD.xe x i)) := by
  haveI := pD.pw.hom i
  rw [MonObj.mul_comp, MonObj.comp_mul, prB_pr, cPoint_pr, comp_cP]

theorem famφ_pr (α' : D'.X) (i : Fin j) (a : Fin 4) :
    DegPre.famφ D' F α' a ≫ (pD.pw.pr i).left = prB pD F i ≫ DegPre.famφ D F (pD.xe α' i) a := by
  haveI := pD.pw.hom i
  fin_cases a
  · exact congrArg (fun q => q.left) (prB_pr pD F i)
  · exact congrArg (fun q => q.left) (shift_pr pD F α' i)
  · exact congrArg (fun q => q.left) ((cPoint_pr pD (DegPre.BF D' F) α' i).trans
      (comp_cP D (TF (R := R) F ◁ pD.pw.pr i) _).symm)
  · exact congrArg (fun q : DegPre.BF D' F ⟶ D.P.A => q.left) ((MonObj.one_comp (pD.pw.pr i)).trans
      (MonObj.comp_one (M := D.P.A) (TF (R := R) F ◁ pD.pw.pr i)).symm)

theorem trF_pr (mu : D'.X) (i : Fin j) : (DegPre.trF D' F mu).left ≫ prB pD F i =
    prB pD F i ≫ (DegPre.trF D F (pD.xe mu i)).left := by
  refine congrArg (fun q => q.left) (?_ : DegPre.trF D' F mu ≫ (TF (R := R) F ◁ pD.pw.pr i) =
    (TF (R := R) F ◁ pD.pw.pr i) ≫ DegPre.trF D F (pD.xe mu i))
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd_assoc]
    exact shift_pr pD F mu i

theorem zF_pr (i : Fin j) : (DegPre.zF D' F).left ≫ prB pD F i = (DegPre.zF D F).left := by
  haveI := pD.pw.hom i
  refine congrArg (fun q => q.left) (?_ : DegPre.zF D' F ≫ (TF (R := R) F ◁ pD.pw.pr i) = DegPre.zF D F)
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem xe_shift (k : ℕ) (α mu : D'.X) (i : Fin j) : pD.xe (α + k • mu) i = pD.xe α i + k • pD.xe mu i := by
  rw [map_add, map_nsmul]; rfl

theorem deltaφ_pr (k : ℕ) (α mu : D'.X) (i : Fin j) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D' F k α mu a ≫ (pD.pw.pr i).left =
      prB pD F i ≫ DegPre.deltaφ D F k (pD.xe α i) (pD.xe mu i) a := by
  rcases a with a | a
  · refine (famφ_pr pD F (α + k • mu) i a).trans ?_
    rw [xe_shift]; rfl
  · show ((DegPre.trF D' F mu).left ≫ DegPre.famφ D' F α a) ≫ _ =
      prB pD F i ≫ (DegPre.trF D F (pD.xe mu i)).left ≫ DegPre.famφ D F (pD.xe α i) a
    rw [Category.assoc, famφ_pr, ← Category.assoc, trF_pr, Category.assoc]

section Values

variable {Z : Scheme.{0}} {y : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} {J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι}
  (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
include hJ hJ'

theorem psi_val (x : D'.X) (r : Z ⟶ (TK R).left) :
    (om pD.w y J J' (r ≫ D'.xK x))⁻¹ * val (D'.psi x) r y J' = ∏ i, val (D.psi (pD.xe x i)) r y J := by
  obtain ⟨b, h₁, h₂⟩ := pD.w_psi x
  have e₁ := mapsAt_val pD.w (D'.xK x) (-1) (D'.psi x) b h₁ r y hJ hJ'
  rw [zpow_neg_one] at e₁
  exact e₁.symm.trans ((val_corr hJ h₂ r).trans (val_finProd _ _ _ r y hJ))

theorem rig_val (r : Z ⟶ (TK R).left) :
    om pD.w y J J' (r ≫ (toUnit (TK R)).left ≫ eSec D'.P.A) * val D'.rigK r y J' = ∏ _i : Fin j, val D.rigK r y J := by
  obtain ⟨b, h₁, h₂⟩ := pD.w_rig
  have e₁ := mapsAt_val pD.w (eSec D'.P.A) 1 D'.rig b h₁ (r ≫ (toUnit (TK R)).left) y hJ hJ'
  rw [zpow_one, Category.assoc] at e₁
  have e₂ := (val_corr hJ h₂ (r ≫ (toUnit (TK R)).left)).trans (val_finProd _ _ _ _ y hJ)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans (e₁.symm.trans (e₂.trans ?_))
  exact Finset.prod_congr rfl fun _ _ => (val_pull hJ _ _ _).symm

omit hJ' in
theorem famMult_val (k : ℕ) (mu α : D.X) (r : Z ⟶ (TF (R := R) F).left) :
    val (DegPre.famMult D F k mu α) r y J = val (D.psi mu) (r ≫ jFK (R := R) F) y J ^ k *
      (val (D.psi (mu + α)) (r ≫ jFK (R := R) F) y J * (val (D.psi mu) (r ≫ jFK (R := R) F) y J)⁻¹ *
        (val (D.psi α) (r ≫ jFK (R := R) F) y J)⁻¹ * (val D.rigK (r ≫ jFK (R := R) F) y J)⁻¹) *
      val D.rigK (r ≫ jFK (R := R) F) y J ^ k :=
  (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_powGen _ _ _ _ _ _ _) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))))) (val_powGen _ _ _ _ _ _ _)))

end Values

theorem prod_delta_zero (D : DegPre R) (k : ℕ) (α mu : D.X) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ a, h ((DegPre.zF D F).left ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a =
      (h (cP D _ mu).left)⁻¹ ^ k * ((h (cP D _ (mu + α)).left)⁻¹ * h (cP D _ mu).left * h (cP D _ α).left *
        (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹) * h (1 : TF (R := R) F ⟶ D.P.A).left ^ k := by
  have p₁ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
  have p₂ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [Category.assoc, DegPre.trF, lift_snd]
    refine (MonObj.comp_mul _ (DegPre.prB D F) (cP D _ mu)).trans ?_
    rw [z₂, comp_cP, _root_.one_mul]
  rw [z₂, _root_.mul_one] at p₁
  rw [z₃, ← cPoint_add, add_comm α mu] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₁ (prod_neg _ _ p₂)).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem famMult_box (k : ℕ) (α mu : D'.X) (y : (TF (R := R) F).left) {J J'}
    (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' ((DegPre.zF D' F).left ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) *
      val (Z := (TF (R := R) F).left) (DegPre.famMult D' F k mu α) (𝟙 _) y J' =
      ∏ i, val (Z := (TF (R := R) F).left) (DegPre.famMult D F k (pD.xe mu i) (pD.xe α i)) (𝟙 _) y J := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D'.xK χ = (cP D' (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D'.P.A =
      (1 : TF (R := R) F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := fun χ => (congrArg (fun q => (om pD.w y J J' q)⁻¹ *
    val (D'.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J') (a₁ χ)).symm.trans
    (psi_val pD hJ hJ' χ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F))
  have b₂ := rig_val pD hJ hJ' (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F)
  rw [a₂] at b₂
  have b₃ := (b₁ (mu + α)).trans (Finset.prod_congr rfl fun i _ => congrArg
    (fun χ => val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J)
    (show pD.xe (mu + α) i = pD.xe mu i + pD.xe α i by rw [map_add]; rfl))
  rw [prod_delta_zero F D' k α mu (om pD.w y J J'), famMult_val F hJ']
  simp only [famMult_val F hJ, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
  rw [← b₃, ← b₁ mu, ← b₁ α, ← b₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  module

end Deg

section Main

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem unit_shuffle {S : Type*} [CommRing S] (A B c : Sˣ) (x : S) :
    A.val * x * (B * A⁻¹ * c).val = B.val * (x * c.val) := by
  simp only [Units.val_mul]
  calc _ = (A.val * (A⁻¹).val) * (B.val * (x * c.val)) := by ring
    _ = _ := by rw [Units.mul_inv, _root_.one_mul]

theorem gen_box (hG : GlobalFnsSt) (k : ℕ) (α mu : D'.X)
    (u' : LB.Gen (LB.LinComb D'.P.L (DegPre.deltaφ D' F k α mu) (DegPre.deltaε k))) (hu' : u'.IsGen)
    (hc' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (DegPre.zF D' F).left) (DegPre.famMult D' F k mu α))
    (u : ∀ i, LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k (pD.xe α i) (pD.xe mu i)) (DegPre.deltaε k)))
    (hu : ∀ i, (u i).IsGen)
    (hc : ∀ i, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (u i) (DegPre.zF D F).left)
      (DegPre.famMult D F k (pD.xe mu i) (pD.xe α i)))
    {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D' F).left) (y : Z) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (q ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) * val u' q y J' =
      ∏ i, val (u i) (q ≫ prB pD F i) y J := by
  obtain ⟨t, ht, hv⟩ := exists_boxPull_gen pD.w pD.w_gen D.P.isLB D'.P.isLB (prB pD F) (deltaφ_pr pD F k α mu) u hu
  have z₁ : DegPre.zF D' F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have key := gen_unique D'.P.isLB (fst (TF (R := R) F) D'.P.A).left (DegPre.zF D' F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D' F hG) hu' ht (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
      have e₁ := hv _ (DegPre.zF D' F).left y J J' hJ hJ'
      have e₂ := famMult_box pD F k α mu y hJ hJ'
      have e₃ := val_corr hJ' hc' (𝟙 _)
      rw [val_pull hJ', Category.id_comp] at e₃
      have e₄ : ∀ i, val (u i) ((DegPre.zF D' F).left ≫ prB pD F i) y J =
          val (Z := (TF (R := R) F).left) (DegPre.famMult D F k (pD.xe mu i) (pD.xe α i)) (𝟙 _) y J := fun i => by
        have := val_corr hJ (hc i) (𝟙 _)
        rw [val_pull hJ, Category.id_comp] at this
        rw [zF_pr]; exact this
      exact e₃.trans (mul_left_cancel (e₂.trans ((Finset.prod_congr rfl fun i _ => (e₄ i).symm).trans e₁.symm))))
    Z q y J' hJ'
  rw [key]
  exact hv Z q y J J' hJ hJ'

theorem box_fe (hG : GlobalFnsSt) (k : ℕ) (Fs : Fin j → Fam D F k)
    (s' : ∀ α' : D'.X, LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F α') (DegPre.famε k)))
    (hs : ∀ α', IsBoxPull pD.w (prB pD F) (famφ_pr pD F α') (s' α') (fun i => (Fs i).s (pD.xe α' i))) :
    DegPre.FamFE D' F k s' := by
  intro mu α u' hu' hc'
  choose u hu hc using fun i => (gen_fe (D := D) (F := F) hG k (pD.xe mu i) (pD.xe α i)).1
  refine (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have e₁ := boxPull_val (hs (α + k • mu)) (𝟙 _) y hJ hJ'
  have e₂ := boxPull_val (hs α) (𝟙 _ ≫ (DegPre.trF D' F mu).left) y hJ hJ'
  have e₃ := gen_box pD F hG k α mu u' hu' hc' u hu hc (𝟙 _) y hJ hJ'
  have e₄ : ∀ i, sval ((Fs i).s (pD.xe (α + k • mu) i)) (𝟙 _ ≫ prB pD F i) y J =
      sval ((Fs i).s (pD.xe α i)) ((𝟙 _ ≫ (DegPre.trF D' F mu).left) ≫ prB pD F i) y J *
        (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
    have := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 ((Fs i).fe _ _ (u i) (hu i) (hc i)) _
      (𝟙 _ ≫ prB pD F i) y J hJ
    rw [xe_shift, this, Category.assoc, Category.assoc, trF_pr]
  have e₅ : (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, om pD.w y J J' ((𝟙 _ ≫ (DegPre.trF D' F mu).left) ≫ DegPre.famφ D' F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.trans ((Finset.prod_congr rfl fun i _ => e₄ i).trans ?_)
  rw [Finset.prod_mul_distrib, ← Units.coe_prod, ← e₃, e₅]
  refine (congrArg₂ (· * ·) e₂.symm rfl).trans ?_
  exact unit_shuffle _ _ _ _

end Main

theorem exists_isBoxFam : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (Fs : Fin j → Fam D F k),
    ∃ F' : Fam D' F k, IsBoxFam pD F k F' Fs := by
  intro hG R _ _ j D D' pD F _ _ k Fs
  choose s' hs using fun α' : D'.X => exists_boxPull pD.w pD.w_gen D.P.isLB D'.P.isLB (prB pD F) (famφ_pr pD F α')
    (fun i => (Fs i).s (pD.xe α' i))
  exact ⟨⟨s', box_fe pD F hG k Fs s' hs⟩, fun α' => ⟨famφ_pr pD F α', hs α'⟩⟩

end GlobalTheory.BoxFamily
