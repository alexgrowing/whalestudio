import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory
namespace LevelExpansion

section Torsor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}

def WtAt (i : splitTorus S X ⟶ G) (V : G.left.Opens) (a : Γ(G.left, V)) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G) (z : Z.left), y.left z ∈ V →
    gs ((t ≫ i) * y).left z V a = gs t.left z ⊤ (charUnit S X χ).val * gs y.left z V a

theorem act_q [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ i) * g).left ≫ q.left = g.left ≫ q.left := by
  have : (t ≫ i) ≫ q = 1 := by
    rw [Category.assoc, hi.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, this, _root_.one_mul]

theorem act_mem [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) {V : B.left.Opens} (h : g.left z ∈ q.left ⁻¹ᵁ V) :
    ((t ≫ i) * g).left z ∈ q.left ⁻¹ᵁ V :=
  (congrArg (fun f => f z ∈ V) (act_q hi t g)).mpr h

theorem wtAt_of_isWt [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens}
    {a : Γ(G.left, q.left ⁻¹ᵁ V)} {χ : X} (h : IsWt i (q.left ⁻¹ᵁ V) a χ) : WtAt i (q.left ⁻¹ᵁ V) a χ := by
  intro Z t y z hz
  let W : Z.left.Opens := y.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)
  let Z' : Over S := Over.mk (W.ι ≫ Z.hom)
  let κ : Z' ⟶ Z := Over.homMk W.ι rfl
  let z' : Z'.left := (⟨z, hz⟩ : W.toScheme)
  have h₂ : ⊤ ≤ (κ ≫ y).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun w _ => (show W.toScheme from w).2
  have h₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ y)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun w _ => act_mem hi _ _ w (h₂ trivial)
  have E := congrArg (gs (𝟙 Z'.left) z' ⊤) (h Z' (κ ≫ t) (κ ≫ y) h₁ h₂)
  rw [gs_mul _ z' ⊤ trivial, gs_appLE _ _ ⊤ _ _ z' trivial, gs_appLE _ _ ⊤ _ _ z' trivial] at E
  have e₁ : gs (𝟙 Z'.left) z' ⊤ ((κ ≫ t).left.appTop.hom (charUnit S X χ).val) =
      gs (𝟙 Z'.left ≫ (κ ≫ t).left) z' ⊤ (charUnit S X χ).val := gs_pull (𝟙 Z'.left) (κ ≫ t).left z' ⊤ trivial _
  have e₂ : ((κ ≫ t) ≫ i) * (κ ≫ y) = κ ≫ ((t ≫ i) * y) := by rw [MonObj.comp_mul, Category.assoc]
  rw [e₁, e₂, Category.id_comp, Category.id_comp, Category.id_comp, Over.comp_left, Over.comp_left,
    Over.comp_left] at E
  have : Flat κ.left := inferInstanceAs (Flat W.ι)
  apply LiftTest.stalkMap_injective_of_flat κ.left z'
  exact ((LiftTest.gs_comp κ.left _ z' _ (act_mem hi t y z hz) a).symm.trans E).trans
    ((congrArg₂ (· * ·) (LiftTest.gs_comp κ.left _ z' ⊤ trivial _) (LiftTest.gs_comp κ.left _ z' _ hz a)).trans
      (map_mul _ _ _).symm)

theorem eq_zero_of_wtAt [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens} (s : Finset X)
    (a : X → Γ(G.left, q.left ⁻¹ᵁ V)) (ha : ∀ χ, WtAt i (q.left ⁻¹ᵁ V) (a χ) χ) (hs : ∑ χ ∈ s, a χ = 0) :
    ∀ χ ∈ s, a χ = 0 := by
  refine WeightVal.eq_zero_of_stalk_sum X G s a fun w hw => ?_
  have hm := act_mem hi (fst (splitTorus S X) G) (snd _ _) w hw
  have E := congrArg (gs ((fst (splitTorus S X) G ≫ i) * snd _ _).left w _) hs
  rw [DVR.gs_fsum _ w _ hm, LinDescent.gs_zero _ w _ hm] at E
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) E
  rw [ha χ _ _ _ w hw]
  refine congrArg (· * _) ((gs_pull (𝟙 _) (fst (splitTorus S X) G).left w ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

variable {Y : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (B.left ⟶ Y)} {ε : K → ℤ}

theorem trF_act [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (j j' : K → L.ι) :
    trF (fun k => q.left ≫ φ k) ε ((t ≫ i) * g).left z j j' = trF (fun k => q.left ≫ φ k) ε g.left z j j' := by
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Category.assoc, act_q hi, Category.assoc]

theorem act_φ [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (k : K) : ((t ≫ i) * g).left ≫ q.left ≫ φ k = g.left ≫ q.left ≫ φ k := by
  rw [← Category.assoc, act_q hi, Category.assoc]

omit [GrpObj G] [GrpObj B] in
theorem le_wchart (j : K → L.ι) : q.left ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => q.left ≫ φ k) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

omit [GrpObj G] [GrpObj B] in
theorem wchart_le (j : K → L.ι) : LB.wchart L (fun k => q.left ≫ φ k) j ≤ q.left ⁻¹ᵁ LB.wchart L φ j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_descent [IsMonHom q] [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hi : IsPullback i (toUnit _) q η[B]) (hL : L.IsLB) (s : LB.Sec (LB.LinComb L (fun k => q.left ≫ φ k) ε))
    (hs : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G) (z : Z.left) (J), Good L z J →
      sval s ((t ≫ i) * y).left z J = sval s y.left z J) :
    ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good L z J → sval d (r ≫ q.left) z J = sval s r z J := by
  have D := invariant_functions_descend S G B _ q i ‹_› ‹_› ‹_› ‹_› ‹_› hi
  have ex : ∀ j, ∃ a : Γ(B.left, LB.wchart L φ j),
      (q.left.app _).hom a = LinDescent.rs (le_wchart j) (s.f j) := fun j =>
    (D _).2.2 _ fun Z t y h₁ h₂ => fn_ext fun z _ => by
      rw [gs_appLE _ _ ⊤ _ _ z trivial, gs_appLE _ _ ⊤ _ _ z trivial, Category.id_comp, Category.id_comp]
      have m₁ : ((t ≫ i) * y).left z ∈ q.left ⁻¹ᵁ LB.wchart L φ j := h₁ (Set.mem_univ z)
      have m₂ : y.left z ∈ q.left ⁻¹ᵁ LB.wchart L φ j := h₂ (Set.mem_univ z)
      refine (gs_res ((t ≫ i) * y).left z (le_wchart j) m₁ (s.f j)).trans
        (Eq.trans ?_ (gs_res y.left z (le_wchart j) m₂ (s.f j)).symm)
      choose J hJ using fun χ : Z.left ⟶ Y => exists_chart hL (χ z)
      have hJ' : Good L z J := hJ
      refine (sec_trans s ((t ≫ i) * y).left z (le_wchart j m₁) (hJ'.mem _ _)).trans
        (Eq.trans ?_ (sec_trans s y.left z (le_wchart j m₂) (hJ'.mem _ _)).symm)
      refine congrArg₂ (· * ·) ?_ (hs Z t y z J hJ')
      rw [trF_act hi]
      simp only [act_φ hi]
  choose a ha using ex
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) j, r z ∈ q.left ⁻¹ᵁ LB.wchart L φ j →
      gs (r ≫ q.left) z _ (a j) = gs r z (LB.wchart L (fun k => q.left ≫ φ k) j) (s.f j) := fun Z r z j hz => by
    rw [← gs_pull r q.left z _ hz, ha]
    exact gs_res r z _ hz _
  refine ⟨⟨a, fun j j' => (D _).1 (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ => ?_⟩
  · have hm : (𝟙 G.left ≫ q.left) y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gs_pull (𝟙 _) q.left y _ hm _).trans (Eq.trans ?_ (gs_pull (𝟙 _) q.left y _ hm _).symm)
    refine (gs_res _ y _ hm _).trans (Eq.trans ?_ ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_unit _ y _ hm _).trans (congrArg Units.val (gm_linComb L φ ε _ y j j' hm.1 hm.2)))
      (gs_res _ y _ hm _))).symm)
    refine (hv _ (𝟙 _) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hv _ (𝟙 _) y j' hy.2)).symm)
    refine (sec_trans s (𝟙 _) y (le_wchart j hy.1) (le_wchart j' hy.2)).trans ?_
    simp only [trF, Category.assoc]
  · rw [sval_of _ _ z J (fun k => J (r ≫ q.left ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv Z r z _ (wchart_le _ (hJ.mem (fun k => q.left ≫ φ k) r))

theorem glue_sec {W : Scheme.{0}} (hL : L.IsLB) (ψ : K → (W ⟶ Y)) (ε : K → ℤ) {κ : Type} (O : κ → W.Opens)
    (c : κ → K → L.ι) (hc : ∀ k, O k ≤ LB.wchart L ψ (c k)) (cov : ∀ x, ∃ k, x ∈ O k) (b : ∀ k, Γ(W, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l →
      gs (𝟙 W) x (O k) (b k) = (trF ψ ε (𝟙 W) x (c k) (c l)).val * gs (𝟙 W) x (O l) (b l)) :
    ∃ τ : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) j k, r z ∈ LB.wchart L ψ j → r z ∈ O k →
      gs r z (LB.wchart L ψ j) (τ.f j) = (trF ψ ε r z j (c k)).val * gs r z (O k) (b k) := by
  obtain ⟨m, hm, hm'⟩ := LinDescent.glue_sec (DVR.linComb_isLB _ hL ψ ε) ⊤ O c (fun _ => le_top) hc
    (fun x _ => cov x) b (fun k l x hk hl => (h k l x hk hl).trans
      (congrArg (fun u : (W.presheaf.stalk x)ˣ => u.val * _) (gm_linComb L ψ ε (𝟙 W) x _ _ (hc k hk) (hc l hl)).symm))
  have le : ∀ j, (LB.LinComb L ψ ε).U j ≤ ⊤ ⊓ (LB.LinComb L ψ ε).U j := fun j => le_inf le_top le_rfl
  refine ⟨⟨fun j => LinDescent.rs (le j) (m j), fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j k hj hk => ?_⟩
  · refine ((gs_res (𝟙 W) y _ hy _).trans (gs_res (𝟙 W) y (le j) hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 W) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 W) y _ hy _)
        ((gs_res (𝟙 W) y _ hy _).trans (gs_res (𝟙 W) y (le j') hy.2 _)))).symm)
    exact hm W (𝟙 W) y j j' trivial hy.1 hy.2
  · exact (gs_res r z (le j) hj _).trans ((hm' Z r z j k hj hk).trans
      (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) (gm_linComb L ψ ε r z _ _ hj (hc k hk))))

theorem exists_weights [IsMonHom q] [IsMonHom i] [IsAffineHom q.left] [CompactSpace B.left]
    (hi : IsPullback i (toUnit _) q η[B]) (hL : L.IsLB) (σ : LB.Sec (LB.LinComb L (fun k => q.left ≫ φ k) ε)) :
    ∃ (s : Finset X) (τ : X → LB.Sec (LB.LinComb L (fun k => q.left ≫ φ k) ε)), (∀ α ∉ s, ∀ j, (τ α).f j = 0) ∧
      (∀ α (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G) (z : Z.left) (J), Good L z J →
        sval (τ α) ((t ≫ i) * y).left z J = gs t.left z ⊤ (charUnit S X α).val * sval (τ α) y.left z J) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J), Good L z J → sval σ r z J = ∑ α ∈ s, sval (τ α) r z J := by
  classical
  have ex : ∀ b : B.left, ∃ (j : K → L.ι) (V : B.left.Opens), IsAffineOpen V ∧ b ∈ V ∧ V ≤ LB.wchart L φ j := fun b => by
    choose j hj using fun k => exists_chart hL (φ k b)
    obtain ⟨V, hV, h₁, h₂⟩ := exists_isAffineOpen_mem_and_subset (x := b) (U := LB.wchart L φ j) (Set.mem_iInter.2 hj)
    exact ⟨j, V, hV, h₁, h₂⟩
  choose c V hV hb hle using ex
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun b => (V b : Set B.left)) (fun b => (V b).isOpen)
    (fun b _ => Set.mem_iUnion.2 ⟨b, hb b⟩)
  have hO : ∀ b, q.left ⁻¹ᵁ V b ≤ LB.wchart L (fun k => q.left ≫ φ k) (c b) := fun b y hy => le_wchart _ (hle b hy)
  have cov : ∀ x : G.left, ∃ b : F, x ∈ q.left ⁻¹ᵁ V b := fun x => by
    obtain ⟨b, hb, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ (q.left x)))
    exact ⟨⟨b, hb⟩, hx⟩
  choose a ha ha' using fun b => (functions_graded_by_weights S G X i ‹_› (q.left ⁻¹ᵁ V b) ((hV b).preimage q.left)
    (fun w hw => act_mem hi _ _ w hw)).1 (LinDescent.rs (hO b) (σ.f (c b)))
  replace ha := fun b χ => wtAt_of_isWt hi (ha b χ)
  let s : Finset X := F.biUnion fun b => (a b).support
  have hs : ∀ b : F, (a b).support ⊆ s := fun b => Finset.subset_biUnion_of_mem (fun b => (a b).support) b.2
  have h0 : ∀ (b : F) χ, χ ∉ s → a b χ = 0 := fun b χ h => Finsupp.notMem_support_iff.1 fun h' => h (hs b h')
  have hsum : ∀ (b : F) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), r z ∈ q.left ⁻¹ᵁ V b →
      ∑ χ ∈ s, gs r z _ (a b χ) = gs r z (LB.wchart L (fun k => q.left ≫ φ k) (c b)) (σ.f (c b)) := fun b Z r z hz => by
    rw [← DVR.gs_fsum r z _ hz, ← Finsupp.sum_of_support_subset (a b) (hs b) (fun _ x => x) (fun _ _ => rfl), ← ha']
    exact gs_res r z _ hz _
  have compat : ∀ α (b b' : F) (x : G.left), x ∈ q.left ⁻¹ᵁ V b → x ∈ q.left ⁻¹ᵁ V b' →
      gs (𝟙 _) x _ (a b α) = (trF (fun k => q.left ≫ φ k) ε (𝟙 _) x (c b) (c b')).val * gs (𝟙 _) x _ (a b' α) := by
    intro α b b' x hx hx'
    by_cases hα : α ∈ s
    swap
    · rw [h0 b α hα, h0 b' α hα, LinDescent.gs_zero (𝟙 _) x _ hx, LinDescent.gs_zero (𝟙 _) x _ hx', mul_zero]
    have l₁ : q.left ⁻¹ᵁ (V b ⊓ V b') ≤ q.left ⁻¹ᵁ V b := fun _ h => h.1
    have l₂ : q.left ⁻¹ᵁ (V b ⊓ V b') ≤ q.left ⁻¹ᵁ V b' := fun _ h => h.2
    have l₃ := le_inf (l₁.trans (hO b)) (l₂.trans (hO b'))
    obtain ⟨h, hh⟩ : ∃ h : X → Γ(G.left, q.left ⁻¹ᵁ (V b ⊓ V b')), ∀ χ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z),
        r z ∈ q.left ⁻¹ᵁ (V b ⊓ V b') → gs r z _ (h χ) =
          gs r z _ (a b χ) - (trF (fun k => q.left ≫ φ k) ε r z (c b) (c b')).val * gs r z _ (a b' χ) :=
      ⟨fun χ => LinDescent.rs l₁ (a b χ) -
        LinDescent.rs l₃ ((LB.LinComb L (fun k => q.left ≫ φ k) ε).g (c b) (c b')).val * LinDescent.rs l₂ (a b' χ),
        fun χ Z r z hz => (LinDescent.gs_sub r z _ hz _ _).trans (congrArg₂ (· - ·) (gs_res r z _ hz _)
          ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ (l₃ hz) _).trans
            (congrArg Units.val (gm_linComb L _ ε r z _ _ (l₃ hz).1 (l₃ hz).2)))) (gs_res r z _ hz _))))⟩
    have H := eq_zero_of_wtAt hi s h (fun χ Z t y z hz => by
      rw [hh χ _ _ z (act_mem hi t y z hz), hh χ _ _ z hz, ha b χ Z t y z hz.1, ha b' χ Z t y z hz.2, trF_act hi]
      ring) (fn_ext fun y hy => by
      rw [DVR.gs_fsum (𝟙 _) y _ hy, LinDescent.gs_zero (𝟙 _) y _ hy,
        Finset.sum_congr rfl fun χ _ => hh χ _ (𝟙 _) y hy, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsum b _ (𝟙 _) y hy.1, hsum b' _ (𝟙 _) y hy.2, sec_trans σ (𝟙 _) y (l₃ hy).1 (l₃ hy).2, sub_self]) α hα
    have E := hh α _ (𝟙 _) x ⟨hx, hx'⟩
    rw [H, LinDescent.gs_zero (𝟙 _) x _ (show x ∈ q.left ⁻¹ᵁ (V b ⊓ V b') from ⟨hx, hx'⟩)] at E
    exact sub_eq_zero.1 E.symm
  choose τ hτ using fun α => glue_sec hL (fun k => q.left ≫ φ k) ε (fun b : F => q.left ⁻¹ᵁ V b) (fun b => c b)
    (fun b => hO b) cov (fun b => a b α) (compat α)
  refine ⟨s, τ, fun α hα j => fn_ext fun y hy => ?_, fun α Z t y z J hJ => ?_, fun Z r z J hJ => ?_⟩
  · obtain ⟨b, hb⟩ := cov y
    refine (hτ α _ (𝟙 _) y j b hy hb).trans ?_
    rw [h0 b α hα, LinDescent.gs_zero (𝟙 _) y _ hb, mul_zero]
    exact (LinDescent.gs_zero (𝟙 _) y _ hy).symm
  · obtain ⟨b, hb⟩ := cov (y.left z)
    refine (hτ α _ _ z _ b (hJ.mem _ _) (act_mem hi t y z hb)).trans
      (Eq.trans ?_ (congrArg _ (hτ α _ _ z _ b (hJ.mem _ _) hb)).symm)
    rw [ha b α Z t y z hb, trF_act hi, mul_left_comm]
    simp only [act_φ hi]
  · obtain ⟨b, hb⟩ := cov (r z)
    refine (sec_trans σ r z (hJ.mem _ r) (hO b hb)).trans ?_
    rw [← hsum b Z r z hb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => (hτ α Z r z _ b (hJ.mem _ r) hb).symm

end Torsor

section Values
variable {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem good_comp (x : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (x z) (fun ψ => J (x ≫ ψ)) := fun ψ => hJ (x ≫ ψ)

theorem sval_comp (s : LB.Sec (LB.LinComb L φ ε)) (x : Z ⟶ W) (r : W ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    sval s (x ≫ r) z J = (x.stalkMap z).hom (sval s r (x z) (fun ψ => J (x ≫ ψ))) := by
  rw [sval_of s (x ≫ r) z J (fun k => J (x ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact LiftTest.gs_comp x r z _ ((good_comp x hJ).mem φ r) _

theorem val_comp (t : LB.Gen (LB.LinComb L φ ε)) (x : Z ⟶ W) (r : W ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    (val t (x ≫ r) z J).val = (x.stalkMap z).hom (val t r (x z) (fun ψ => J (x ≫ ψ))).val := by
  rw [val_of t (x ≫ r) z J (fun k => J (x ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := (good_comp x hJ).mem φ r
  exact (gs_unit (x ≫ r) z _ hm _).symm.trans ((LiftTest.gs_comp x r z _ hm _).trans
    (congrArg _ (gs_unit r (x z) _ hm _)))

def secSub {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

theorem sval_secSub (s s' : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (secSub s s') r z J = sval s r z J - sval s' r z J :=
  LinDescent.gs_sub r z _ (hJ.mem φ r) _ _

theorem sval_eq_zero (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans (LinDescent.gs_zero r z _ (hJ.mem φ r))

end Values

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem formEq (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ g.pG.left) (D.Oφ g.pG α))
      (Sum.elim (fun _ => (k : ℤ)) (fun a => - Oinvε a))
      (fun a => g.pG.left ≫ D.famφB α a) (DegPre.famε k) := by
  intro U _ h
  have e : ∀ a, g.pG.left ≫ D.Oφ (𝟙 _) α a = D.Oφ g.pG α a := fun a => by
    rw [WeightPf.Oφ_comp, Category.comp_id]
  have e₀ : g.pG.left ≫ D.famφB α 0 = g.pG.left := Category.comp_id _
  have e₁ : g.pG.left ≫ D.famφB α 1 = D.Oφ g.pG α 0 := e 0
  have e₂ : g.pG.left ≫ D.famφB α 2 = D.Oφ g.pG α 1 := e 1
  have e₃ : g.pG.left ≫ D.famφB α 3 = D.Oφ g.pG α 3 := e 3
  have e₄ : D.Oφ g.pG α 2 = g.pG.left := rfl
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr, Category.id_comp, e₀, e₁, e₂, e₃, e₄]
  change h _ ^ (k : ℤ) * (h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) * h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ)) =
    h _ ^ ((k : ℤ) - 1) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ)
  rw [sub_eq_add_neg, zpow_add]
  ac_rfl

theorem exists_coeff (k : ℕ) (α : D.X)
    (τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ))))
    (hτ : ∀ (Z : Over _) (t : Z ⟶ splitTorus _ D.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (J), Good D.P.L z J →
      sval τ ((t ≫ g.i) * y).left z J = gs t.left z ⊤ (charUnit _ D.X α).val * sval τ y.left z J) :
    ∃ f : LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)),
      ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J →
        sval τ (𝟙 (thickObj R I e G).left) z J =
          sval f g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (formEq g k α)
    (pullMulSec τ (𝟙 _) (LB.invGen D.P.L _ _ (g.t α)) (DVR.invGen_isGen _ _ _ _ (g.t_gen α)))
  have hs' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = sval τ r z J * ((val (g.t α) r z J)⁻¹).val := fun Z r z J hJ => by
    refine (hs Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
    exact congrArg₂ (· * ·) (congrArg (sval τ · z J) (Category.comp_id r)) (congrArg Units.val (val_inv _ r))
  obtain ⟨d, hd⟩ := exists_descent (q := g.q) (i := g.i) (φ := fun i => (D.prBe I e).left ≫ D.famφB α i) (ε := DegPre.famε k)
    g.isKernel D.P.isLB s (fun Z t y z J hJ => by
      refine (hs' _ _ z J hJ).trans (Eq.trans ?_ (hs' _ _ z J hJ).symm)
      rw [hτ Z t y z J hJ, (TorusCoord.val_torus_point_and_translate R I D e G g Z t y z J hJ α).2,
        gs_unit t.left z ⊤ trivial, mul_inv, Units.val_mul, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨d, fun z J hJ => ?_⟩
  have E := (hd _ (𝟙 _) z J hJ).trans (hs' _ (𝟙 _) z J hJ)
  rw [Category.id_comp] at E
  exact ((congrArg (· * _) E).trans (Units.inv_mul_cancel_right _ _)).symm

theorem coeff_unique (k : ℕ)
    (f f' : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)))
    (s s' : Finset D.X) (h₀ : ∀ α ∉ s, ∀ j, (f α).f j = 0) (h₀' : ∀ α ∉ s', ∀ j, (f' α).f j = 0)
    (h : ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J →
      ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val =
        ∑ α ∈ s', sval (f' α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) : f = f' := by
  classical
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Mono (D.prBe I e).left := inferInstanceAs (Mono (pullback.fst D.P.A.hom (thick R I e)))
  funext α
  by_cases hα : α ∈ s ∪ s'
  swap
  · rw [Finset.mem_union, not_or] at hα
    exact DVR.SecOps.sec_ext fun j => (h₀ α hα.1 j).trans (h₀' α hα.2 j).symm
  have H := sval_eq_zero_of_sum_mul_coord R I D e G g _ (D.prBe I e) _ _ _ (fun α => secSub (f α) (f' α)) (s ∪ s')
    (fun Z x r hr z J hJ => by
      obtain rfl : r = x ≫ g.q.left := (cancel_mono (D.prBe I e).left).1 (hr.trans (Category.assoc _ _ _).symm)
      have hJ' := good_comp x hJ
      have E := h (x z) _ hJ'
      rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by
          rw [sval_eq_zero _ (h₀ β hβ) _ hJ', zero_mul]),
        Finset.sum_subset (Finset.subset_union_right (s₁ := s) (s₂ := s')) (fun β _ hβ => by
          rw [sval_eq_zero _ (h₀' β hβ) _ hJ', zero_mul]), ← sub_eq_zero, ← Finset.sum_sub_distrib] at E
      have E' := congrArg (x.stalkMap z).hom E
      rw [map_sum, map_zero] at E'
      refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) E'
      rw [← sub_mul, map_mul]
      refine congrArg₂ (· * ·) ((sval_comp _ x g.q.left hJ).trans (congrArg _ (sval_secSub _ _ _ hJ'))) ?_
      exact (congrArg (fun y => (val (g.t β) y z J).val) (Category.comp_id x).symm).trans (val_comp _ x (𝟙 _) hJ))
    α hα
  have H' := LiftTest.main R I D e G g _ (D.prBe I e) _ D.P.L D.P.isLB _ _ _ _ H
  refine DVR.SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => sub_eq_zero.1 ((sval_secSub _ _ _ hJ).symm.trans
    (H' _ (𝟙 _) ⟨(thickObj R I e D.P.A).hom, (Category.id_comp _).symm⟩ y J hJ)))

end LevelExpansion

open LevelExpansion in

theorem existsUnique_level_expansion : (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : ℕ) (σ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ)))), ∃! f : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)), ∃ s : Finset D.X, (∀ α ∉ s, ∀ j, (f α).f j = 0) ∧ ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J → sval σ (𝟙 (thickObj R I e G).left) z J = ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) := by
  intro R _ _ I D e G _ _ g k σ
  classical
  have := g.q_hom
  have := g.i_hom
  have := g.q_affine
  have : IsProper (thickObj R I e D.P.A).hom := by
    have := D.P.isAb.proper; show IsProper (pullback.snd _ _); infer_instance
  have : CompactSpace (thickObj R I e D.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (thickObj R I e D.P.A).hom
  obtain ⟨s, τ, -, h₁, h₂⟩ := exists_weights (q := g.q) (i := g.i) (φ := fun _ : Fin 1 => (D.prBe I e).left) (ε := fun _ => (k : ℤ))
    g.isKernel D.P.isLB σ
  choose d hd using fun α => exists_coeff g k α (τ α) (h₁ α)
  refine existsUnique_of_exists_of_unique ⟨fun α => if α ∈ s then d α else DVR.SecOps.secZero, s,
    fun α hα j => by beta_reduce; rw [if_neg hα]; rfl, fun z J hJ => ?_⟩ ?_
  · refine (h₂ _ (𝟙 _) z J hJ).trans (Finset.sum_congr rfl fun α hα => ?_)
    beta_reduce
    rw [if_pos hα]
    exact hd α z J hJ
  · rintro f f' ⟨s₁, a₁, b₁⟩ ⟨s₂, a₂, b₂⟩
    exact coeff_unique g k f f' s₁ s₂ a₁ a₂ fun z J hJ => (b₁ z J hJ).symm.trans (b₂ z J hJ)

end GlobalTheory
end
