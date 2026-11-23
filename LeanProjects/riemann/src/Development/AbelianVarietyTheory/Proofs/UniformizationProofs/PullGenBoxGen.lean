import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxCubical

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_res)

section Box

variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K K' : Type} [Fintype J] [Fintype K] [Fintype K']

lemma gU_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι) (y : Y)
    (hy : y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gU y hy ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gU y (GeneratorPullback.box_le L F φ jj i hy) ((t i).s (fun k _ => jj k i)) := by
  show gU y hy (∏ i, _) = _
  exact (map_prod (gU y hy) _ _).trans (Finset.prod_congr rfl fun i _ => gU_res _ _ _ _)

lemma gU_pullGen (M : LB X') (φ : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb M φ ε))
    (a : Z ⟶ Y) (j : K → M.ι) (z : Z) (hz : z ∈ LB.wchart M (fun k => a ≫ φ k) j) :
    gU z hz ((LB.pullGen M φ ε t a).s j) =
      Units.map (RingHom.toMonoidHom (a.stalkMap z).hom)
        (gU (a.base z) (LBxP.wpl M φ a j hz) (t.s j)) :=
  (gU_res _ _ _ _).trans (gU_pullU a _ z _ _)

lemma pullGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (a : Z ⟶ Y) :
    LB.pullGen (LB.LinComb L F (fun _ => 1)) φ ε (GeneratorPullback.boxGen L F φ ε t) a =
      GeneratorPullback.boxGen L F (fun k => a ≫ φ k) ε (fun i => LB.pullGen (L.pull (F i)) φ ε (t i) a) := by
  apply LBxP.gen_ext
  intro jj z hz
  refine (gU_pullGen _ φ ε _ a jj z hz).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (fun k => a ≫ φ k) ε _ jj z hz).symm
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap z).hom))
    (gU_boxGen L F φ ε t jj (a.base z) _)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (gU_pullGen (L.pull (F i)) φ ε (t i) a _ z _).symm

lemma mulGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε')) :
    LB.mulGen (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
        (GeneratorPullback.boxGen L F φ' ε' t') =
      GeneratorPullback.boxGen L F (Sum.elim φ φ') (Sum.elim ε ε')
        (fun i => LB.mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine (LBxP.gU_mulGen _ φ ε φ' ε' _ _ jj y hy).trans ?_
  refine Eq.trans ?_ (gU_boxGen L F (Sum.elim φ φ') (Sum.elim ε ε') _ jj y hy).symm
  refine (congrArg₂ (· * ·) (gU_boxGen L F φ ε t _ y _) (gU_boxGen L F φ' ε' t' _ y _)).trans ?_
  refine Finset.prod_mul_distrib.symm.trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (LBxP.gU_mulGen (L.pull (F i)) φ ε φ' ε' (t i) (t' i) (fun k _ => jj k i) y _).symm

lemma oneGen_boxGen (F : J → (X' ⟶ X)) :
    LB.oneGen (Y := Y) (LB.LinComb L F (fun _ => 1)) =
      GeneratorPullback.boxGen L F PEmpty.elim PEmpty.elim (fun i => LB.oneGen (L.pull (F i))) := by
  apply LBxP.gen_ext
  intro jj y hy
  refine Eq.trans ?_ (gU_boxGen L F PEmpty.elim PEmpty.elim _ jj y hy).symm
  refine (map_one (gU y hy)).trans (Finset.prod_eq_one fun i _ => ?_).symm
  exact map_one (gU y _)

lemma corr_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε))
    (t' : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ' ε'))
    (h : ∀ i, LB.Gen.Corr (L.pull (F i)) φ ε φ' ε' (t i) (t' i)) :
    LB.Gen.Corr (LB.LinComb L F (fun _ => 1)) φ ε φ' ε' (GeneratorPullback.boxGen L F φ ε t)
      (GeneratorPullback.boxGen L F φ' ε' t') := by
  intro jj jj' h1 h2 h12
  apply unit_ext
  intro y hy
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((gU_res _ y hy _).trans (gU_boxGen L F φ' ε' t' jj' y hy.2)).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := h i (fun k _ => jj k i) (fun k _ => jj' k i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h1 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h2 k₁ k₂ e) i)
    (fun k₁ k₂ e => funext fun _ => congrFun (h12 k₁ k₂ e) i)
  have hy' : y ∈ LB.wchart (L.pull (F i)) φ (fun k _ => jj k i) ⊓
      LB.wchart (L.pull (F i)) φ' (fun k _ => jj' k i) :=
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ' jj' i hy.2⟩
  exact (gU_res _ y hy' _).symm.trans ((congrArg (gU y hy') H).trans (gU_res _ y hy' _))

lemma gU_pull_lcg (F : J → (X' ⟶ X)) (δ : J → ℤ) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F δ).U i ⊓ (LB.LinComb L F δ).U j)) :
    gU y hy (pullU a _ ((LB.LinComb L F δ).g i j)) =
      ∏ n, (gU y (show y ∈ (a ≫ F n) ⁻¹ᵁ (L.U (i n) ⊓ L.U (j n)) from
        ⟨LB.wchart_le L F i n hy.1, LB.wchart_le L F j n hy.2⟩)
        (pullU (a ≫ F n) _ (L.g (i n) (j n)))) ^ δ n := by
  refine (gU_pullU a _ y hy _).trans ?_
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom))
    (LBxP.gU_lcg L F δ i j (a.base y) hy)).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun n _ => ?_)
  refine (map_zpow _ _ _).trans (congrArg (· ^ δ n) ?_)
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact LBxP.gU_pullU_comp a (F n) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (h : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro jj jj'
  apply unit_ext
  intro y hy
  have hy' : ∀ i, y ∈ (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj k i) ⊓
      (LB.LinComb (L.pull (F i)) φ ε).U (fun k _ => jj' k i) := fun i =>
    ⟨GeneratorPullback.box_le L F φ jj i hy.1, GeneratorPullback.box_le L F φ jj' i hy.2⟩
  have hg : gU y hy ((LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε).g jj jj') =
      ∏ i, gU y (hy' i) ((LB.LinComb (L.pull (F i)) φ ε).g (fun k _ => jj k i)
        (fun k _ => jj' k i)) := by
    refine (LBxP.gU_lcg _ φ ε jj jj' y hy).trans ?_
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ =>
      LBxP.gU_lcg (L.pull (F i)) φ ε _ _ y (hy' i)).symm
    refine Eq.trans ?_ Finset.prod_comm
    refine Finset.prod_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (Finset.prod_zpow _ _ _).symm
    refine congrArg (· ^ ε k) ?_
    refine (gU_pull_lcg L F (fun _ => 1) (φ k) (jj k) (jj' k) y _).trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    refine (zpow_one _).trans ?_
    exact (LBxP.gU_pull_g L (F i) (φ k) (fun _ => jj k i) (fun _ => jj' k i) y _ _).symm
  refine ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj y hy.1)).trans ?_
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg
    ((gU_res _ y hy _).trans (gU_boxGen L F φ ε t jj' y hy.2)))).symm
  refine Eq.trans ?_ Finset.prod_mul_distrib
  refine Finset.prod_congr rfl fun i _ => ?_
  have H := congrArg (gU y (hy' i)) (h i (fun k _ => jj k i) (fun k _ => jj' k i))
  exact (gU_res _ y (hy' i) _).symm.trans (H.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gU_res _ y (hy' i) _))))

end Box

section Cub

variable {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] {X : Scheme.{0}}
  {J : Type} [Fintype J]

def prodCubical (L : LB X) (F : J → (G'.left ⟶ X))
    (r : ∀ i, LB.Gen ((L.pull (F i)).pull (eSec G'))) (hL : ∀ i, (L.pull (F i)).IsLB)
    (hr : ∀ i, (r i).IsGen) (c : ∀ i, CubicalStr G' ⟨L.pull (F i), r i, hL i, hr i⟩)
    (r' : LB.Gen ((LB.LinComb L F (fun _ => 1)).pull (eSec G')))
    (hL' : (LB.LinComb L F (fun _ => 1)).IsLB) (hr' : r'.IsGen) :
    CubicalStr G' ⟨LB.LinComb L F (fun _ => 1), r', hL', hr'⟩ where
  t := GeneratorPullback.boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t)
  isGen := isGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) (fun i => (c i).isGen)
  face := fun n =>
    LBxP.corr_of_eq (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (oneGen_boxGen L F) (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).face n))
  cubeSymmetric_swap_first :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_first))
  cubeSymmetric_swap_last :=
    LBxP.corr_of_eq rfl (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
      (corr_boxGen L F (thφ G' (x3 G')) thε _ _ (fun i => (c i).t) _ (fun i => (c i).cubeSymmetric_swap_last))
  cocycle :=
    LBxP.corr_of_eq
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      ((congrArg₂ (LB.mulGen (LB.LinComb L F (fun _ => 1)) _ _ _ _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)
        (pullGen_boxGen L F (thφ G' (x3 G')) thε (fun i => (c i).t) _)).trans
        (mulGen_boxGen L F _ _ _ _ _ _))
      (corr_boxGen L F _ _ _ _ _ _ (fun i => (c i).cocycle))

end Cub

end GlobalTheory.BoxCubical

namespace GlobalTheory

theorem boxCubical : ∀ S : Scheme.{0}, BoxCubicalSt (S := S) := by
  intro S G' G _ _ _ _ j p L c hL hr
  let m : Fin j → CubeMap G' G := fun i => letI := p.hom i; CubeMap.ofHom (p.pr i)
  have hLi : ∀ i, (L.L.pull (m i).F).IsLB := fun i => LB.isLB_pull L.isLB (m i).F
  have hri : ∀ i, ((m i).rigPull L.L L.rig).IsGen := fun i =>
    LBxP.isGen_pullAlong L.L (m i).F (m i).e (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec G') (fun _ => (m i).e_comm) L.rig L.rigGen
  exact ⟨BoxCubical.prodCubical L.L (fun i => (p.pr i).left) (fun i => (m i).rigPull L.L L.rig)
    hLi hri (fun i => CubePf.cubical (m i) L c (hLi i) (hri i)) _ hL hr, rfl⟩

end GlobalTheory
