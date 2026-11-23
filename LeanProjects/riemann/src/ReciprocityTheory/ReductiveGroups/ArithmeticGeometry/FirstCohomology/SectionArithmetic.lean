import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

def secAdd {M : LB Y} (s t : LB.Sec M) : LB.Sec M where
  f i := s.f i + t.f i
  compat i j := by rw [map_add, map_add, s.compat, t.compat, mul_add]

def secZero (M : LB Y) : LB.Sec M where
  f _ := 0
  compat _ _ := by rw [map_zero, map_zero, mul_zero]

def secCMul {M : LB Y} {V : Y.Opens} (hV : ∀ i, M.U i ≤ V) (c : Γ(Y, V)) (s : LB.Sec M) : LB.Sec M where
  f i := (Y.presheaf.map (homOfLE (hV i)).op).hom c * s.f i
  compat i j := fn_ext fun y hy => by
    have e := congrArg (gs (𝟙 Y) y (M.U i ⊓ M.U j)) (s.compat i j)
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy] at e
    rw [gs_res (𝟙 Y) y inf_le_left hy, gs_mul (𝟙 Y) y _ hy.1, gs_res (𝟙 Y) y (hV i) hy.1, e,
      gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y inf_le_right hy, gs_mul (𝟙 Y) y _ hy.2, gs_res (𝟙 Y) y (hV j) hy.2]
    ring

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε) :=
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l j)).op).hom ((h.app _).hom (s.f j))) =
            gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
        (gs_res _ y _ hj _).trans (gs_pull _ h y _ (l j hj) _)
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.assoc] }

theorem sval_pullSec {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullSec s h) r z J = sval s (r ≫ h) z J := by

  have hm1 := hJ.mem (fun k => h ≫ φ k) r
  have hm2 := hJ.mem φ (r ≫ h)
  simp only [Category.assoc] at hm2
  unfold sval
  simp only [Category.assoc]
  exact (gs_res r z _ hm1 _).trans (gs_pull r h z _ hm2 _)

def mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) :
    LB.Sec (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) :=
  have l₁ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
      (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K' → L.ι, y ∈ LB.wchart L (Sum.elim φ φ') j →
          gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (l₁ j)).op).hom (s.f (j ∘ Sum.inl)) *
            (Y.presheaf.map (homOfLE (l₂ j)).op).hom (t.f (j ∘ Sum.inr))) =
          gs (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            gs (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (t.f (j ∘ Sum.inr)) := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y) y (l₁ j hy.1) (l₁ j' hy.2), sec_trans t (𝟙 Y) y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Sum.elim_inl, Sum.elim_inr]
      rfl }

theorem sval_mulSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (t : LB.Sec (LB.LinComb L φ' ε')) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (mulSec s t) r z J = sval s r z J * sval t r z J := by

  have hm := hJ.mem (Sum.elim φ φ') r
  unfold sval
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

def powSec {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L (fun p : I × K => φ p.2) (fun p => ε p.2)) :=
  have l : ∀ (j : I × K → L.ι) (i : I), LB.wchart L (fun p : I × K => φ p.2) j ≤ LB.wchart L φ (fun k => j (i, k)) :=
    fun _ i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { f := fun j => ∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))
    compat := fun j j' => fn_ext fun y hy => by
      have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.2) j →
          gs (𝟙 Y) y _ (∏ i, (Y.presheaf.map (homOfLE (l j i)).op).hom ((s i).f (fun k => j (i, k)))) =
          ∏ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) := fun j hj => by
        rw [gs_eq (𝟙 Y) y _ hj, map_prod, map_prod]
        exact Finset.prod_congr rfl fun i _ => (gs_eq (𝟙 Y) y _ hj _).symm.trans (gs_res _ y _ hj _)
      refine ((gs_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2))) ((gs_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
      have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ (fun k => j (i, k))) ((s i).f (fun k => j (i, k))) =
          (trF φ ε (𝟙 Y) y (fun k => j (i, k)) (fun k => j' (i, k))).val *
            gs (𝟙 Y) y (LB.wchart L φ (fun k => j' (i, k))) ((s i).f (fun k => j' (i, k))) :=
        fun i => sec_trans (s i) (𝟙 Y) y (l j i hy.1) (l j' i hy.2)
      rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, ← Units.coe_prod]
      congr 2
      simp only [trF]
      rw [Fintype.prod_prod_type] }

theorem sval_powSec {I : Type} [Fintype I] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : I → LB.Sec (LB.LinComb L φ ε))
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (powSec s) r z J = ∏ i, sval (s i) r z J := by

  have hm := hJ.mem (fun p : I × K => φ p.2) r
  unfold sval
  dsimp only [powSec]
  refine (gs_eq r z _ hm _).trans ?_
  erw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => (gs_eq r z _ hm _).symm.trans (gs_res r z _ hm _)

theorem germ_eq_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y)
    {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (j : K → L.ι) (hy : y ∈ LB.wchart L φ j) :
    (Y.presheaf.germ (LB.wchart L φ j) y hy).hom (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  have h1 := sec_trans s (𝟙 Y) y (j' := fun k => J (𝟙 Y ≫ φ k)) hy (hJ.mem φ (𝟙 Y))
  erw [gs_eq (𝟙 Y) y _ hy] at h1
  unfold sval
  rw [← h1]
  first | rfl | simp

theorem isUnit_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (k : (LB.LinComb L φ ε).ι) (hk : r z ∈ Y.basicOpen (s.f k)) :
    IsUnit (sval s r z J) := by

  have hkU : r z ∈ LB.wchart L φ k := Y.basicOpen_le _ hk
  have hm := hJ.mem φ r
  unfold sval
  rw [sec_trans s r z hm hkU]
  refine (Units.isUnit _).mul ?_
  erw [gs_eq r z _ hkU]
  have hz : z ∈ Z.basicOpen ((r.app _).hom (s.f k)) := by
    rw [← Scheme.preimage_basicOpen]; exact hk
  exact (Z.mem_basicOpen _ z hkU).1 hz

end ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
