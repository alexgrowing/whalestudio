import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi

lemma res_res' {X : Scheme.{0}} {U W Z : X.Opens} (h : W ≤ U) (h' : Z ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [show (homOfLE (h'.trans h)).op = (homOfLE h).op ≫ (homOfLE h').op from rfl,
    Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

lemma pullU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)ˣ) :
    pullU f W (res h x) = res ((TopologicalSpace.Opens.map f.base).monotone h) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  have e := congrArg (fun φ => φ.hom (x : Γ(X, U))) (f.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

lemma res_pullU_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (hZ : Z ≤ f ⁻¹ᵁ U) (hZ' : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res hZ (pullU f U x) = res hZ' (pullU f W (res h x)) := by
  rw [pullU_res, res_res']

section LinComb

variable {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

include hL in
lemma linComb_g_self (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j)
      ((LB.LinComb L φ ε).g j j) = 1 := by
  simp only [LB.LinComb, map_prod, map_zpow]
  refine Finset.prod_eq_one fun k _ => ?_
  erw [res_res', res_pullU_eq (φ k) (le_inf le_rfl le_rfl) _ (LB.wchart_le L φ j k), hL.g_self]
  rw [map_one, map_one, one_zpow]

set_option maxHeartbeats 1000000 in
include hL in
lemma linComb_cocycle (i j l : K → L.ι) :
    res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ j)
        ((LB.LinComb L φ ε).g i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ j ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤ LB.wchart L φ i ⊓ LB.wchart L φ l)
        ((LB.LinComb L φ ε).g i l) := by
  simp only [LB.LinComb, map_prod, map_zpow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  congr 1
  erw [res_res', res_res', res_res']

  have hT : LB.wchart L φ i ⊓ LB.wchart L φ j ⊓ LB.wchart L φ l ≤
      (φ k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k)) := by
    intro y hy
    exact ⟨⟨LB.wchart_le L φ i k hy.1.1, LB.wchart_le L φ j k hy.1.2⟩, LB.wchart_le L φ l k hy.2⟩
  erw [res_pullU_eq (φ k) (inf_le_left : L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (i k) ⊓ L.U (j k)) _ hT,
    res_pullU_eq (φ k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (j k) ⊓ L.U (l k)) _ hT,
    res_pullU_eq (φ k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U (i k) ⊓ L.U (j k) ⊓ L.U (l k) ≤ L.U (i k) ⊓ L.U (l k)) _ hT]
  rw [← map_mul, ← map_mul, hL.cocycle]

include hL in
lemma linComb_cover : ⨆ j, (LB.LinComb L φ ε).U j = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hc : ∀ k, ∃ i, (φ k).base y ∈ L.U i := by
    intro k
    have h1 : (φ k).base y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  choose j hj using hc
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, Set.mem_iInter.mpr hj⟩

include hL in

theorem linComb_isLB : (LB.LinComb L φ ε).IsLB where
  cover := linComb_cover L hL φ ε
  g_self := fun j => linComb_g_self L hL φ ε j
  cocycle := fun i j l => linComb_cocycle L hL φ ε i j l

end LinComb

end ReciprocityTheory.ChartRestriction.G.DVR
