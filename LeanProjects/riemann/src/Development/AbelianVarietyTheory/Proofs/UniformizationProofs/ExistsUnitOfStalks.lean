import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootUnit

open TopologicalSpace

theorem gs_id {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = (Y.presheaf.germ U y h).hom a := gs_eq (𝟙 Y) y U h a

theorem gs_ne_zero {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))

theorem exists_unit_of_stalks {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy

theorem exists_unit_of_stalks' {Y : Scheme.{0}} [IsIntegral Y] (W U V : Y.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, U)) (b : Γ(Y, V)) (hb : ∀ y ∈ W, gs (𝟙 Y) y V b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y U a = v.val * gs (𝟙 Y) y V b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y U a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y V b := by
  obtain ⟨r, hr⟩ := exists_unit_of_stalks W ((Y.presheaf.map (homOfLE hU).op).hom a)
    ((Y.presheaf.map (homOfLE hV).op).hom b)
    (fun y hy => by rw [gs_res (𝟙 Y) y hV hy]; exact hb y hy)
    (fun y hy => by rw [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy]; exact h y hy)
  refine ⟨r, fun y hy => ?_⟩
  have := hr y hy
  rwa [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy] at this

theorem sec_gs_ne_zero {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]

theorem trF_pull {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_gen_of_pow : ∀ (X Y : Scheme.{0}) [IsIntegral Y], (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → ∀ (L : LB X), L.IsLB → ∀ (f₁ f₂ : Y ⟶ X) (l : ℕ), 1 ≤ l → ∀ (s₁ : LB.Sec (L.pull f₁)) (s₂ : LB.Sec (L.pull f₂)) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![(l : ℤ), -(l : ℤ)])), u.IsGen → (∃ j, s₂.f j ≠ 0) → (∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J ^ l = (val u (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J ^ l) → ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![1, -1]), r.IsGen ∧ ∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J = (val r (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J := by
  intro X Y _ hN L hL f₁ f₂ l hl s₁ s₂ u _ hs H
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₂ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have main : ∀ j : Fin 2 → L.ι, ∃ r : Γ(Y, LB.wchart L ![f₁, f₂] j)ˣ, ∀ y ∈ LB.wchart L ![f₁, f₂] j,
      gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0)) (s₁.f fun _ => j 0) =
        (gm (𝟙 Y) y _ r).val *
          gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1)) (s₂.f fun _ => j 1) := by
    intro j
    exact exists_unit_of_stalks' (LB.wchart L ![f₁, f₂] j) _ _ (l₁ j) (l₂ j) _ _
      (fun y hy => sec_gs_ne_zero s₂ hs y _ (l₂ j hy))
      (fun y hy => by
        choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
        have hJ' : Good L y J := hJ
        haveI := hN y
        have as : Associated (sval s₂ (𝟙 Y) y J) (sval s₁ (𝟙 Y) y J) :=
          (Associated.pow_iff (by omega : l ≠ 0)).1 ⟨val u (𝟙 Y) y J, (_root_.mul_comm _ _).trans (H y J hJ').symm⟩
        obtain ⟨v, hv⟩ := as
        have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ j hy) (hJ'.mem (K := PUnit) (fun _ => f₁) (𝟙 Y))
        have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ j hy) (hJ'.mem (K := PUnit) (fun _ => f₂) (𝟙 Y))
        change _ = _ * sval s₁ (𝟙 Y) y J at e₁
        change _ = _ * sval s₂ (𝟙 Y) y J at e₂
        rw [e₁, e₂, ← hv]
        generalize trF (L := L) (K := PUnit) (fun _ => f₁) (fun _ => 1) (𝟙 Y) y _ _ = t₁
        generalize trF (L := L) (K := PUnit) (fun _ => f₂) (fun _ => 1) (𝟙 Y) y _ _ = t₂
        refine ⟨t₁ * v * t₂⁻¹, ?_⟩
        rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
        ring)
  choose r hr using main
  refine ⟨⟨r⟩, fun i j => unit_ext fun y hy => ?_, fun y J hJ => hr _ y (hJ.mem ![f₁, f₂] (𝟙 Y))⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) (gm_res _ y _ hy _))).symm)
  have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ i hy.1) (l₂ j hy.2)
  have hb := sec_gs_ne_zero s₂ hs y _ (l₂ j hy.2)
  rw [hr i y hy.1, hr j y hy.2, e₂, trF_pull, trF_pull, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul] at e₁
  have e := Units.ext (mul_right_cancel₀ hb e₁)
  rw [Fin.prod_univ_two]
  change gm (𝟙 Y) y _ (r i) = gm (𝟙 Y ≫ f₁) y _ (L.g (i 0) (j 0)) ^ (1 : ℤ) *
    gm (𝟙 Y ≫ f₂) y _ (L.g (i 1) (j 1)) ^ (-1 : ℤ) * gm (𝟙 Y) y _ (r j)
  rw [zpow_one, zpow_neg_one, mul_right_comm, ← e, mul_inv_cancel_right]

end GlobalTheory.RootUnit
