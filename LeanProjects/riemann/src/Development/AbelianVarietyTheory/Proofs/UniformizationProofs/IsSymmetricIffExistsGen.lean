import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SymmetricBundle

open Geo.Tor

theorem isSymmetric_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem gen_of_isSymmetric {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (h : L.IsSymmetric) :
    ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨he, w, hw, hm⟩ := h
  have oi : eSec G ≫ (ι[G]).left = eSec G := he.trans (Category.id_comp _)
  have pg := (isGen_iff w).1 hw
  have pm := (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he L.L j) (fun _ => rfl)).1 hm
  have m₀ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      (ι[G]).left x ∈ L.L.U (j 0) := fun j x hx => Set.mem_iInter.1 hx 0
  have m₁ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      x ∈ L.L.U (j 1) := fun j x hx => Set.mem_iInter.1 hx 1
  have le : ∀ j : Fin 2 → L.L.ι, LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j ≤
      (L.L.pull (ι[G]).left).U (fun _ => j 0) ⊓ L.L.U (j 1) := fun j x hx => ⟨mem_pull.2 (m₀ j x hx), m₁ j x hx⟩
  let s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]) :=
    ⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩
  have hs : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : Fin 2 → L.L.ι),
      f y ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j) (s.s j) = gw w f y (j 0) (j 1) :=
    fun Y f y j hj => gm_res f y (le j) hj _
  refine ⟨s, fun j j' => unit_ext fun x hx => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j hx.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L.L _ _ (𝟙 _) x j j' hx.1 hx.2)
        ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j' hx.2)))).symm)
    rw [pg _ (𝟙 _) x (j 0) (j' 0) (j 1) (j' 1) (m₀ _ _ hx.1) (m₀ _ _ hx.2) (m₁ _ _ hx.1) (m₁ _ _ hx.2),
      Fin.prod_univ_two]
    congr 1
    show _ = gm (𝟙 _ ≫ (ι[G]).left) x _ (L.L.g (j 0) (j' 0)) ^ (1 : ℤ) *
      gm (𝟙 _ ≫ 𝟙 _) x _ (L.L.g (j 1) (j' 1)) ^ (-1 : ℤ)
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  · have ri : (𝟙 _ ≫ eSec G) ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := by rw [Category.assoc, oi]
    have hq₀ : (𝟙 _ ≫ eSec G) y ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := hJ _
    have hq₁ : (ι[G]).left ((𝟙 _ ≫ eSec G) y) ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := by
      have := hJ ((𝟙 _ ≫ eSec G) ≫ (ι[G]).left)
      rw [congrArg J ri] at this
      exact this
    rw [val_pull hJ, val_one, val_of s (𝟙 _ ≫ eSec G) y J ![J (𝟙 _ ≫ eSec G), J (𝟙 _ ≫ eSec G)] (fun k => by
      fin_cases k
      · exact congrArg J ri
      · exact congrArg J (Category.comp_id _)), hs _ _ _ _ (Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hq₁, hq₀])]
    have a := pm _ (𝟙 _) y (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => hq₁) (fun _ => hq₀)
    rw [Category.comp_id, Fintype.prod_unique, zpow_one] at a
    exact mul_eq_right.1 a.symm

end SymmetricBundle

theorem isSymmetric_iff_exists_gen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), L.IsSymmetric ↔ ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) :=
  fun _ _ _ _ L => ⟨SymmetricBundle.gen_of_isSymmetric L,
    fun ⟨s, hs, hr⟩ => SymmetricBundle.isSymmetric_of_gen L s hs hr⟩

end GlobalTheory
