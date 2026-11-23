import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.GenPush

variable {X Y : Scheme.{0}}

private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} {h : V ≤ U} (hy : f y ∈ V)
    (a : Γ(X, U)ˣ) : gm f y V (res h a) = gm f y U a := by
  apply Units.ext
  rw [← gs_unit f y V hy, ← gs_unit f y U (h hy)]
  exact gs_res f y h hy a.val

private theorem gm_id_pullU_eq_gm {X Y : Scheme.{0}} (c : Y ⟶ X) (y : Y) {U : X.Opens} (hy : c y ∈ U)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y (c ⁻¹ᵁ U) (pullU c U a) = gm c y U a := by
  have hy' : (𝟙 Y ≫ c) y ∈ U := by simpa using hy
  apply Units.ext
  rw [← gs_unit (𝟙 Y) y (c ⁻¹ᵁ U) (by simpa using hy), ← gs_unit c y U hy]
  have e := gs_pull (𝟙 Y) c y U (by simpa using hy) a.val
  rw [Category.id_comp] at e
  exact e

private theorem mem_pull_U_of_mem {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) {y : Y} {a : N.ι} (ha : c y ∈ N.U a) :
    y ∈ (N.pull c).U (fun _ => a) := by
  unfold LB.pull LB.LinComb LB.wchart
  exact Set.mem_iInter.2 fun _ => ha

private theorem gm_id_pull_g_eq_gm_g {X Y : Scheme.{0}} (N : LB X) (c : Y ⟶ X) (y : Y) {a b : N.ι} (ha : c y ∈ N.U a)
    (hb : c y ∈ N.U b) :
    gm (𝟙 Y) y ((N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b)) ((N.pull c).g (fun _ => a) (fun _ => b)) =
      gm c y (N.U a ⊓ N.U b) (N.g a b) := by
  have hm : (𝟙 Y) y ∈ (N.pull c).U (fun _ => a) ⊓ (N.pull c).U (fun _ => b) :=
    ⟨mem_pull_U_of_mem N c (by simpa using ha), mem_pull_U_of_mem N c (by simpa using hb)⟩
  revert hm
  unfold LB.pull LB.LinComb
  dsimp only
  intro hm
  simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
  exact (gm_res_eq_gm (𝟙 Y) y hm _).trans (gm_id_pullU_eq_gm c y (show c y ∈ N.U a ⊓ N.U b from ⟨ha, hb⟩) _)

private theorem gm_div_g_eq_mul_inv {X Y : Scheme.{0}} (A B : LB X) (f : Y ⟶ X) (y : Y) (p q : (A.div B).ι)
    (hp : f y ∈ A.U p.1 ⊓ B.U p.2) (hq : f y ∈ A.U q.1 ⊓ B.U q.2) :
    gm f y ((A.div B).U p ⊓ (A.div B).U q) ((A.div B).g p q) =
      gm f y (A.U p.1 ⊓ A.U q.1) (A.g p.1 q.1) * (gm f y (B.U p.2 ⊓ B.U q.2) (B.g p.2 q.2))⁻¹ := by
  unfold LB.div
  dsimp only
  rw [map_mul, map_inv, gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩,
    gm_res_eq_gm f y (V := (A.U p.1 ⊓ B.U p.2) ⊓ (A.U q.1 ⊓ B.U q.2)) ⟨hp, hq⟩]

theorem exists_gen_of_units (c : Y ⟶ X) [IsOpenImmersion c] (N : LB X) (hN : ∀ a, N.U a ≤ c.opensRange)
    (V : N.ι → Y.Opens) (hV : ∀ a y, c y ∈ N.U a → y ∈ V a) (s : ∀ a, Γ(Y, V a)ˣ)
    (hs : ∀ (y : Y) a b, c y ∈ N.U a → c y ∈ N.U b →
      gm (𝟙 Y) y (V a) (s a) = gm c y (N.U a ⊓ N.U b) (N.g a b) * gm (𝟙 Y) y (V b) (s b)) :
    ∃ t : N.Gen, t.IsGen := by
  have hW : ∀ a, c ⁻¹ᵁ N.U a ≤ V a := fun a y hy => hV a y hy
  choose b hb using fun a => exists_ext_unit c (c ⁻¹ᵁ N.U a) (res (hW a) (s a))
  have hE : ∀ a, N.U a ≤ c ''ᵁ (c ⁻¹ᵁ N.U a) := by
    intro a x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx
    exact ⟨y, hx, rfl⟩
  have key : ∀ (y : Y) a, c y ∈ N.U a → gm c y (c ''ᵁ (c ⁻¹ᵁ N.U a)) (b a) = gm (𝟙 Y) y (V a) (s a) := by
    intro y a ha
    have e := hb a Y (𝟙 Y) y (by simpa using ha)
    rw [Category.id_comp] at e
    rw [e, gm_res_eq_gm (𝟙 Y) y (by simpa using ha)]
  refine ⟨⟨fun a => res (hE a) (b a)⟩, ?_⟩
  unfold LB.Gen.IsGen
  intro a a'
  apply Units.ext
  apply fn_ext
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range c := hN a hx.1
  have hx' : (𝟙 X) (c y) ∈ N.U a ⊓ N.U a' := by simpa using hx
  rw [gs_unit (𝟙 X) (c y) _ hx', gs_unit (𝟙 X) (c y) _ hx']
  congr 1
  apply gm_inj c y hx hx
  rw [map_mul, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.1, gm_res_eq_gm c y hx, gm_res_eq_gm c y hx.2,
    key y a hx.1, key y a' hx.2]
  exact hs y a a' hx.1 hx.2

theorem gen_stalk {N : LB Y} {t : N.Gen} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y (N.U i) (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y (N.U j) (t.s j) := by
  unfold LB.Gen.IsGen at ht
  have hm : (𝟙 Y) y ∈ N.U i ⊓ N.U j := by simpa using (⟨hi, hj⟩ : y ∈ N.U i ⊓ N.U j)
  have e := congrArg (gm (𝟙 Y) y (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y hm, gm_res_eq_gm (𝟙 Y) y hm] at e
  exact e

theorem gen_iso_of_charts_le_range : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  intro X Y c _
  refine ⟨fun N hN ⟨t, ht⟩ => ?_, fun M M' hM ⟨w, hw⟩ => ?_⟩
  · refine exists_gen_of_units c N hN (fun a => (N.pull c).U (fun _ => a)) (fun a y hy => mem_pull_U_of_mem N c hy)
      (fun a => t.s (fun _ => a)) ?_
    intro y a b ha hb
    rw [gen_stalk ht y (fun _ => a) (fun _ => b) (mem_pull_U_of_mem N c ha) (mem_pull_U_of_mem N c hb),
      gm_id_pull_g_eq_gm_g N c y ha hb]
  · have hN : ∀ p : (M'.div M).ι, (M'.div M).U p ≤ c.opensRange := by
      intro p
      show M'.U p.1 ⊓ M.U p.2 ≤ _
      rw [inf_comm]
      exact hM p.2 p.1
    have hV : ∀ (p : (M'.div M).ι) (y : Y), c y ∈ (M'.div M).U p →
        y ∈ ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι) :=
      fun p y hy => ⟨mem_pull_U_of_mem M' c hy.1, mem_pull_U_of_mem M c hy.2⟩
    obtain ⟨t, ht⟩ := exists_gen_of_units c (M'.div M) hN
      (fun p => ((M'.pull c).div (M.pull c)).U ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) hV
      (fun p => w.s ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)) (by
        intro y p q hp hq
        rw [gen_stalk hw y _ _ (hV p y hp) (hV q y hq)]
        congr 1
        have m1 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => p.1) ⊓ (M.pull c).U (fun _ => p.2) := hV p y hp
          simpa using h
        have m2 : (𝟙 Y) y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := by
          have h : y ∈ (M'.pull c).U (fun _ => q.1) ⊓ (M.pull c).U (fun _ => q.2) := hV q y hq
          simpa using h
        have e1 := gm_div_g_eq_mul_inv (M'.pull c) (M.pull c) (𝟙 Y) y
          ((fun _ => p.1, fun _ => p.2) : (M'.pull c).ι × (M.pull c).ι)
          ((fun _ => q.1, fun _ => q.2) : (M'.pull c).ι × (M.pull c).ι) m1 m2
        have e2 := gm_div_g_eq_mul_inv M' M c y p q hp hq
        refine e1.trans (Eq.trans ?_ e2.symm)
        dsimp only
        rw [gm_id_pull_g_eq_gm_g M' c y hp.1 hq.1, gm_id_pull_g_eq_gm_g M c y hp.2 hq.2])
    exact ⟨t, ht⟩

end GlobalTheory.GenPush
