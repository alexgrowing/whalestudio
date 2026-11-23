import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycle
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenIsoRatio

theorem gm_pullU_res {X Y : Scheme.{0}} (β : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ β ⁻¹ᵁ U) (y : Y)
    (hy : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU β U a)) = gm β y U a := by
  rw [gm_res (𝟙 Y) y h hy, gm_pull (𝟙 Y) β y U (h hy), Category.id_comp]

theorem gm_pull_g' {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by
  have hp : y ∈ (L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU β _ (L.g i i'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) β y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _).trans (by rw [Category.id_comp]))

theorem ratio : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro X Y β P M N hP hM hN w w₁ v hw hw₁ hv
  let W : N.ι × P.ι × M.ι → Y.Opens := fun j =>
    N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) ⊓ (M.pull β).U (fun _ => j.2.2)
  have l₁ : ∀ j, W j ≤ N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) := fun j => inf_le_left
  have l₂ : ∀ j, W j ≤ N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2) := fun j =>
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have l₃ : ∀ j, W j ≤ β ⁻¹ᵁ (M.U j.2.2 ⊓ P.U j.2.1) := fun j y hy =>
    ⟨mem_pull.1 hy.2, mem_pull.1 hy.1.2⟩
  let r : ∀ j, Γ(Y, W j)ˣ := fun j =>
    res (l₁ j) (w₁.s (j.1, fun _ => j.2.1)) * (res (l₃ j) (pullU β _ (v.s (j.2.2, j.2.1))))⁻¹ *
      (res (l₂ j) (w.s (j.1, fun _ => j.2.2)))⁻¹
  have k : ∀ j (y : Y), y ∈ W j → gm (𝟙 Y) y (W j) (r j) =
      gm (𝟙 Y) y (N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1)) (w₁.s (j.1, fun _ => j.2.1)) *
        (gm β y (M.U j.2.2 ⊓ P.U j.2.1) (v.s (j.2.2, j.2.1)))⁻¹ *
        (gm (𝟙 Y) y (N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2)) (w.s (j.1, fun _ => j.2.2)))⁻¹ := by
    intro j y hy
    simp only [r, map_mul, map_inv]
    erw [gm_res (𝟙 Y) y (l₁ j) hy, gm_res (𝟙 Y) y (l₂ j) hy, gm_pullU_res β _ (l₃ j) y hy]
  obtain ⟨u, hu⟩ := glue_unit (⊤ : Y.Opens) W (fun _ => le_top)
    (fun y _ => by
      obtain ⟨n, hn⟩ := exists_chart hN y
      obtain ⟨i, hi⟩ := exists_chart hP (β y)
      obtain ⟨m, hm⟩ := exists_chart hM (β y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(n, i, m), ⟨hn, mem_pull.2 hi⟩, mem_pull.2 hm⟩) r
    (fun j j' y hy => by
      have hi := mem_pull.1 hy.1.1.2
      have hi' := mem_pull.1 hy.2.1.2
      have hm := mem_pull.1 hy.1.2
      have hm' := mem_pull.1 hy.2.2
      rw [k j y hy.1, k j' y hy.2,
        GlobalTheory.PartialCocycle.gm_iso hw₁ (𝟙 Y) y j.1 j'.1 (fun _ => j.2.1) (fun _ => j'.2.1) hy.1.1.1 hy.2.1.1
          hy.1.1.2 hy.2.1.2,
        GlobalTheory.PartialCocycle.gm_iso hw (𝟙 Y) y j.1 j'.1 (fun _ => j.2.2) (fun _ => j'.2.2) hy.1.1.1 hy.2.1.1
          hy.1.2 hy.2.2,
        GlobalTheory.PartialCocycle.gm_iso hv β y j.2.2 j'.2.2 j.2.1 j'.2.1 hm hm' hi hi',
        gm_pull_g' β P y _ _ hi hi', gm_pull_g' β M y _ _ hm hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨u, fun n i m hle => ?_⟩
  have e : res (l₁ (n, i, m)) (w₁.s (n, fun _ => i)) =
      res (le_top : W (n, i, m) ≤ ⊤) u * res hle (pullU β _ (v.s (m, i))) * res (l₂ (n, i, m)) (w.s (n, fun _ => m)) := by
    change _ = _ * res (l₃ (n, i, m)) (pullU β _ (v.s (m, i))) * _
    rw [hu (n, i, m)]
    simp only [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact congrArg Units.val e

end GlobalTheory.GenIsoRatio
