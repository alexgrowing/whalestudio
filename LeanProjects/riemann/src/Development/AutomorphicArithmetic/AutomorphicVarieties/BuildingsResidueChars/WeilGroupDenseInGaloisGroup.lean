import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne in
theorem UpperTheory.weil_group_dense_in_galois_group :
    UpperTheory.V.Af.Wd.WeilDense := by
  intro F Ω _ _ _ _ _ w A h
  have hσ := isFrob_frob (h := h)
  have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A w h ⟨_, hσ.1⟩ hσ
  have h2 : (Subgroup.zpowers (⟨_, hσ.1⟩ : Dec (F := F) A) ⊔
      (Ine (F := F) A).subgroupOf (Dec (F := F) A)) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
    refine sup_le ?_ fun x hx => ⟨⟨x, Ine_le_Weil h hx⟩, rfl⟩
    exact (Subgroup.zpowers_le).2 ⟨frob h, rfl⟩
  have h3 := Subgroup.topologicalClosure_mono h2
  rw [h1] at h3
  intro g
  exact h3 (Subgroup.mem_top g)
