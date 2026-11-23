import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.GenHW

theorem block_span_hw : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  intro R S M Λ v hv
  have hKS : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set G := GlobalTheory.BlockReps.gen M.act v with hG
  set ρ := restrAct M.act G hKS with hρ
  have hρapp : ∀ Z, IsKC Z → ∀ x : G, ((ρ Z x : G) : M.V) = M.act Z x := by
    intro Z hZ x
    rw [hρ, restrAct_apply, kpart_of_isKC hZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
    exact Submodule.finiteDimensional_of_le (GlobalTheory.BlockReps.gen_le hvW hWs)
  · intro Y Z hY hZ
    ext x
    have hYZ := GlobalTheory.TensorHW.isKC_comm hY hZ
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [hρapp _ hYZ, hρapp _ hY, hρapp _ hZ, hρapp _ hZ, hρapp _ hY, M.lie]
    simp
  · intro w
    have h := GlobalTheory.BlockReps.decomp hKS w.2 (M.wts w)
    have hle : (⨆ μ, G ⊓ wtSub M.act μ) ≤ (⨆ μ : Ix R S → ℚ, wtSub ρ μ).map G.subtype := by
      refine iSup_le fun μ x hx => ⟨⟨x, hx.1⟩, Submodule.mem_iSup_of_mem μ ?_, rfl⟩
      rw [GlobalTheory.TensorHW.mem_wt]
      intro a
      apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact GlobalTheory.TensorHW.mem_wt.1 hx.2 a
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle h)
    rwa [Subtype.val_injective hyw] at hy
  · refine ⟨fun h => hv.1 (congrArg Subtype.val h), ?_⟩
    have hv2 := GlobalTheory.TensorHW.mem_hw.1 hv.2
    rw [GlobalTheory.TensorHW.mem_hw]
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact hv2.1 a
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hab))]
      exact hv2.2 a b hab
  · set N := GlobalTheory.BlockReps.gen ρ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hN
    have hNs : KStable ρ N := GlobalTheory.BlockReps.stable_gen (act := ρ) _
    have hmap : KStable M.act (N.map G.subtype) := by
      rintro X hX _ ⟨y, hy, rfl⟩
      exact ⟨ρ X y, hNs X hX y hy, hρapp X hX y⟩
    have hle : G ≤ N.map G.subtype :=
      GlobalTheory.BlockReps.gen_le ⟨⟨v, GlobalTheory.BlockReps.mem_gen v⟩, GlobalTheory.BlockReps.mem_gen _, rfl⟩ hmap
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle w.2)
    rwa [Subtype.val_injective hyw] at hy

end GlobalTheory.GenHW
