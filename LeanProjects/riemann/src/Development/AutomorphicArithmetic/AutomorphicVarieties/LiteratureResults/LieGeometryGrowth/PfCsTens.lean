import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsLie
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

variable (E a) in

private def csSub : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.Cs φ.1}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro φ ψ ⟨R, hR⟩ ⟨S, hS⟩
    refine ⟨max R S, fun g hg => ?_⟩
    have h1 := hR g (lt_of_le_of_lt (le_max_left _ _) hg)
    have h2 := hS g (lt_of_le_of_lt (le_max_right _ _) hg)
    show φ.1 g + ψ.1 g = 0
    rw [h1, h2, add_zero]
  smul_mem' := by
    rintro c φ ⟨R, hR⟩
    refine ⟨R, fun g hg => ?_⟩
    show c • φ.1 g = 0
    rw [hR g hg, smul_zero]

private theorem cs_iff {d : ℕ} (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Pf.Cs (ev x) ↔ x ∈ tens d (csSub E a) := by
  rw [mem_tens]
  constructor
  · rintro ⟨R, hR⟩ j
    exact ⟨R, fun g hg => by rw [Pf.cmp_ev, hR g hg]; rfl⟩
  · intro h
    choose R hR using h
    refine ⟨∑ j, |R j|, fun g hg => funext fun j => ?_⟩
    rw [← Pf.cmp_ev]
    refine hR j g (lt_of_le_of_lt ?_ hg)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |R j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))

end

theorem UpperTheory.V.Lit.Geo.Pf.csTens :
    UpperTheory.V.Lit.Geo.Pf.CsTens := by
  intro E _ _ _ a Ξ r X x hx
  rw [cs_iff] at hx
  rw [cs_iff, cs_iff]
  have hA : smA Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    exact Pf.csLie E a _ X (mem_tens.1 hx j)
  have hB : smB Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
