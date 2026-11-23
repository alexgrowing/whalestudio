import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.WigSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ROpApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tens_map {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W)
    (T : Module.End ℂ (W ⊗[ℂ] (Fin d → ℂ))) (h : ∀ φ ∈ N, ∀ v, T (φ ⊗ₜ[ℂ] v) ∈ tens d N) :
    ∀ m ∈ tens d N, T m ∈ tens d N := by
  intro m hm
  rw [← sum_cmp m, map_sum]
  exact Submodule.sum_mem _ fun i _ => h _ (mem_tens.1 hm i) _

private theorem tmul_mem {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} {N : Submodule ℂ W} {φ : W} (h : φ ∈ N)
    (v : Fin d → ℂ) : φ ⊗ₜ[ℂ] v ∈ tens d N :=
  mem_tens.2 fun i => by rw [cmp_tmul]; exact N.smul_mem _ h

theorem UpperTheory.V.Cj.H.wigSm :
    UpperTheory.V.Cj.H.WigSm := by
  intro E _ _ _ a Ξ N hN τ m hm u q ω hc hd hv
  obtain ⟨hA, hB, hAB, -, -, hI⟩ := smAB E a Ξ
  obtain ⟨c1, c2, -, -⟩ := capSm E a Ξ τ u
  have hs : smA Ξ + smB Ξ = smLie Ξ := LinearMap.ext fun X => by
    rw [LinearMap.add_apply, smA_apply, smB_apply]; rfl
  have key := wigSub E a _ (smA Ξ) (smB Ξ) hA hB hAB (tens Ξ.d N)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smA_apply, LinearMap.rTensor_tmul]; exact tmul_mem (hN X φ hφ) _)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smB_apply, LinearMap.lTensor_tmul]; exact tmul_mem hφ _)
    τ (u + ((a : ℂ) - 1) / 2)
    ((cap τ u - (m.map (u + ·)).prod • (1 : Module.End ℂ (Sm E a))).rTensor (Fin Ξ.d → ℂ)) (by
      rw [c1, c2 m hm, LinearMap.rTensor_sub, LinearMap.rTensor_smul]
      congr 2
      exact LinearMap.rTensor_id _ _)
  rw [hs] at key
  cases q with
  | zero =>
    show app _ ω = 0
    refine AlternatingMap.ext fun Y => ?_
    exact key.1 ω (hI _ ω hc) hd Y
  | succ q =>
    obtain ⟨η, h1, h2⟩ := key.2 q ω (hI _ ω hc) hd (fun Y => mem_tens.2 (hv Y))
    exact ⟨η, fun X => mem_tens.1 (h1 X), AlternatingMap.ext fun Y => h2 Y⟩
