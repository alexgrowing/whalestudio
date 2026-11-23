import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.SingleDatum

theorem exists_basis_integral_coords : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (O : Subring ℂ), (∀ x : F, la.valuation F x ≤ 1 → (x : ℂ) ∈ O) → ∀ S : Set ℂ, S.Finite → S ⊆ O → ∃ (m : ℕ) (β : Fin m → ℂ) (lam : Fin m → (ℂ →ₗ[F] F)), (∀ k, β k ∈ O) ∧ ∀ x ∈ S, x = ∑ k, β k * (lam k x : ℂ) ∧ ∀ k, la.valuation F (lam k x) ≤ 1 := by
  intro F _ la O hO S hS hSO
  let R := (la.valuation F).integer
  have hsm : ∀ (r : R) (z : ℂ), r • z = (((r : F) : ℂ)) * z := fun r z => rfl
  let N : Submodule R ℂ := Submodule.span R S
  haveI : Module.Finite R N := Module.Finite.span_of_finite R hS
  haveI : Module.IsTorsionFree R N := inferInstance
  haveI : Module.Free R N := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis R N).reindex (Fintype.equivFin _)
  let m := Fintype.card (Module.Free.ChooseBasisIndex R N)
  let β : Fin m → ℂ := fun k => ((b k : N) : ℂ)
  have hliR : LinearIndependent R β := b.linearIndependent.map' N.subtype N.ker_subtype
  have hliF : LinearIndependent F β := (LinearIndependent.iff_fractionRing R F).1 hliR
  choose g hg using fun k : Fin m => LinearMap.exists_extend ((Finsupp.lapply k).comp hliF.repr)
  have key : ∀ k j, g k (β j) = if j = k then 1 else 0 := by
    intro k j
    have hmem : β j ∈ Submodule.span F (Set.range β) := Submodule.subset_span ⟨j, rfl⟩
    have := LinearMap.congr_fun (hg k) ⟨β j, hmem⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hliF.repr_eq_single j _ rfl]
    simp [Finsupp.single_apply]
  have hNO : ∀ z ∈ N, z ∈ O := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hSO hy
    | zero => exact O.zero_mem
    | add y w _ _ hy hw => exact O.add_mem hy hw
    | smul r y _ hy =>
      rw [hsm]
      exact O.mul_mem (hO _ ((Valuation.mem_integer_iff _ _).1 r.2)) hy
  refine ⟨m, β, g, fun k => hNO _ (b k).2, ?_⟩
  intro x hx
  have hxN : x ∈ N := Submodule.subset_span hx
  let c : Fin m → F := fun j => ((b.repr ⟨x, hxN⟩ j : R) : F)
  have hxs : x = ∑ j, c j • β j := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hxN⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Submodule.coe_smul, hsm, Algebra.smul_def]
    rfl
  have hg' : ∀ k, g k x = c k := by
    intro k
    rw [hxs, map_sum]
    simp only [map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨?_, fun k => ?_⟩
  · conv_lhs => rw [hxs]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg', Algebra.smul_def, mul_comm]
    rfl
  · rw [hg']
    exact (Valuation.mem_integer_iff _ _).1 (b.repr ⟨x, hxN⟩ k).2

end GlobalTheory.SingleDatum
