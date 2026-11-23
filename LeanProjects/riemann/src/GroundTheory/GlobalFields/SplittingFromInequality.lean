import Mathlib
import GroundTheory.GlobalFields.FirstInequalityStatement
import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
import GroundTheory.GlobalFields.Adele.WeakApproxUnits

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter Topology
open SemiLocal IdeleNorm

noncomputable section

section Approximation

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem IdeleGroup.finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    IdeleGroup.finiteProj v (IdeleGroup.diagonal K a) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a :=
  Units.ext (IdeleGroup.coe_finiteProj_diagonal v a)

theorem IdeleGroup.infiniteProj_diagonal (w : InfinitePlace K) (a : Kˣ) :
    IdeleGroup.infiniteProj w (IdeleGroup.diagonal K a) =
      Units.map (algebraMap K w.Completion).toMonoidHom a :=
  Units.ext (IdeleGroup.coe_infiniteProj_diagonal w a)

variable (L) in

theorem exists_diagonal_mul_mem_localNorms (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : IdeleGroup K) :
    ∃ a : Kˣ, (∀ v ∈ S, IdeleGroup.finiteProj v (IdeleGroup.diagonal K a * x) ∈
        (finiteLocalNorm L v).range) ∧
      ∀ w, IdeleGroup.infiniteProj w (IdeleGroup.diagonal K a * x) ∈
        (infiniteLocalNorm L w).range := by
  classical
  let U : Set (((v : S) → (v.1.adicCompletion K)ˣ) ×
      ((w : (Finset.univ : Finset (InfinitePlace K))) → (w.1.Completion)ˣ)) :=
    {p | (∀ v : S, p.1 v * IdeleGroup.finiteProj v.1 x ∈ (finiteLocalNorm L v.1).range) ∧
      ∀ w : (Finset.univ : Finset (InfinitePlace K)),
        p.2 w * IdeleGroup.infiniteProj w.1 x ∈ (infiniteLocalNorm L w.1).range}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun v : S ↦ (isOpen_range_finiteLocalNorm v.1).preimage
        (((continuous_apply v).comp continuous_fst).mul continuous_const)).inter
      (isOpen_iInter_of_finite fun w ↦ (isOpen_range_infiniteLocalNorm w.1).preimage
        (((continuous_apply w).comp continuous_snd).mul continuous_const))
  have hne : U.Nonempty := by
    refine ⟨(fun v ↦ (IdeleGroup.finiteProj v.1 x)⁻¹, fun w ↦ (IdeleGroup.infiniteProj w.1 x)⁻¹),
      fun v ↦ ?_, fun w ↦ ?_⟩
    · rw [inv_mul_cancel]
      exact one_mem _
    · rw [inv_mul_cancel]
      exact one_mem _
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S Finset.univ).exists_mem_open hU hne
  refine ⟨a, fun v hv ↦ ?_, fun w ↦ ?_⟩
  · rw [map_mul, IdeleGroup.finiteProj_diagonal]
    exact ha.1 ⟨v, hv⟩
  · rw [map_mul, IdeleGroup.infiniteProj_diagonal]
    exact ha.2 ⟨w, Finset.mem_univ w⟩

theorem ideleNorm_range_sup_eq_top_of_eventually_splitsCompletely
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ ?_
  set S := (eventually_cofinite.1 h).toFinset
  obtain ⟨a, hfin, hinf⟩ := exists_diagonal_mul_mem_localNorms L S x
  have hmem : IdeleGroup.diagonal K a * x ∈ (ideleNorm K L).range := by
    refine mem_range_ideleNorm_of_forall _ (fun v ↦ ?_) hinf
    by_cases hv : v ∈ S
    · exact hfin v hv
    · have hv' : SplitsCompletely L v := by simpa [S] using hv
      rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v
        ((splitsCompletely_iff_isFiniteSplit v).1 hv')]
      exact Subgroup.mem_top _
  have hx : x = (IdeleGroup.diagonal K a * x) * (IdeleGroup.diagonal K a)⁻¹ := by
    rw [mul_comm, inv_mul_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hmem (inv_mem ⟨a, rfl⟩)

end Approximation

section Cyclic

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic Gal(L/K)]

theorem FirstInequality.finrank_eq_one_of_eventually_splitsCompletely (hFI : FirstInequality.{u})
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, SplitsCompletely L v) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_sup_eq_top (ideleNorm_range_sup_eq_top_of_eventually_splitsCompletely h)

theorem FirstInequality.finrank_eq_one_of_splitsCompletely_of_finite (hFI : FirstInequality.{u})
    {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) (h : ∀ v ∉ T, SplitsCompletely L v) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_eventually_splitsCompletely
    (eventually_cofinite.2 (hT.subset fun v hv ↦ by_contra fun hvT ↦ hv (h v hvT)))

end Cyclic

end

end GroundTheory.Global
