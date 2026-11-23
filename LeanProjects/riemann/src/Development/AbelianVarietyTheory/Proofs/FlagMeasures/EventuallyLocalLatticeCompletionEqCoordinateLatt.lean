import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicU.Cofinite

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_mem_intLoc_iff_repr {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] E, y ∈ intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := by
  classical
  set ω := Module.Free.chooseBasis ℤ (𝓞 E) with hω
  have hI : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E), z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ _ => Iff.rfl
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ j k,
      algebraMap F (Fv F v) (b.repr ((ω j : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    intro j k
    exact eventually_algebraMap_mem_integers _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ k,
      (1 : Fv F v) ⊗ₜ[F] b k ∈ intLoc F E v := by
    rw [Filter.eventually_all]
    intro k
    exact eventually_one_tmul_mem_intLoc _
  filter_upwards [h1, h2] with v h1 h2 y
  have key : ∀ (x : 𝓞 E) (k : Fin d),
      algebraMap F (Fv F v) (b.repr (x : E) k) ∈ v.adicCompletionIntegers F := by
    intro x k
    have hx : (x : E) = ∑ j, (ω.repr x j) • ((ω j : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (ω.sum_repr x)
      rw [map_sum] at this
      simp only [map_zsmul] at this
      exact this.symm
    rw [hx, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]
    refine sum_mem fun j _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact zsmul_mem (h1 j k) _
  constructor
  · intro hy
    rw [hI] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      intro k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul]
      exact mul_mem ha (key x k)
    | zero => intro k; simp
    | add z w _ _ hz hw =>
      intro k
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hz k) (hw k)
    | neg z _ hz =>
      intro k
      rw [map_neg, Finsupp.neg_apply]
      exact neg_mem (hz k)
  · intro hy
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
    refine sum_mem fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.smul_def]
    refine mul_mem ?_ (h2 k)
    rw [hI]
    refine AddSubgroup.subset_closure ⟨_, hy k, 1, ?_⟩
    simp [Algebra.TensorProduct.algebraMap_apply]

theorem eventually_latLoc_eq_latV :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
      (b : Module.Basis (Fin d) F E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L →
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} = latV b v := by
  intro F E _ _ _ _ _ n d b L hL
  haveI := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_latLoc_eq F L (stdLattice E n), eventually_mem_intLoc_iff_repr b]
    with v hv h1
  have hI : ∀ z : Fv F v ⊗[F] E, z ∈ intLoc F E v ↔
      z ∈ AddSubgroup.closure {z : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E,
        z = a ⊗ₜ[F] (x : E)} := fun _ => Iff.rfl
  have hS : ∀ y : Fin n → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E n) v ↔
      y ∈ AddSubgroup.closure {y : Fin n → Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F,
        ∃ x ∈ stdLattice E n, y = fun i => a ⊗ₜ[F] x i} := fun _ => Iff.rfl
  have hstd : ∀ x : Fin n → E, x ∈ stdLattice E n ↔ ∀ i, ∃ z : 𝓞 E, (z : E) = x i := by
    intro x
    unfold stdLattice Formalism.UG.stdLat
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range,
      Algebra.linearMap_apply]
  have hloc : ∀ y, y ∈ latLoc F (stdLattice E n) v ↔ ∀ i, y i ∈ intLoc F E v := by
    intro y
    constructor
    · intro hy i
      rw [hS] at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hz
        obtain ⟨w, hw⟩ := (hstd x).1 hx i
        rw [hI]
        exact AddSubgroup.subset_closure ⟨a, ha, w, by rw [hw]⟩
      | zero => exact zero_mem _
      | add z w _ _ hz hw => exact add_mem hz hw
      | neg z _ hz => exact neg_mem hz
    · intro hy
      rw [← Finset.univ_sum_single y, hS]
      refine sum_mem fun i _ => ?_
      have hyi := hy i
      rw [hI] at hyi
      revert hyi
      generalize y i = z0
      intro hyi
      induction hyi using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, x, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : E), (hstd _).2 fun j => ?_, ?_⟩
        · by_cases h : j = i
          · subst h
            exact ⟨x, by simp⟩
          · exact ⟨0, by simp [h]⟩
        · funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [h]
      | zero => simp
      | add z w _ _ hz hw =>
        rw [Pi.single_add]
        exact add_mem hz hw
      | neg z _ hz =>
        rw [Pi.single_neg]
        exact neg_mem hz
  ext X
  unfold latV
  simp only [Set.mem_setOf_eq, hv, hloc, h1, Fin.forall_fin_one]

end GlobalTheory.AdelicU.Cofinite
