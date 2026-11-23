import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace GlobalTheory.AdeleBaseChange

theorem isOpen_of_tmul_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (S : AddSubgroup (Af F ⊗[F] E))
    (hS : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x : 𝓞 E, a ⊗ₜ[F] (x : E) ∈ S) :
    IsOpen (S : Set (Af F ⊗[F] E)) := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Af F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Af F) _
  refine S.isOpen_of_mem_nhds (g := 0) ?_
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Af F) b
  obtain ⟨D, hD, hb⟩ := exists_nat_mul_integral (Finset.univ.image b)
  choose o ho using fun i => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hn : ∀ᶠ z : Af F ⊗[F] E in 𝓝 0, ∀ k, ∃ a : Af F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ B.repr z k = D • a := by
    rw [Filter.eventually_all]
    intro k
    have hc : Continuous fun z : Af F ⊗[F] E => B.coord k z :=
      IsModuleTopology.continuous_of_linearMap (B.coord k)
    have := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F D hD
    have h0 : B.coord k (0 : Af F ⊗[F] E) = 0 := map_zero _
    exact hc.continuousAt.preimage_mem_nhds (x := 0) (h0 ▸ this)
  refine Filter.mem_of_superset hn fun z hz => ?_
  choose a ha hza using hz
  rw [← B.sum_repr z]
  refine sum_mem fun k _ => ?_
  have e : B.repr z k • B k = a k ⊗ₜ[F] ((o k : 𝓞 E) : E) := by
    change _ = a k ⊗ₜ[F] algebraMap (𝓞 E) E (o k)
    rw [ho, hza, Algebra.TensorProduct.basis_apply, TensorProduct.tmul_smul, smul_assoc]
    congr 1
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  exact hS _ (ha k) _

theorem exists_integral_subring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    ∃ (R : Subring (Af F ⊗[F] E)) (ι : (Af F ⊗[F] E) ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ R ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1) ∧
      IsCompact (R : Set (Af F ⊗[F] E)) ∧ IsOpen (R : Set (Af F ⊗[F] E)) ∧ (∀ a ∈ R, sigR (Af F) σ a ∈ R) ∧
      ∀ a : Af F ⊗[F] E, ∃ N : ℕ, N ≠ 0 ∧ (N : Af F ⊗[F] E) * a ∈ R := by
  intro F E _ _ _ _ _ σ
  obtain ⟨ι, -, hι, -⟩ := exists_tensor_finiteAdele_equiv F E
  let I : Subring (FiniteAdeleRing (𝓞 E) E) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
      mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
      one_mem' := fun v => one_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      zero_mem' := fun v => zero_mem _
      neg_mem' := fun ha v => neg_mem (ha v) }
  let R : Subring (Af F ⊗[F] E) := I.comap ι.toRingHom
  have hR : ∀ y, y ∈ R ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1 := fun y => Iff.rfl
  have hm : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ x : 𝓞 E,
      a ⊗ₜ[F] (x : E) ∈ R := fun a ha x =>
    (hR _).2 ((hι _).1 (AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩))
  refine ⟨R, ι, hR, ?_, isOpen_of_tmul_mem F E R.toAddSubgroup hm, fun y hy => ?_, fun a => ?_⟩
  · have h := (GlobalTheory.AdeleCocompact.isCompact_integral E).image (continuous_symm_finite F E ι hι)
    have e : (R : Set (Af F ⊗[F] E)) =
        ι.symm '' {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} := by
      ext y
      constructor
      · intro hy
        exact ⟨ι y, hy, ι.symm_apply_apply y⟩
      · rintro ⟨a, ha, rfl⟩
        exact (hR _).2 fun P => by rw [ι.apply_symm_apply]; exact ha P
    rw [e]
    exact h
  · have hy' := (hι y).2 ((hR y).1 hy)
    clear hy
    induction hy' using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact hm a ha (RingOfIntegers.mapRingHom (σ : E →+* E) x)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · obtain ⟨M, hM, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral E (ι a)
    refine ⟨M, hM.ne', (hR _).2 fun P => ?_⟩
    rw [map_mul, map_natCast]
    exact h P

end GlobalTheory.AdeleBaseChange
