import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNatMulMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNsmulIntegersMem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImportsBis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImportsTer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NsmulIntegralMemNhdsZero
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

namespace GlobalTheory.AdLat.OpenLat

variable (F : Type) [Field F] [NumberField F]

theorem isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  first
  | exact @_root_.GlobalTheory.IntegralOpen.isOpen_integral
  | exact _root_.GlobalTheory.IntegralOpen.isOpen_integral
  | (apply _root_.GlobalTheory.IntegralOpen.isOpen_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralOpen.isOpen_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralOpen.isOpen_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralOpen.isOpen_integral ..)

theorem exists_nsmul_adele (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → N • a ∈ U := by
  first
  | exact @_root_.GlobalTheory.LocalNormBound.main
  | exact _root_.GlobalTheory.LocalNormBound.main
  | (apply _root_.GlobalTheory.LocalNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalNormBound.main ..)

theorem nsmul_integral_mem_nhds (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (𝓞 F) F | ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
  first
  | exact @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
  | (apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero ..)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [Algebra F E] in

theorem exists_denom (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target
  | (apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemUnitaryExistence.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemUnitaryExistence.target ..)

theorem isOpen_nsmul_hat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  intro F E _ _ _ _ _ n L hL
  classical
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  haveI : ContinuousSMul (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.toContinuousSMul _ _
  refine ⟨fun N hN => ?_, fun W hW => ?_⟩
  · let S : AddSubgroup (Fin n → RA F E) := (hat F (L : Set (Fin n → E))).map (nsmulAddMonoidHom N)
    have hS : {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y} = S := by
      ext z
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩
    rw [hS]
    refine S.isOpen_of_mem_nhds (g := 0) ?_
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
    choose d hd hdL using fun i k => exists_denom L hL (Pi.single i (b k))
    have hn : ∀ᶠ z : Fin n → RA F E in 𝓝 0, ∀ i k, ∃ a : FiniteAdeleRing (𝓞 F) F,
        (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ B.repr (z i) k = (N * d i k) • a := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro k
      have hc : Continuous fun z : Fin n → RA F E => B.coord k (z i) :=
        (IsModuleTopology.continuous_of_linearMap (B.coord k)).comp (continuous_apply i)
      have := nsmul_integral_mem_nhds F (N * d i k) (Nat.mul_pos hN (hd i k))
      have h0 : B.coord k ((0 : Fin n → RA F E) i) = 0 := map_zero _
      exact hc.continuousAt.preimage_mem_nhds (x := 0) (h0 ▸ this)
    refine Filter.mem_of_superset hn fun z hz => ?_
    choose a ha hza using hz
    refine ⟨∑ i, ∑ k, fun j => a i k ⊗ₜ[F] (d i k • (Pi.single i (b k) : Fin n → E)) j,
      sum_mem fun i _ => sum_mem fun k _ =>
        AddSubgroup.subset_closure ⟨a i k, ha i k, _, hdL i k, rfl⟩, ?_⟩
    funext j
    rw [nsmulAddMonoidHom_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Finset.sum_apply, ← B.sum_repr (z j), Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hza, Algebra.TensorProduct.basis_apply, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul,
        smul_smul, smul_assoc]
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · intro i _ hij
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero, TensorProduct.tmul_zero]
    · simp
  · let w := RingOfIntegers.basis E
    let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) → RA F E :=
      fun c => ∑ k, c k • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E (w k))
    have hφ : Continuous φ := continuous_finset_sum _ fun k _ => by fun_prop
    have h0 : φ 0 = 0 := by simp [φ]
    have h1 : φ ⁻¹' W ∈ 𝓝 0 := hφ.continuousAt.preimage_mem_nhds (h0 ▸ hW)
    rw [nhds_pi, Filter.mem_pi] at h1
    obtain ⟨I, -, t, ht, hsub⟩ := h1
    obtain ⟨N, hN, hNt⟩ := exists_nsmul_adele F (⋂ k, t k) (Filter.iInter_mem.mpr ht)
    refine ⟨N, hN, fun y hy => ?_⟩
    have hex : ∃ c, (∀ k v, c k v ∈ v.adicCompletionIntegers F) ∧ φ c = y := by
      induction hy using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hx
        refine ⟨fun k => w.repr x k • a, fun k v => zsmul_mem (ha v) _, ?_⟩
        conv_rhs => rw [← w.sum_repr x, map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zsmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      | zero => exact ⟨0, fun k v => zero_mem _, h0⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hc, rfl⟩ := hx
        obtain ⟨e, he, rfl⟩ := hy
        exact ⟨c + e, fun k v => add_mem (hc k v) (he k v), by simp [φ, add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact ⟨-c, fun k v => neg_mem (hc k v), by simp [φ]⟩
    obtain ⟨c, hc, rfl⟩ := hex
    have h2 : N • φ c = φ (N • c) := by
      simp only [φ, Finset.smul_sum, Pi.smul_apply, smul_assoc]
    rw [h2]
    exact hsub fun k _ => Set.mem_iInter.mp (hNt (c k) (hc k)) k

end GlobalTheory.AdLat.OpenLat
