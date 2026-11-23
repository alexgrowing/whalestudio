import Mathlib
open scoped TensorProduct

namespace GlobalTheory.FlatIdealInf

open TensorProduct

theorem range_lTensor_iInf_le {B R M : Type} [CommRing B] [AddCommGroup R] [Module B R]
    [Module.Flat B R] [AddCommGroup M] [Module B M] {ι : Type} [Finite ι]
    (K : ι → Submodule B M) :
    ⨅ i, LinearMap.range (LinearMap.lTensor R (K i).subtype) ≤
      LinearMap.range (LinearMap.lTensor R (⨅ i, K i).subtype) := by
  classical
  cases nonempty_fintype ι
  intro t ht
  rw [Submodule.mem_iInf] at ht
  let φ : M →ₗ[B] (∀ i, M ⧸ K i) := LinearMap.pi (fun i => (K i).mkQ)
  have hexB : Function.Exact (⨅ i, K i).subtype φ := by
    rw [LinearMap.exact_iff, LinearMap.ker_pi, Submodule.range_subtype]
    simp only [Submodule.ker_mkQ]
  have hex := Module.Flat.lTensor_exact R hexB
  have hcomp : ∀ i (u : R ⊗[B] M), TensorProduct.piRight B B R (fun i => M ⧸ K i) (LinearMap.lTensor R φ u) i =
      LinearMap.lTensor R (K i).mkQ u := by
    intro i u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [φ]
    | add x y hx hy => simp_all
  have h0 : LinearMap.lTensor R φ t = 0 := by
    apply (TensorProduct.piRight B B R (fun i => M ⧸ K i)).injective
    rw [map_zero]
    funext i
    rw [hcomp i t, Pi.zero_apply]
    obtain ⟨s, hs⟩ := ht i
    rw [← hs]
    exact (lTensor_exact R (LinearMap.exact_subtype_mkQ (K i)) (Submodule.mkQ_surjective _) _).mpr
      ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := (hex t).mp h0
  exact ⟨s, hs⟩

theorem mem_map_algebraMap_iff {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by
  rw [← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]
  let e := (Algebra.TensorProduct.rid B R R).toRingEquiv
  have he : (e : R ⊗[B] B →+* R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R := by
    ext b
    simp [e, Algebra.algebraMap_eq_smul_one]
  rw [← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

theorem iInf_map_le_map_iInf : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B),
    ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  intro B R _ _ _ _ ι _ K x hx
  rw [mem_map_algebraMap_iff]
  have h := range_lTensor_iInf_le (R := R) (fun i => (K i).restrictScalars B)
  have hK : (⨅ i, (K i).restrictScalars B) = (⨅ i, K i).restrictScalars B := by
    ext y; simp
  rw [hK] at h
  apply h
  rw [Submodule.mem_iInf]
  intro i
  exact (mem_map_algebraMap_iff (K i) x).mp ((Submodule.mem_iInf _).mp hx i)

end GlobalTheory.FlatIdealInf
