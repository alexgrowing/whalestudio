import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.WittTensorFixed

theorem tensor_flat {R W T : Type} [CommRing R] [CommRing W] [Algebra R W] [AddCommGroup T]
    [Module R T] [Module.Flat R T] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : W ⊗[R] T, ∃ b, TensorProduct.map f.toLinearMap LinearMap.id b - b = y) ∧
    (∀ b : W ⊗[R] T, TensorProduct.map f.toLinearMap LinearMap.id b = b ↔
      ∃ t : T, b = (1 : W) ⊗ₜ[R] t) ∧
    Function.Injective (fun t : T => (1 : W) ⊗ₜ[R] t) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : W ⊗[R] T,
      TensorProduct.map f.toLinearMap LinearMap.id b - b = g.rTensor T b := by
    intro b
    simp only [g, LinearMap.rTensor_sub, LinearMap.rTensor_id, LinearMap.sub_apply,
      LinearMap.id_apply]
    rfl
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := rTensor_exact T hex gsurj
  have emb : ∀ t : T, (1 : W) ⊗ₜ[R] t = i.rTensor T ((1 : R) ⊗ₜ[R] t) := by
    intro t
    simp [i]
  have hrange : ∀ x : R ⊗[R] T, i.rTensor T x = (1 : W) ⊗ₜ[R] TensorProduct.lid R T x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r t =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, i, Algebra.linearMap_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]
  refine ⟨fun y => ?_, fun b => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective T gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have hiff : TensorProduct.map f.toLinearMap LinearMap.id b = b ↔ g.rTensor T b = 0 := by
      rw [← key, sub_eq_zero]
    rw [hiff, hexT]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨TensorProduct.lid R T x, hrange x⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(1 : R) ⊗ₜ t, (emb t).symm⟩
  · have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := T) i hi
    intro t t' h
    have h' : i.rTensor T ((1 : R) ⊗ₜ[R] t) = i.rTensor T ((1 : R) ⊗ₜ[R] t') := by
      rw [← emb, ← emb]
      exact h
    simpa using congrArg (TensorProduct.lid R T) (hinj h')

theorem baseChange_flat {R W O : Type} [CommRing R] [CommRing W] [Algebra R W] [CommRing O]
    [Algebra R O] [Module.Flat R O] (f : W →ₐ[R] W) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap R W z)
    (hi : Function.Injective (algebraMap R W)) :
    (∀ y : O ⊗[R] W, ∃ b, Algebra.TensorProduct.map (AlgHom.id O O) f b - b = y) ∧
    (∀ b : O ⊗[R] W, Algebra.TensorProduct.map (AlgHom.id O O) f b = b →
      ∃ z, b = algebraMap O (O ⊗[R] W) z) ∧
    Function.Injective (algebraMap O (O ⊗[R] W)) := by

  let g : W →ₗ[R] W := f.toLinearMap - LinearMap.id
  let i : R →ₗ[R] W := Algebra.linearMap R W
  have key : ∀ b : O ⊗[R] W,
      Algebra.TensorProduct.map (AlgHom.id O O) f b - b = g.lTensor O b := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul o w => simp [g, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]; abel
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨b, hb⟩ := hs y
    exact ⟨b, by simpa [g] using hb⟩
  have hex : Function.Exact i g := by
    intro y
    constructor
    · intro hy
      have hfy : f y = y := by
        have h2 : f y - y = 0 := by simpa [g] using hy
        exact sub_eq_zero.mp h2
      obtain ⟨z, rfl⟩ := hk y hfy
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      simp [g, i]
  have hexT := lTensor_exact O hex gsurj
  have emb : ∀ z : O, algebraMap O (O ⊗[R] W) z = i.lTensor O (z ⊗ₜ[R] (1 : R)) := by
    intro z
    simp [i]
  have hrange : ∀ x : O ⊗[R] R,
      i.lTensor O x = algebraMap O (O ⊗[R] W) (TensorProduct.rid R O x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, i, Algebra.linearMap_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      rw [Algebra.algebraMap_eq_smul_one (A := W) r, ← TensorProduct.smul_tmul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  refine ⟨fun y => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := LinearMap.lTensor_surjective O gsurj y
    exact ⟨b, by rw [key]; exact hb⟩
  · have h0 : g.lTensor O b = 0 := by rw [← key, hb, sub_self]
    obtain ⟨x, rfl⟩ := (hexT b).mp h0
    exact ⟨TensorProduct.rid R O x, hrange x⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := O) i hi
    intro z z' h
    rw [emb, emb] at h
    simpa using congrArg (TensorProduct.rid R O) (hinj h)

theorem algebraMap_WCb_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (WCb l)) := by

  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hker : RingHom.ker (algebraMap ℤ_[l] (WCb l)) ≠ ⊥ := by
    intro h
    apply hne
    have hxk : x ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := hx
    rw [h] at hxk
    exact (Submodule.mem_bot _).mp hxk
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ n ∈ RingHom.ker (algebraMap ℤ_[l] (WCb l)) := by
    rw [hn]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (WittVector.p_nonzero l (Cb l)) hmem

theorem flat_lattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O) :
    Module.Flat O ↥T.L.T := by

  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨⟨a, ha⟩, hax⟩ := hx
  have hax' : a • x = 0 := hax
  rw [Submodule.mem_bot]
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hLL : algebraMap O LL a ≠ 0 := fun h => ha0 (hO (by rw [h, map_zero]))
  have hx0 : (algebraMap O LL a) • (x : T.V) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, hax']
    rfl
  exact Subtype.ext ((smul_eq_zero.mp hx0).resolve_left hLL)

theorem lattice_fixed {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsDomain O]
    [IsBezout O] (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (hs : ∀ y, ∃ b, f b - b = y)
    (hk : ∀ b, f b = b → ∃ z, b = algebraMap O R z)
    (hi : Function.Injective (algebraMap O R)) :
    (∀ y : TW R T, ∃ b, TWmap f T b - b = y) ∧
    (∀ b : TW R T, TWmap f T b = b ↔ ∃ t : ↥T.L.T, b = (1 : R) ⊗ₜ[O] t) ∧
    Function.Injective (fun t : ↥T.L.T => (1 : R) ⊗ₜ[O] t) := by
  haveI := flat_lattice hO T
  unfold TW TWmap
  exact tensor_flat f hs hk hi

theorem ring_fixed (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ y : RW LL, ∃ b, φRW LL b - b = y) ∧
    (∀ b : RW LL, φRW LL b = b → ∃ z, b = algebraMap ↥(OL LL) (RW LL) z) ∧
    Function.Injective (algebraMap ↥(OL LL) (RW LL)) := by
  obtain ⟨_, -, -, -, hfree, -, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  unfold RW φRW
  exact baseChange_flat (frobW l) hs hk (algebraMap_WCb_injective l)

set_option maxHeartbeats 1600000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  intro l _ K LL T
  obtain ⟨hdvr, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := fun a b h => Subtype.ext h
  obtain ⟨hs, hk, hi⟩ := ring_fixed l LL
  exact lattice_fixed hO T (φRW LL) hs hk hi

end GlobalTheory.WittTensorFixed
