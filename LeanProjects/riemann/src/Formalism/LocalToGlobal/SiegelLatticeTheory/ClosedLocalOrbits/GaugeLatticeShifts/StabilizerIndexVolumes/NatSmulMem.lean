import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StClosed
import Lemmata.GeneralBFactThirdVersion.Imports

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Den

variable {E : Type} [Field E] [NumberField E]

theorem intE_iff (x : E) : IntE x ↔ IsIntegral ℤ x := by
  rw [IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  rfl

theorem intE_zero : IntE (0 : E) := ⟨0, by simp⟩

theorem intE_one : IntE (1 : E) := ⟨1, by simp⟩

theorem intE_nat (k : ℕ) : IntE (k : E) := ⟨k, by simp⟩

theorem intE_add {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by simp⟩

theorem intE_neg {x : E} (hx : IntE x) : IntE (-x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨-a, by simp⟩

theorem intE_sub {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x - y) := by
  rw [sub_eq_add_neg]; exact intE_add hx (intE_neg hy)

theorem intE_mul {x y : E} (hx : IntE x) (hy : IntE y) : IntE (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by simp⟩

theorem intE_nat_mul (k : ℕ) {x : E} (hx : IntE x) : IntE ((k : E) * x) := intE_mul (intE_nat k) hx

theorem intE_sum {ι : Type*} (s : Finset ι) (x : ι → E) (h : ∀ i ∈ s, IntE (x i)) : IntE (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intE_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intE_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intE_star [StarRing E] {x : E} (hx : IntE x) : IntE (star x) := by
  rw [intE_iff] at hx ⊢
  exact hx.map (starRingEnd E).toIntAlgHom

theorem den_exists (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IntE ((m : E) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, h⟩ := hx.exists_nsmul_eq (𝓞 E)
  refine ⟨m, hm, s, ?_⟩
  rw [← nsmul_eq_mul, h]

theorem den_fin {ι : Type*} [Fintype ι] (x : ι → E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ i, IntE ((m : E) * x i) := by
  classical
  choose m hm hx using fun i => den_exists (x i)
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr (fun i _ => hm i), fun i => ?_⟩
  have : ((∏ j, m j : ℕ) : E) * x i = ((∏ j ∈ Finset.univ.erase i, m j : ℕ) : E) * ((m i : E) * x i) := by
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast; ring
  rw [this]
  exact intE_nat_mul _ (hx i)

theorem intE_scale {m : ℕ} (k : ℕ) {x : E} (h : IntE ((m : E) * x)) : IntE (((k * m : ℕ) : E) * x) := by
  have : ((k * m : ℕ) : E) * x = (k : E) * ((m : E) * x) := by push_cast; ring
  rw [this]; exact intE_nat_mul k h

theorem den_mat {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ i j, IntE ((k : E) * A i j) := by
  obtain ⟨k, hk, h⟩ := den_fin (fun p : m × n => A p.1 p.2)
  exact ⟨k, hk, fun i j => h (i, j)⟩

theorem intE_matmul {l m n : Type*} [Fintype m] {A : Matrix l m E} {B : Matrix m n E} {a b : ℕ}
    (hA : ∀ i j, IntE ((a : E) * A i j)) (hB : ∀ i j, IntE ((b : E) * B i j)) :
    ∀ i j, IntE (((a * b : ℕ) : E) * (A * B) i j) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine intE_sum _ _ fun k _ => ?_
  have : ((a * b : ℕ) : E) * (A i k * B k j) = ((a : E) * A i k) * ((b : E) * B k j) := by push_cast; ring
  rw [this]; exact intE_mul (hA i k) (hB k j)

end Den

section Lat

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem coe_smul_eq (o : 𝓞 E) (v : V) : (o : E) • v = o • v := algebraMap_smul E o v

theorem nat_smul_mem (Λ : Submodule (𝓞 E) V) (k : ℕ) {v : V} (hv : v ∈ Λ) : (k : E) • v ∈ Λ := by
  rw [Nat.cast_smul_eq_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hv k

theorem int_smul_mem (Λ : Submodule (𝓞 E) V) {c : E} (hc : IntE c) {v : V} (hv : v ∈ Λ) : c • v ∈ Λ := by
  obtain ⟨o, rfl⟩ := hc
  rw [coe_smul_eq]; exact Λ.smul_mem o hv

theorem lat_smul_mem (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  first | exact Bl.general_b_fact_third_version.goal1 .. | (apply Bl.general_b_fact_third_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_version.goal1 <;> first | assumption | infer_instance)

theorem lat_fun_bdd (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) {ι : Type*} [Fintype ι]
    (φ : ι → V →ₗ[E] E) : ∃ m : ℕ, m ≠ 0 ∧ ∀ v ∈ Λ, ∀ i, IntE ((m : E) * φ i v) := by
  classical
  obtain ⟨S, hS⟩ := h.fg
  obtain ⟨m, hm, hmS⟩ := den_fin (fun p : ι × S => φ p.1 (p.2 : V))
  refine ⟨m, hm, fun v hv i => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hmS (i, ⟨x, hx⟩)
  | zero => simpa using intE_zero
  | add x y _ _ hx hy => rw [map_add, mul_add]; exact intE_add hx hy
  | smul o x _ hx =>
    rw [← coe_smul_eq, LinearMap.map_smul, smul_eq_mul, mul_left_comm]
    exact intE_mul ⟨o, rfl⟩ hx

theorem coord_exists [FiniteDimensional E V] {n : ℕ} {f : Fin n → V} (hf : LinearIndependent E f) :
    ∃ φ : Fin n → V →ₗ[E] E, ∀ c d, φ c (f d) = if d = c then 1 else 0 := by
  classical
  have : ∀ c : Fin n, ∃ G : V →ₗ[E] E, ∀ d, G (f d) = if d = c then 1 else 0 := by
    intro c
    obtain ⟨G, hG⟩ := LinearMap.exists_extend ((Finsupp.lapply c).comp hf.repr)
    refine ⟨G, fun d => ?_⟩
    have h1 : G (f d) = (G.comp (Submodule.span E (Set.range f)).subtype) ⟨f d, Submodule.subset_span ⟨d, rfl⟩⟩ := rfl
    rw [h1, hG]
    rw [LinearMap.comp_apply, hf.repr_eq_single d _ rfl, Finsupp.lapply_apply, Finsupp.single_apply]
  choose φ hφ using this
  exact ⟨φ, hφ⟩

end Lat

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
