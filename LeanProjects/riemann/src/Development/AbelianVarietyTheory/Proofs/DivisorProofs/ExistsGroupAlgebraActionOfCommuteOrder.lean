import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LKGeo.CommBC

theorem actOn_tmul_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (a b : R) (c : C) (v : V) :
    actOn rep R (a ⊗ₜ c) (b ⊗ₜ v) = (a * b) ⊗ₜ rep c v := by
  have : actOn rep R (a ⊗ₜ c) = Algebra.ofId R _ a * Module.End.baseChangeHom ℚ R V (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ a c
  rw [this, Module.End.mul_apply]
  simp only [Algebra.ofId_apply, Module.algebraMap_end_apply]
  change a • (LinearMap.baseChange R (rep c)) (b ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem exists_actOn_eq {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) {ι' : Type} (S : ι' → Module.End ℚ V)
    (hrange : ∀ B : Module.End ℚ V, (∀ b, B * S b = S b * B) → ∃ x, rep x = B)
    (R : Type) [CommRing R] [Algebra ℚ R] (A : Module.End R (R ⊗[ℚ] V))
    (hA : ∀ b, A * (S b).baseChange R = (S b).baseChange R * A) : ∃ y, actOn rep R y = A := by
  classical
  let r := Module.Free.chooseBasis ℚ R
  let e : R ⊗[ℚ] V ≃ₗ[ℚ] (Module.Free.ChooseBasisIndex ℚ R →₀ V) :=
    (LinearEquiv.rTensor V r.repr).trans (TensorProduct.finsuppScalarLeft ℚ V _)
  have he : ∀ (a : R) (v : V) k, e (a ⊗ₜ v) k = r.repr a k • v := by
    intro a v k
    simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  let Ak : Module.Free.ChooseBasisIndex ℚ R → Module.End ℚ V := fun k =>
    (Finsupp.lapply k) ∘ₗ e.toLinearMap ∘ₗ (A.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ R V 1)
  have hAk : ∀ k v, Ak k v = e (A (1 ⊗ₜ v)) k := fun k v => rfl
  have heS : ∀ (s : Module.End ℚ V) (x : R ⊗[ℚ] V) k, e (s.baseChange R x) k = s (e x k) := by
    intro s x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [he]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hcomm : ∀ k b, Ak k * S b = S b * Ak k := by
    intro k b; ext v
    simp only [Module.End.mul_apply, hAk]
    have := congrArg (fun f => f ((1 : R) ⊗ₜ v)) (hA b)
    simp only [Module.End.mul_apply, LinearMap.baseChange_tmul] at this
    rw [this, heS]
  choose x hx using fun k => hrange (Ak k) (hcomm k)
  let bV := Module.finBasis ℚ V
  let F := Finset.univ.biUnion fun i => (e (A ((1 : R) ⊗ₜ bV i))).support
  have hzero : ∀ k ∉ F, Ak k = 0 := by
    intro k hk
    refine bV.ext fun i => ?_
    rw [hAk, LinearMap.zero_apply]
    by_contra h
    exact hk (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  refine ⟨∑ k ∈ F, r k ⊗ₜ x k, ?_⟩
  have h1 : ∀ v, actOn rep R (∑ k ∈ F, r k ⊗ₜ x k) ((1 : R) ⊗ₜ v) = A ((1 : R) ⊗ₜ v) := by
    intro v
    apply e.injective
    ext j
    rw [map_sum, LinearMap.sum_apply, map_sum, Finsupp.finset_sum_apply]
    simp_rw [actOn_tmul_tmul, _root_.mul_one, hx, he, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul]
    rw [Finset.sum_ite_eq', ← hAk]
    split_ifs with hj
    · rfl
    · rw [hzero j hj, LinearMap.zero_apply]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have : a ⊗ₜ[ℚ] v = a • ((1 : R) ⊗ₜ v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rw [this, map_smul, map_smul, h1]

theorem exists_actOn_eq_of_commute : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
    (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) →
    ∃ y, actOn L.rep (AfP p) y = A := by
  intro p _ D G L A hA
  haveI := D.finLa
  exact exists_actOn_eq L.rep (actQ D) (fun B hB => (L.rep_range B).mpr hB) (AfP p) A hA

end GlobalTheory.LKGeo.CommBC
