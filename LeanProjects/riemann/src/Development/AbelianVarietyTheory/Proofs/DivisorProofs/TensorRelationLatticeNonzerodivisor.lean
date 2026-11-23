import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc.KerGen

theorem baseChange_injective {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {h : ℕ} {P : Type}
    [AddCommGroup P] [Module A P] [Module.Projective A P] (κ : P →ₗ[A] (Fin h → A)) (π : A)
    (hκ : Function.Injective κ) (hb : baseOf π h ≤ LinearMap.range κ)
    (hπ : algebraMap A R π ∈ nonZeroDivisors R) : Function.Injective (κ.baseChange R) := by
  have hm : ∀ v : Fin h → A, (π • (LinearMap.id : (Fin h → A) →ₗ[A] (Fin h → A))) v ∈ LinearMap.range κ :=
    fun v => hb (Submodule.smul_mem_pointwise_smul v π ⊤ trivial)
  let σ : (Fin h → A) →ₗ[A] P :=
    (LinearEquiv.ofInjective κ hκ).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hm
  have hσ : ∀ v, κ (σ v) = π • v := fun v => by
    have := (LinearEquiv.ofInjective κ hκ).apply_symm_apply (LinearMap.codRestrict _ _ hm v)
    exact congrArg Subtype.val this
  have hσκ : ∀ x, σ (κ x) = π • x := fun x => hκ (by rw [hσ, map_smul])
  have hc : ∀ y : R ⊗[A] P, σ.baseChange R (κ.baseChange R y) = algebraMap A R π • y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, hσκ, algebraMap_smul, TensorProduct.tmul_smul]
    | add a b ha hb => rw [map_add, map_add, ha, hb, smul_add]
  have hr : IsSMulRegular (R ⊗[A] P) (algebraMap A R π) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hπ
  intro a b hab
  apply hr
  show algebraMap A R π • a = algebraMap A R π • b
  rw [← hc, ← hc, hab]

theorem main : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (h : ℕ) (P Q : Type) [AddCommGroup P] [Module A P] [Module.Projective A P] [AddCommGroup Q] [Module A Q] (κ : P →ₗ[A] (Fin h → A)) (t : P →ₗ[A] Q) (π : A), Function.Injective κ → baseOf π h ≤ LinearMap.range κ → algebraMap A R π ∈ nonZeroDivisors R → Function.Surjective t → ∀ (r : ℕ) (x : Fin r → P) (c : Fin r → R), ∑ l, c l ⊗ₜ[A] t (x l) = 0 ↔ ∑ l, c l • piMap (algebraMap A R) (Fin h) (κ (x l)) ∈ Submodule.span R {z | ∃ x₀ : P, t x₀ = 0 ∧ z = piMap (algebraMap A R) (Fin h) (κ x₀)} := by
  intro A R _ _ _ h P Q _ _ _ _ _ κ t π hκ hb hπ ht r x c
  let Φ : R ⊗[A] P →ₗ[R] (Fin h → R) :=
    (TensorProduct.piScalarRight A R R (Fin h)).toLinearMap ∘ₗ κ.baseChange R
  have hΦ : ∀ (a : R) (y : P), Φ (a ⊗ₜ[A] y) = a • piMap (algebraMap A R) (Fin h) (κ y) := fun a y => by
    funext i
    simp [Φ, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective Φ :=
    (TensorProduct.piScalarRight A R R (Fin h)).injective.comp (baseChange_injective κ π hκ hb hπ)
  have hsum : Φ (∑ l, c l ⊗ₜ[A] x l) = ∑ l, c l • piMap (algebraMap A R) (Fin h) (κ (x l)) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun l _ => hΦ _ _
  have hsum' : t.baseChange R (∑ l, c l ⊗ₜ[A] x l) = ∑ l, c l ⊗ₜ[A] t (x l) := by
    rw [map_sum]; rfl
  rw [← hsum, ← hsum']
  generalize (∑ l, c l ⊗ₜ[A] x l) = y
  constructor
  · intro hy
    have hex := lTensor_exact R (LinearMap.exact_subtype_ker_map t) ht
    obtain ⟨z, rfl⟩ := (hex y).1 hy
    clear hy
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      rw [LinearMap.lTensor_tmul, hΦ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.1, w.2, rfl⟩)
    | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  · intro hy
    have hle : Submodule.span R {z | ∃ x₀ : P, t x₀ = 0 ∧ z = piMap (algebraMap A R) (Fin h) (κ x₀)}
        ≤ (LinearMap.ker (t.baseChange R)).map Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x₀, h0, rfl⟩
      refine ⟨1 ⊗ₜ[A] x₀, ?_, by rw [hΦ, one_smul]⟩
      show t.baseChange R (1 ⊗ₜ[A] x₀) = 0
      rw [LinearMap.baseChange_tmul, h0, TensorProduct.tmul_zero]
    obtain ⟨z, hz, hzy⟩ := hle hy
    rw [← hinj hzy]
    exact hz

end GlobalTheory.ChainDesc.KerGen
