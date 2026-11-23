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

namespace GlobalTheory.ChainDesc

theorem dvd_of_map_dvd_of_isIntegral {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B]
    [IsDomain A'] [IsIntegrallyClosed A'] [IsDomain B] [Algebra A A'] [Algebra A B]
    [Algebra.IsIntegral A B] (g : A' →+* B) (hg : Function.Injective g)
    (hc : ∀ a, g (algebraMap A A' a) = algebraMap A B a) (a x : A') (h : g a ∣ g x) : a ∣ x := by
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, zero_dvd_iff] at h
    rw [zero_dvd_iff]
    exact hg (by rw [h, map_zero])
  obtain ⟨b, hb⟩ := h
  letI : Algebra A' B := g.toAlgebra
  haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  have hbi : IsIntegral A' b := (Algebra.IsIntegral.isIntegral (R := A) b).tower_top
  let K := FractionRing A'
  let L := FractionRing B
  have hinj : Function.Injective (algebraMap A' L) := by
    rw [IsScalarTower.algebraMap_eq A' B L]
    exact (IsFractionRing.injective B L).comp hg
  let φ : K →ₐ[A'] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A' L) hinj
  have haK : algebraMap A' K a ≠ 0 := fun h0 => ha (IsFractionRing.injective A' K (by rw [h0, map_zero]))
  have haL : algebraMap A' L a ≠ 0 := fun h0 => ha (hinj (by rw [h0, map_zero]))
  have hφ : φ (algebraMap A' K x / algebraMap A' K a) = algebraMap B L b := by
    rw [map_div₀, φ.commutes, φ.commutes, div_eq_iff haL, IsScalarTower.algebraMap_apply A' B L x,
      IsScalarTower.algebraMap_apply A' B L a, ← map_mul, mul_comm]
    exact congrArg _ hb
  have hi : IsIntegral A' (algebraMap A' K x / algebraMap A' K a) := by
    rw [← isIntegral_algHom_iff φ φ.toRingHom.injective, hφ]
    exact hbi.algebraMap
  obtain ⟨c, hc'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨c, IsFractionRing.injective A' K ?_⟩
  rw [map_mul, hc', mul_div_cancel₀ _ haK]

theorem dvd_of_map_dvd_and_mem_smul_top :
    ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] [IsDomain A'] [IsIntegrallyClosed A'] [IsDomain B] [Algebra A A'] [Algebra A B] [Algebra.IsIntegral A B] (g : A' →+* B), Function.Injective g → (∀ a, g (algebraMap A A' a) = algebraMap A B a) → (∀ a x : A', g a ∣ g x → a ∣ x) ∧ ∀ (N N' : Type) [AddCommGroup N] [Module A N] [Module.Projective A N] [AddCommGroup N'] [Module A' N'] (e : A' ⊗[A] N ≃ₗ[A'] N') (l : N' →ₛₗ[g] B ⊗[A] N), (∀ y, l (e (1 ⊗ₜ y)) = 1 ⊗ₜ y) → ∀ (a : A') (y : N'), l y ∈ g a • (⊤ : Submodule B (B ⊗[A] N)) → y ∈ a • (⊤ : Submodule A' N') := by
  intro A A' B _ _ _ _ _ _ _ _ _ g hg hc
  have h1 : ∀ a x : A', g a ∣ g x → a ∣ x := dvd_of_map_dvd_of_isIntegral g hg hc
  refine ⟨h1, ?_⟩
  intro N N' _ _ _ _ _ e l hl a y hy
  let gA : A' →ₐ[A] B := { g with commutes' := hc }
  let I : Ideal B := Ideal.span {g a}
  let π : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let ψ : A' →ₗ[A] B ⧸ I := π ∘ₗ gA.toLinearMap
  have hex : Function.Exact (LinearMap.mulLeft A a) ψ := by
    intro x
    have : ψ x = 0 ↔ g a ∣ g x := by
      change Ideal.Quotient.mk I (g x) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rw [this]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := h1 a x h
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨g c, by simp⟩
  have hexN := Module.Flat.rTensor_exact N hex
  have hle : ∀ z, l (e z) = gA.toLinearMap.rTensor N z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul c n =>
      have : c ⊗ₜ[A] n = c • ((1 : A') ⊗ₜ[A] n) := by simp [TensorProduct.smul_tmul']
      rw [LinearMap.rTensor_tmul, this, map_smul, map_smulₛₗ, hl, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
  have hπ : ∀ w : B ⊗[A] N, π.rTensor N (g a • w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [smul_add, map_add, hu, hv, add_zero]
    | tmul c n =>
      have : π (g a • c) = 0 := by
        change Ideal.Quotient.mk I (g a * c) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _
      rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, this, TensorProduct.zero_tmul]
  have hmul : ∀ z : A' ⊗[A] N, (LinearMap.mulLeft A a).rTensor N z = a • z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [smul_add, map_add, hu, hv]
    | tmul c n => rw [LinearMap.rTensor_tmul, TensorProduct.smul_tmul']; rfl
  obtain ⟨z, rfl⟩ := e.surjective y
  obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  have hz : ψ.rTensor N z = 0 := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, ← hle, ← hw, hπ]
  obtain ⟨z', hz'⟩ := (hexN z).mp hz
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨e z', trivial, ?_⟩
  rw [← hz', hmul, map_smul]

end GlobalTheory.ChainDesc
