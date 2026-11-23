import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent

theorem sum_sum_mul_of_split {K : Type} [CommRing K] {h n : ℕ} (G S : Fin n → Fin h → K)
    (hGS : ∀ i i' : Fin h, ∑ k, G k i * S k i' = if i = i' then 1 else 0) (w : Fin h → K) (i : Fin h) :
    ∑ k, (∑ i', S k i' * w i') * G k i = w i := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i', ∑ k, S k i' * w i' * G k i = w i' * (if i = i' then 1 else 0) := by
    intro i'
    rw [← hGS i i', Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [this]
  simp [mul_ite]

variable {X : Scheme.{0}} [IsIntegral X] {K' : IntermediateField X.functionField (Kbar X)}
    {U : AffOp X} {h n : ℕ} {L : Submodule U.Bp (Fin h → U.Bp)} {g : Fin n → Fin h → U.Bp}
    {S : Fin n → Fin h → Kbar X}

theorem Splits.mem_span (hS : Splits U L g S) {v : Fin h → U.Bp} (hv : v ∈ L) :
    v ∈ Submodule.span U.Bp (Set.range g) := by
  obtain ⟨-, hGS, hSL⟩ := hS
  choose r hr using hSL v hv
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨r, ?_⟩
  funext i
  apply Subtype.ext
  have := sum_sum_mul_of_split (fun k i => (g k i : Kbar X)) S hGS (fun i => (v i : Kbar X)) i
  simp only [← hr] at this
  rw [← this]
  simp

theorem Splits.finite_projective (hS : Splits U L g S) (hgK : ∀ k i, (g k i : Kbar X) ∈ K')
    (hSK : ∀ k i, S k i ∈ K') :
    Module.Finite (ringOver K' U) (descMod K' U L) ∧ Module.Projective (ringOver K' U) (descMod K' U L) := by
  obtain ⟨hgL, hGS, hSL⟩ := hS
  have key := sum_sum_mul_of_split (fun k i => (g k i : Kbar X)) S hGS
  have hmem : ∀ v : Fin h → U.Bp, v ∈ L → ∀ k,
      (∑ i, S k i * (v i : Kbar X)) ∈ integralClosure Γ(X, U.1) (Kbar X) := by
    intro v hv k
    obtain ⟨r, hr⟩ := hSL v hv k
    rw [← hr]; exact r.2
  have hK : ∀ a : Fin h → ringOver K' U, ∀ k, (∑ i, S k i * ((a i : U.Bp) : Kbar X)) ∈ K' := fun a k =>
    K'.sum_mem fun i _ => K'.mul_mem (hSK k i) (mem_ringOver.1 (a i).2)
  let σ : descMod K' U L →ₗ[ringOver K' U] (Fin n → ringOver K' U) :=
    { toFun := fun a k => ⟨⟨∑ i, S k i * ((a.1 i : U.Bp) : Kbar X), hmem _ a.2 k⟩, hK a.1 k⟩
      map_add' := by
        intro a b; funext k
        apply Subtype.ext; apply Subtype.ext
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; funext k
        apply Subtype.ext; apply Subtype.ext
        simp [Finset.mul_sum, mul_left_comm] }
  let gA : Fin n → descMod K' U L := fun k => ⟨fun i => ⟨g k i, hgK k i⟩, hgL k⟩
  let π : (Fin n → ringOver K' U) →ₗ[ringOver K' U] descMod K' U L :=
    ∑ k, (LinearMap.proj k : (Fin n → ringOver K' U) →ₗ[ringOver K' U] ringOver K' U).smulRight (gA k)
  have hπ : ∀ c i, ((((π c : descMod K' U L) : Fin h → ringOver K' U) i : U.Bp) : Kbar X)
      = ∑ k, ((c k : U.Bp) : Kbar X) * (g k i : Kbar X) := by
    intro c i
    simp [π, gA]
  have hπσ : π.comp σ = LinearMap.id := by
    apply LinearMap.ext; intro a
    apply Subtype.ext; funext i; apply Subtype.ext; apply Subtype.ext
    rw [LinearMap.comp_apply, hπ]
    exact key _ i
  exact ⟨Module.Finite.of_surjective π (fun a => ⟨σ a, by rw [← LinearMap.comp_apply, hπσ]; rfl⟩),
    Module.Projective.of_split σ π hπσ⟩

theorem isDescended_of_splits : ∀ (X : Scheme.{0}) [IsIntegral X] (K' : IntermediateField X.functionField (Kbar X))
    (U : AffOp X) (h n : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (g : Fin n → Fin h → U.Bp)
    (S : Fin n → Fin h → Kbar X), Splits U L g S → (∀ k i, (g k i : Kbar X) ∈ K') → (∀ k i, S k i ∈ K') →
    IsDescended K' U L := by
  intro X _ K' U h n L g S hS hgK hSK
  obtain ⟨h1, h2⟩ := hS.finite_projective hgK hSK
  refine ⟨h1, h2, le_antisymm (fun v hv => Submodule.span_mono ?_ (hS.mem_span hv)) (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨fun i => ⟨g k i, hgK k i⟩, hS.1 k, rfl⟩
  · rintro x ⟨a, ha, rfl⟩
    exact ha

end GlobalTheory.BplusDescent
