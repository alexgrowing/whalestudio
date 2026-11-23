import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftCommLTensorNatural
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProductStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock.AmiExact

theorem pf_punit (p : ℕ) : Pf p PUnit :=
  ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨b, Subsingleton.elim _ _⟩⟩⟩

theorem tensor_punit_eq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    (w : C ⊗[A] PUnit) : w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => rfl
  | tmul c u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem almost_injective {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K₀ : Type) [CommRing K₀] [Algebra A K₀] (hK : Pf p K₀)
    (z : K₀) (hz : (1 : B) ⊗ₜ[A] z = 0) (k : ℕ) : r k • z = 0 := by
  have good : Good p r (0 : PUnit →ₗ[A] K₀) := by
    intro C _ _ _ w _ k
    exact ⟨0, (tensor_punit_eq_zero _).trans (tensor_punit_eq_zero _).symm⟩
  have h := hCov PUnit K₀ (pf_punit p) hK 0 good z
    ⟨0, by rw [map_zero, hz]⟩ k
  simpa using h

theorem ker_zero {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n)) (h0 : ∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z)
    (z : K 0) (hz : d 0 z = 0) (k : ℕ) : r k • z = 0 :=
  almost_injective hCov (K 0) (hK 0) z (by rw [← h0, hz, map_zero]) k

theorem exact_of_good {p : ℕ} {A : Type} [CommRing A] {B : Type} [CommRing B] [Algebra A B]
    {r : ℕ → A} (hCov : Cov p r B) (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n)
    (hK : ∀ n, Pf p (K n))
    (hS : ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z)
    (n : ℕ) (hG : Good p r (d n)) (z : K (n + 1)) (hz : d (n + 1) z = 0) (k : ℕ) :
    r k • z ∈ LinearMap.range (d n) :=
  hCov (K n) (K (n + 1)) (hK n) (hK (n + 1)) (d n) hG z
    ⟨H n z, by simpa [hz] using hS n z⟩ k

theorem lTensor_sq_zero {A C : Type} [CommRing A] [AddCommGroup C] [Module A C]
    {K : ℕ → Type} [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)]
    (d : ∀ n, K n →ₗ[A] K (n + 1)) (dd : ∀ n z, d (n + 1) (d n z) = 0)
    (n : ℕ) (z : C ⊗[A] K n) : (d (n + 1)).lTensor C ((d n).lTensor C z) = 0 := by
  have h : d (n + 1) ∘ₗ d n = 0 := LinearMap.ext (dd n)
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

theorem exact_succ {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {B : Type} [CommRing B]
    [Algebra A B] {r : ℕ → A} (hA : Pf p A) (hCov : Cov p r B) (n : ℕ) :
    ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
      (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n),
      (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) →
      ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧
        ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) →
      ∀ z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  induction n with
  | zero =>
    intro K _ _ d H hK _ hH
    refine exact_of_good hCov K d H hK hH.2 0 ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', _⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    have hz : r k • w = 0 :=
      ker_zero hCov (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
        (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n)) h0' w hw k
    rw [hz]
    exact zero_mem _
  | succ n ih =>
    intro K _ _ d H hK dd hH
    refine exact_of_good hCov K d H hK hH.2 (n + 1) ?_
    intro C _ _ hC w hw k
    obtain ⟨H₁, h0', hS'⟩ := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor A B C K d H hH
    obtain ⟨v, hv⟩ := ih (fun n => C ⊗[A] K n) (fun n => (d n).lTensor C) H₁
      (fun n => GlobalTheory.T.perfect_tensor_product p A C (K n) hA hC (hK n))
      (fun n z => lTensor_sq_zero d dd n z) ⟨h0', hS'⟩ w hw k
    refine ⟨((d n).codRestrict (LinearMap.ker (d (n + 1))) (fun z => dd n z)).lTensor C v, ?_⟩
    rw [← hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl

theorem exact_of_contraction :
    ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := by
  intro p _ A _ B _ _ r hA hCov K _ _ d H hK dd hH
  exact ⟨fun z hz k => ker_zero hCov K d H hK hH.1 z hz k,
    fun n z hz k => exact_succ hA hCov n K d H hK dd hH z hz k⟩

end GlobalTheory.CompanionTheory.Dblock.AmiExact
