import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSMulRegularCokerDualMapOfExactFibres

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function

namespace GlobalTheory
namespace DualCokernel

theorem extZero_of_isRegularLocalRing (R : Type) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hg : ringKrullDim R = g) (j : ℕ) (hj : j < g) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ hreg j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    exact h ▸ Ideal.subset_span hr

end DualCokernel

open DualCokernel in

theorem exact_dualMap_of_exact_fibres_of_isRegularLocalRing :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by
  intro A _ _ g hg C hF ⟨n, hn⟩ hex
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hDext : ∀ i, ∀ j < g, ExtZero (R := A) (Module.Dual A (C.X i)) j := fun i j hj =>
    FiniteLengthComplex.subsingleton_ext_free _ j (extZero_of_isRegularLocalRing A g hg j hj) _
  have hdd : ∀ i j k f, (C.d i j).hom.dualMap ((C.d j k).hom.dualMap f) = 0 := fun i j k f => by
    ext x
    simp [d_d_apply]

  have hloc : ∀ i, ∀ p : Ideal A, p.IsPrime → p ≠ maximalIdeal A → ∃ s, s ∉ p ∧
      ∀ f, (C.d (i - 1) i).hom.dualMap f = 0 →
        s • f ∈ LinearMap.range (C.d i (i + 1)).hom.dualMap := by
    intro i p hp hpm
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨p, hp⟩
    obtain ⟨t, ht, k₀, k₁, hk⟩ := exists_homotopy C hF n hn p
      (fun j => exact_fibre C p φ hφ j (hK j (Or.inl hpm))) i
    refine ⟨t, ht, fun f hf => ⟨k₁.dualMap f, LinearMap.ext fun x => ?_⟩⟩
    have h1 : f ((C.d (i - 1) i).hom (k₀ x)) = 0 := LinearMap.congr_fun hf (k₀ x)
    have h2 := congrArg f (hk x)
    rw [map_add, h1, zero_add, map_smul] at h2
    exact h2

  have hhom : ∀ i, g ≤ i → ∃ (s : C.X (i + 1) →ₗ[A] C.X i) (t : C.X (i + 1 + 1) →ₗ[A] C.X (i + 1)),
      ∀ x, (C.d i (i + 1)).hom (s x) + t ((C.d (i + 1) (i + 1 + 1)).hom x) = x := by
    intro i hi
    obtain ⟨K, _, φ, hφ, hK⟩ := hex ⟨maximalIdeal A, inferInstance⟩
    obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField
      (f := (C.d i (i + 1)).hom) (g := (C.d (i + 1) (i + 1 + 1)).hom)
      (LinearMap.ext (d_d_apply C _ _ _)) fun m hm' => by
        exact exact_fibre C m φ (hφ.trans (eq_maximalIdeal hm').symm) (i + 1)
          (hK _ (Or.inr (by omega)))
    exact ⟨s, t, fun x => by simpa using LinearMap.congr_fun hst x⟩

  have hstep : ∀ i, ExtZero (R := A)
      (Module.Dual A (C.X (i + 1)) ⧸ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap) 0 →
      LinearMap.ker (C.d i (i + 1)).hom.dualMap ≤
        LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap := by
    intro i h0 f hf
    refine (Submodule.Quotient.mk_eq_zero _).1 (eq_zero_of_extZero h0 _ fun p hp hpm => ?_)
    obtain ⟨s, hs, hs'⟩ := hloc (i + 1) p hp hpm
    exact ⟨s, hs, (Submodule.Quotient.mk_eq_zero _).2 (hs' f hf)⟩
  have hle : ∀ i, LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ≤
      LinearMap.ker (C.d i (i + 1)).hom.dualMap := by
    rintro i _ ⟨y, rfl⟩
    exact hdd _ _ _ y
  have key : ∀ k i, i + k = g → ∀ j < i, ExtZero (R := A)
      (Module.Dual A (C.X i) ⧸ LinearMap.range (C.d i (i + 1)).hom.dualMap) j := by
    intro k
    induction k with
    | zero =>
      rintro i rfl
      obtain ⟨s, t, hst⟩ := hhom i le_rfl
      have hds : ∀ x, (C.d i (i + 1)).hom (s ((C.d i (i + 1)).hom x)) = (C.d i (i + 1)).hom x :=
        fun x => by simpa [d_d_apply] using hst ((C.d i (i + 1)).hom x)
      let ι := (LinearMap.range (C.d i (i + 1)).hom.dualMap).liftQ
        (LinearMap.id - (C.d i (i + 1)).hom.dualMap ∘ₗ s.dualMap) (by
          rintro _ ⟨f, rfl⟩
          ext x
          simp [hds])
      have hι : (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ ∘ₗ ι = LinearMap.id := by
        refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
        refine (Submodule.Quotient.eq _).2 ⟨-s.dualMap f, ?_⟩
        simp [ι]
      exact fun j hj => extZero_retract ι _ hι j (hDext i j hj)
    | succ k ih =>
      intro i hi j hj
      have h := ih (i + 1) (by omega)
      exact extZero_coker ((LinearMap.range _).liftQ _ (hle i))
        (LinearMap.range (C.d i (i + 1)).hom.dualMap).mkQ
        (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (hstep i (h 0 (by omega)))))
        (Submodule.mkQ_surjective _)
        (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]) j
        (h _ (by omega)) (hDext i j (by omega))
  intro i
  refine LinearMap.exact_iff.2 (le_antisymm ?_ (hle i))
  rcases lt_or_ge i g with hi | hi
  · exact hstep i (key (g - (i + 1)) (i + 1) (by omega) 0 (by omega))
  · intro f hf
    obtain ⟨s, t, hst⟩ := hhom i hi
    refine ⟨t.dualMap f, LinearMap.ext fun x => ?_⟩
    have h1 : f ((C.d i (i + 1)).hom (s x)) = 0 := LinearMap.congr_fun hf (s x)
    have h2 := congrArg f (hst x)
    rw [map_add, h1, zero_add] at h2
    exact h2

end GlobalTheory
