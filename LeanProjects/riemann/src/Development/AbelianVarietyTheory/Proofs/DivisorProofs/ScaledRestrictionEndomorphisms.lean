import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.DivLin

theorem inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK (O := O) K H) := by
  have hf : Function.Injective (Algebra.linearMap O K) := IsFractionRing.injective O K
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K) hf
  have e : (inK K H : H →ₗ[O] K ⊗[O] H) =
      ((Algebra.linearMap O K).rTensor H) ∘ₗ (TensorProduct.lid O H).symm.toLinearMap := by
    ext h; simp [inK]
  rw [e]
  exact h2.comp (TensorProduct.lid O H).symm.injective

section K

variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]

theorem algebraMap_bilin (B : LinearMap.BilinForm O H) (x y : H) :
    algebraMap O K (B x y) = B.baseChange K (inK K H x) (inK K H y) := by
  simp [inK, Algebra.algebraMap_eq_smul_one]

theorem inK_apply_end (f : Module.End O H) (h : H) : inK K H (f h) = f.baseChange K (inK K H h) := by
  simp [inK]

variable [Module.Free O H]

theorem restr_mul_eq_zero {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : N * N' = 0) : M * M' = 0 := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply, LinearMap.zero_apply, map_zero]
  rw [hM, hM', map_smul, ← Module.End.mul_apply N N', h]; simp

theorem restr_commute {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (f : Module.End O H)
    (hM : IsScaledRestr D N M) (h : Commute N (f.baseChange K)) : Commute M f := by
  ext x; apply inK_injective_of_free (O := O) K H
  simp only [Module.End.mul_apply]
  rw [hM, inK_apply_end, inK_apply_end, hM, map_smul]
  congr 1
  exact LinearMap.congr_fun h.eq _

theorem restr_skew {D : O} {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (h : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (x y : H) :
    B (M x) y + B x (M y) = 0 := by
  apply IsFractionRing.injective O K
  rw [map_add, algebraMap_bilin, algebraMap_bilin, hM, hM, map_zero]
  simp only [map_smul, LinearMap.smul_apply]
  rw [← smul_add, h, smul_zero]

theorem restr_iso {D : O} {N N' : Module.End K (K ⊗[O] H)} {M M' : Module.End O H} (B : LinearMap.BilinForm O H)
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (h : ∀ x y, B.baseChange K (N x) (N' y) = 0) (x y : H) :
    B (M x) (M' y) = 0 := by
  apply IsFractionRing.injective O K
  rw [algebraMap_bilin, hM, hM', map_zero]
  simp only [map_smul, LinearMap.smul_apply, h, smul_zero]

end K

section R

variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]

theorem baseChange_mul' (f g : Module.End O H) : (f * g).baseChange R = f.baseChange R * g.baseChange R := by
  ext x
  simp

theorem nilPart_eq (l : ℕ) (M : I → Module.End O H) (t : I → R) :
    nilPart l M R t = (lPrime l : R) • ∑ i, t i • (M i).baseChange R := rfl

theorem nilPart_sq {M : I → Module.End O H} (hMM : ∀ i j, M i * M j = 0) (l : ℕ) (t : I → R) :
    nilPart l M R t * nilPart l M R t = 0 := by
  have hSS : (∑ i, t i • (M i).baseChange R) * (∑ i, t i • (M i).baseChange R) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ← baseChange_mul', hMM,
      LinearMap.baseChange_zero, smul_zero, Finset.sum_const_zero]
  rw [nilPart_eq, smul_mul_smul_comm, hSS, smul_zero]

theorem nilPart_commute {M : I → Module.End O H} (f : Module.End O H) (hM : ∀ i, Commute (M i) f) (l : ℕ) (t : I → R) :
    Commute (nilPart l M R t) (f.baseChange R) := by
  rw [nilPart_eq]
  refine Commute.smul_left ?_ _
  refine Commute.sum_left _ _ _ fun i _ => Commute.smul_left ?_ _
  show _ * _ = _ * _
  rw [← baseChange_mul', ← baseChange_mul', (hM i).eq]

theorem baseChange_skew_iso (B : LinearMap.BilinForm O H) {M M' : Module.End O H}
    (hskew : ∀ x y, B (M x) y + B x (M y) = 0) (hiso : ∀ x y, B (M x) (M' y) = 0) (x y : R ⊗[O] H) :
    B.baseChange R (M.baseChange R x) y + B.baseChange R x (M.baseChange R y) = 0 ∧
      B.baseChange R (M.baseChange R x) (M'.baseChange R y) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, LinearMap.add_apply]
    exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
  | tmul c₀ a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add]
      exact ⟨by linear_combination h₁.1 + h₂.1, by linear_combination h₁.2 + h₂.2⟩
    | tmul c' b =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
      rw [← add_smul, hskew, hiso]
      simp

theorem nilPart_skew (B : LinearMap.BilinForm O H) {M : I → Module.End O H}
    (hskew : ∀ i x y, B (M i x) y + B x (M i y) = 0) (hiso : ∀ i j x y, B (M i x) (M j y) = 0) (l : ℕ) (t : I → R)
    (x y : R ⊗[O] H) :
    B.baseChange R (nilPart l M R t x) y + B.baseChange R x (nilPart l M R t y) = 0 := by
  simp only [nilPart_eq, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp only [← smul_add]
  rw [Finset.sum_eq_zero fun i _ => by rw [(baseChange_skew_iso R B (hskew i) (hiso i i) x y).1, smul_zero], smul_zero]

theorem nilPart_iso (B : LinearMap.BilinForm O H) {M : I → Module.End O H}
    (hskew : ∀ i x y, B (M i x) y + B x (M i y) = 0) (hiso : ∀ i j x y, B (M i x) (M j y) = 0) (l : ℕ) (t : I → R)
    (x y : R ⊗[O] H) :
    B.baseChange R (nilPart l M R t x) (nilPart l M R t y) = 0 := by
  simp only [nilPart_eq, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    (baseChange_skew_iso R B (hskew _) (hiso _ _) _ _).2, smul_zero, Finset.sum_const_zero]

end R

end GlobalTheory.DivLin

namespace GlobalTheory.DivLin

theorem nilPart_claims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (O : Type) [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H], Module.Free O H → ∀ (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) (I : Type) [Fintype I] (N : I → Module.End K (K ⊗[O] H)) (D : O) (M : I → Module.End O H), (∀ i, IsScaledRestr D (N i) (M i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) → (∀ i j, N i * N j = 0) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) → (∀ i j x y, B.baseChange K (N i x) (N j y) = 0) → ∀ (l : ℕ) (R : Type) [CommRing R] [Algebra O R] (t : I → R), (∀ x : R ⊗[O] H, ∃ y : R ⊗[O] H, (1 + nilPart l M R t) x = x + (lPrime l : R) • y) ∧ ((1 + nilPart l M R t) * (1 - nilPart l M R t) = 1 ∧ (1 - nilPart l M R t) * (1 + nilPart l M R t) = 1) ∧ (∀ a : OF E, Commute (1 + nilPart l M R t) ((ρ (ofF c a)).baseChange R)) ∧ ∀ x y : R ⊗[O] H, B.baseChange R ((1 + nilPart l M R t) x) ((1 + nilPart l M R t) y) = B.baseChange R x y := by
  intro E _ _ _ c O _ _ K _ _ _ H _ _ hfree ρ B I _ N D M hMN hcomm hNN hskew hiso l R _ _ t
  haveI := hfree
  have hMM : ∀ i j, M i * M j = 0 := fun i j => restr_mul_eq_zero (hMN i) (hMN j) (hNN i j)
  have hMρ : ∀ (a : OF E) i, Commute (M i) (ρ (ofF c a)) := fun a i => restr_commute _ (hMN i) (hcomm i a)
  have hMskew : ∀ i x y, B (M i x) y + B x (M i y) = 0 := fun i => restr_skew B (hMN i) (hskew i)
  have hMiso : ∀ i j x y, B (M i x) (M j y) = 0 := fun i j => restr_iso B (hMN i) (hMN j) (hiso i j)
  have hnn := nilPart_sq R hMM l t
  refine ⟨fun x => ⟨(∑ i, t i • (M i).baseChange R) x, ?_⟩, ⟨?_, ?_⟩, fun a => ?_, fun x y => ?_⟩
  · rw [LinearMap.add_apply, Module.End.one_apply, nilPart_eq, LinearMap.smul_apply]
  · rw [add_mul, one_mul, mul_sub, mul_one, hnn]; abel
  · rw [sub_mul, one_mul, mul_add, mul_one, hnn]; abel
  · exact (Commute.one_left _).add_left (nilPart_commute R _ (hMρ a) l t)
  · simp only [LinearMap.add_apply, Module.End.one_apply, map_add]
    linear_combination nilPart_skew R B hMskew hMiso l t x y + nilPart_iso R B hMskew hMiso l t x y

end GlobalTheory.DivLin
