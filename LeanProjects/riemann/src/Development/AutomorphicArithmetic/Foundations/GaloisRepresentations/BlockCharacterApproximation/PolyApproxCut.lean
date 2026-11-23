import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

noncomputable section

open Polynomial Finset GlobalTheory.Cong

namespace UpperTheory.Gal.CharacterCongruences

section Approx

variable {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type}

def PolyApproxAt (ε : ℝ) (θ : J → k) (S : Set (J → k)) : Prop :=
  ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

omit [IsUltrametricDist k] in

theorem PolyApproxAt.comp {ε : ℝ} {θ : J → k} {S : Set (J → k)} (h : PolyApproxAt ε θ S) {J' : Type} (f : J' → J) :
    PolyApproxAt ε (θ ∘ f) ((· ∘ f) '' S) := by
  classical
  obtain ⟨s, c, hs, hc⟩ := h
  refine ⟨s.image (· ∘ f), fun z => ∑ η ∈ s.filter (fun η => η ∘ f = z), c η, ?_, fun P => ?_⟩
  · rw [Finset.coe_image]; exact Set.image_mono hs
  · convert hc (MvPolynomial.rename f P) using 2
    rw [MvPolynomial.aeval_rename]
    congr 1
    rw [← Finset.sum_fiberwise_of_maps_to (g := (· ∘ f)) (t := s.image (· ∘ f)) fun η hη => Finset.mem_image_of_mem _ hη]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun η hη => ?_
    rw [MvPolynomial.aeval_rename, (Finset.mem_filter.1 hη).2]

end Approx

section Ring

variable (O : Type) [CommRing O] (l N m : ℕ)

def phi : O[X] := ∑ i ∈ range (l ^ m), X ^ (i * l ^ (N - m))

abbrev abelian₂ : Type := AdjoinRoot (phi O l N m)

def aug : abelian₂ O l N m →+* O ⧸ Ideal.span {(l : O) ^ m} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) 1 (by
    simp only [phi, eval₂_finset_sum, eval₂_X_pow, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.mem_span_singleton_self _)

end Ring

def RingFree : Prop :=
  ∀ (O : Type) [CommRing O] (l N m : ℕ), 0 < l → m ≤ N →
    (phi O l N m).Monic ∧ phi O l N m * (X ^ (l ^ (N - m)) - 1) = X ^ (l ^ N) - 1 ∧
    Module.Free O (abelian₂ O l N m) ∧ Module.Finite O (abelian₂ O l N m) ∧ AdjoinRoot.root (phi O l N m) ^ (l ^ N) = 1

def RingInj : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) →
    ∀ (l N m : ℕ), 0 < l → m ≤ N →
    (∀ ζ : K, aeval ζ (phi O l N m) = 0 ↔ ζ ^ (l ^ N) = 1 ∧ ζ ^ (l ^ (N - m)) ≠ 1) ∧
    ((∃ z : K, IsPrimitiveRoot z (l ^ N)) → ∀ p : O[X],
      (∀ ζ : K, ζ ^ (l ^ N) = 1 → ζ ^ (l ^ (N - m)) ≠ 1 → aeval ζ p = 0) → AdjoinRoot.mk (phi O l N m) p = 0)

abbrev Ch (n : ℕ) : Type := Multiplicative (ZMod n) →* ℂˣ

def Regular : Prop :=
  ∀ (Γ M : Type) [Group Γ] [CommGroup M] (l : ℕ), l.Prime → ∀ (N c e r : ℕ), 0 < e → r * e ≤ l ^ c →
    ∀ (ψ : Γ →* Multiplicative (ZMod (l ^ N))), Function.Surjective ψ →
    ∀ (ξ : Multiplicative (ZMod (l ^ N)) →* M), ξ ^ (l ^ c) ≠ 1 →
    ∀ (ω ω' : Γ →* M) (n n' : ℕ), ω ^ e = 1 → ω' ^ e = 1 → n ≤ r → n' ≤ r → n ≠ n' →
      ω * (ξ.comp ψ) ^ n ≠ ω' * (ξ.comp ψ) ^ n'

def FourierCut : Prop :=
  ∀ (n M q : ℕ), 0 < n → n = M * q → ∃ (s : Finset (Ch n)) (c : Ch n → ℂ), (∀ ξ ∈ s, ξ ^ M ≠ 1) ∧
    ∀ x : Multiplicative (ZMod n), 1 - ∑ ξ ∈ s, c ξ * (ξ x : ℂ) = 0 ∨ 1 - ∑ ξ ∈ s, c ξ * (ξ x : ℂ) = q

def sys {k J : Type} [Field k] (ι : k ≃+* ℂ) {n : ℕ} (η : J → ℂ) (ξ : Ch n) : J ⊕ Multiplicative (ZMod n) → k :=
  Sum.elim (fun j => ι.symm (η j)) fun d => ι.symm (ξ d : ℂ)

def CongAbs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N m : ℕ), m ≤ N →
    ∀ (V X J : Type) [AddCommGroup V] [Module ℂ V] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ),
    (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) →
    ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → (∀ x, ‖ι.symm (ev x v₀)‖ ≤ 1) →
    ∀ (ℓ : X → Multiplicative (ZMod (l ^ N))) (S : Ch (l ^ N) → Set (J → ℂ)),
    (∀ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 → ∃ (d : ℕ) (v : Fin d → V) (η : Fin d → J → ℂ), (∀ i, η i ∈ S ξ) ∧
      (∀ i j, T j (v i) = η i j • v i) ∧ ∀ x, ev x (∑ i, v i) = (ξ (ℓ x) : ℂ) * ev x v₀) →
    PolyApproxAt (‖(l : PadicAlgCl l)‖ ^ m) (sys ι θ (1 : Ch (l ^ N)))
      {z | ∃ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 ∧ ∃ η ∈ S ξ, z = sys ι η ξ}

def ProjAbs : Prop :=
  ∀ (S V : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (t : Finset (Submodule ℂ V)),
    sSupIndep (t : Set (Submodule ℂ V)) → ∀ f : S →ₗ[ℂ] V, (∀ v, f v ∈ sSup (t : Set (Submodule ℂ V))) →
    ∃ F : Submodule ℂ V → S →ₗ[ℂ] V, (∀ U ∈ t, ∀ v, F U v ∈ U) ∧ (∀ v, ∑ U ∈ t, F U v = f v) ∧
      ∀ T : Module.End ℂ V, (∀ U ∈ t, ∀ φ ∈ U, T φ ∈ U) → ∀ v v', T (f v) = f v' → ∀ U ∈ t, T (F U v) = F U v'

end UpperTheory.Gal.CharacterCongruences

end
