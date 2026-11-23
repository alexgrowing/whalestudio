import Mathlib
import Formalism.PeriodIntegrals.FockRBlock

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

def embS (K : Type) [CommRing K] {n' k : ℕ} (t : Fin n') :
    MvPolynomial (Fin k) K →ₐ[K] MvPolynomial (Fin n' × Fin k) K :=
  rename fun c => (t, c)

def liftW {n' k : ℕ} (t : Fin n') (l : List (Fin k × Fin k)) : List (Fin n' × (Fin k × Fin k)) :=
  l.map fun y => (t, y)

def concatW {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) : List (Fin n' × (Fin k × Fin k)) :=
  (List.finRange n').flatMap fun t => liftW t (w t)

def partS {n' k : ℕ} (μ : Fin n' × Fin k →₀ ℕ) (t : Fin n') : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c => μ (t, c)

def WordOK {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ) (l : List (Fin n' × (Fin k × Fin k))) : Prop :=
  (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c

def combo {K : Type} [CommRing K] {n' k : ℕ} (f : List (Fin n' × (Fin k × Fin k)) →₀ K)
    (G : MvPolynomial (Fin n' × Fin k) K) : MvPolynomial (Fin n' × Fin k) K :=
  f.sum fun l a => a • opWord l G

def Ok (K : Type) [Field K] (n' m : ℕ) (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (c : ℕ)
    (β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) : Prop :=
  ∃ f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K, (∀ l ∈ f.support, WordOK TT c l) ∧
    ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
      fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (combo f G)) (Th0 K m vec H)

def StepDeg : Prop :=
  ∀ (K : Type) [Field K] (n' k : ℕ) (d : Fin n' → ℕ) (l : List (Fin n' × (Fin k × Fin k))),
    ∀ G ∈ Pol K (ι := Fin n') k d, opWord l G ∈ Pol K (ι := Fin n') k d

def StepLift : Prop :=
  ∀ (K : Type) [CommRing K] (n' k : ℕ) (w : Fin n' → List (Fin k × Fin k)) (F : Fin n' → MvPolynomial (Fin k) K),
    opWord (concatW w) (∏ t, embS K t (F t)) = ∏ t, embS K t (word1 (w t) (F t))

def StepMonoFactor : Prop :=
  ∀ (K : Type) [CommRing K] (n' k : ℕ) (μ : Fin n' × Fin k →₀ ℕ),
    monomial μ (1 : K) = ∏ t, embS K t (monomial (partS μ t) (1 : K))

def StepPure : Prop :=
  FockRBlock → OnePos →
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n'))
    (d : Fin n' → ℕ) (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) →
    (∀ t, t ∉ TT → ν t = 0) →
    ∀ B S : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∀ t, B t ∈ dualWeyl K (m + 1) (m + 1) (ν t)) → (∀ t, S t ∈ dualWeyl K (m + 1) (m + 1) (ν t)) →
      Ok K n' m vec TT d c (∏ t, blockEmb K t (B t)) (∏ t, blockEmb K t (S t))

def StepSpan : Prop :=
  ∀ (K : Type) [Field K] (n' m : ℕ) (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (c : ℕ)
    (M : Fin n' → Submodule K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)),
    (∀ B S : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, B t ∈ M t) → (∀ t, S t ∈ M t) →
      Ok K n' m vec TT d c (∏ t, blockEmb K t (B t)) (∏ t, blockEmb K t (S t))) →
    ∀ β ∈ tensorLat K K M, ∀ s ∈ tensorLat K K M, Ok K n' m vec TT d c β s

theorem tenOp_of_steps (hD : StepDeg) (hP : StepPure) (hS : StepSpan) : PI.TenOp := by
  intro hFP hSB K _ _ n' m hm vec TT d c ν hν hc h0 β hβ s hs
  obtain ⟨f, hf, heq⟩ := hS K n' m vec TT d c (fun t => PI.TO.dualWeyl K (m + 1) (m + 1) (ν t))
    (fun B S hB hS' => hP hFP hSB K n' m hm vec TT d c ν hν hc h0 B S hB hS') β hβ s hs
  have hsum : ∀ G, (∑ l ∈ f.support, f l • PI.TO.opWord l G) = combo f G :=
    fun G => rfl
  refine ⟨f.support, f, hf, fun G hG => ⟨?_, fun H hH => ?_⟩⟩
  · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hD K n' (m + 1) d l G hG)
  · rw [hsum]
    exact heq G hG H hH

end PI.TOW
