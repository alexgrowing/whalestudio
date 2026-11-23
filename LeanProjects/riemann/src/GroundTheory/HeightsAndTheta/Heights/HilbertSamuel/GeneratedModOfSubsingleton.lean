import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I

def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)

section Point

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem cell_zero_subsingleton : Subsingleton (KH.Cell K ι 0) :=
  ⟨fun I J => Subtype.ext (funext fun k => (I.2.1 k).eq_univ.trans (J.2.1 k).eq_univ.symm)⟩

omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in

theorem cell_succ_isEmpty (n : ℕ) : IsEmpty (KH.Cell K ι (n + 1)) := by
  refine ⟨fun I => ?_⟩
  have h : ∑ k, ((I.1 k).card - 1) = 0 :=
    Finset.sum_eq_zero fun k _ => Nat.sub_eq_zero_of_le (Finset.card_le_one_of_subsingleton _)
  have := I.2.2
  omega

theorem cechHc_one_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) := by
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

omit [Fintype K] [∀ k, Subsingleton (ι k)] in

theorem isMultiHomog_one_zero : IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]

theorem generatedMod_of_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    GeneratedMod S ι 𝓜 d := by
  have := cell_zero_subsingleton (K := K) (ι := ι)
  have := cell_succ_isEmpty (K := K) (ι := ι) 0
  intro I x hx
  let z : KH.CechC S ι M 0 := fun J => (Subsingleton.elim I J ▸ x : LocalizedModule (KH.cellMon S J.1) M)
  refine ⟨1, 0, 1, fun _ => 1, fun _ => z, Submonoid.one_mem _, isMultiHomog_one_zero,
    fun _ => isMultiHomog_one_zero, fun _ => ⟨?_, ?_⟩, ?_⟩
  · intro J _
    obtain rfl : I = J := Subsingleton.elim _ _
    exact hx
  · show KH.cechD S ι M 0 z = 0
    exact funext fun J => (IsEmpty.false J).elim
  · simp only [one_smul, Finset.univ_unique, Finset.sum_singleton]
    rfl

theorem h1GenAmple_of_subsingleton (V : Ideal (MRingOver S ι)) (N : K → ℤ) : H1GenAmple S V N := by
  intro M _ _ _ _ 𝓜 _ _ _ e
  exact ⟨0, fun c _ => ⟨cechHc_one_subsingleton 𝓜 _, generatedMod_of_subsingleton 𝓜 _⟩⟩

end Point

abbrev pointIdx : Unit → Type := fun _ => Fin 1

theorem bot_isMultiProjPrime_point : IsMultiProjPrime (⊥ : Ideal (MRingOver ℚ pointIdx)) :=
  ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, by simp [X_ne_zero]⟩⟩

theorem h1GenAmple_projectivePoint : H1GenAmple ℚ (⊥ : Ideal (MRingOver ℚ pointIdx)) 0 :=
  h1GenAmple_of_subsingleton _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
