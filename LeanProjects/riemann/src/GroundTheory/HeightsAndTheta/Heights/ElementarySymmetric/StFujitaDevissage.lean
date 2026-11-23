import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (𝒩 : Set (K → ℤ)),
    IsNoetherianRing S →
    (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ N ∈ 𝒩, ∀ i : ℕ, 1 ≤ i →
        Subsingleton (KH.cechHc ι (KH.quotPart S P) (e + ((fun _ => (m : ℤ)) + N)) i)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N ∈ 𝒩, ∀ i : ℕ, 1 ≤ i →
        Subsingleton (KH.cechHc ι 𝓜 (e + ((fun _ => (m : ℤ)) + N)) i)

namespace FujitaDevissage

theorem cechHc_point_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver ℚ pointIdx) M] [Module ℚ M]
    [IsScalarTower ℚ (MRingOver ℚ pointIdx) M] (𝓜 : (Unit → ℤ) → Submodule ℚ M) (d : Unit → ℤ) (i : ℕ)
    (hi : 1 ≤ i) : Subsingleton (KH.cechHc pointIdx 𝓜 d i) := by
  have hempty : IsEmpty (KH.Cell Unit pointIdx i) := by
    refine ⟨fun I => ?_⟩
    have h : ∑ k, ((I.1 k).card - 1) = 0 :=
      Finset.sum_eq_zero fun k _ => Nat.sub_eq_zero_of_le (Finset.card_le_one_of_subsingleton _)
    have := I.2.2
    omega
  have : Subsingleton (KH.CechC ℚ pointIdx M i) := ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

end FujitaDevissage

theorem FujitaDevissage.hyps_inhabited :
    IsNoetherianRing ℚ ∧
      (∀ P : Ideal (MRingOver ℚ pointIdx), IsMultiProjPrime P → (⊥ : Ideal (MRingOver ℚ pointIdx)) ≤ P →
        ∀ e : Unit → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N ∈ (Set.univ : Set (Unit → ℤ)), ∀ i : ℕ, 1 ≤ i →
          Subsingleton (KH.cechHc pointIdx (KH.quotPart ℚ P) (e + ((fun _ => (m : ℤ)) + N)) i)) ∧
      IsMultiProjPrime (⊥ : Ideal (MRingOver ℚ pointIdx)) ∧
      Module.Finite (MRingOver ℚ pointIdx) (MRingOver ℚ pointIdx ⧸ (⊥ : Ideal (MRingOver ℚ pointIdx))) ∧
      KH.IsMGraded ℚ pointIdx (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ pointIdx))) ∧
      (⊥ : Ideal (MRingOver ℚ pointIdx)) ≤
        Module.annihilator (MRingOver ℚ pointIdx) (MRingOver ℚ pointIdx ⧸ (⊥ : Ideal (MRingOver ℚ pointIdx))) :=
  ⟨inferInstance,
    fun _ _ _ _ => ⟨0, fun _ _ _ _ i hi => FujitaDevissage.cechHc_point_subsingleton _ _ i hi⟩,
    bot_isMultiProjPrime_point, inferInstance,
    QuotPartGraded.proof ℚ Unit pointIdx ⊥ bot_isMultiProjPrime_point.2.1, le_annihilator_quotient _⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
