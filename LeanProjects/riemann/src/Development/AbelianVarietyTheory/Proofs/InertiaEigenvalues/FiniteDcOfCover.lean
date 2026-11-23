import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DoubleCosetSetoidRelIffMem

noncomputable section

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

def dcSetoid (Γ K : Subgroup G) : Setoid G := GlobalTheory.DoubleCosetSetoid.doubleCosetSetoid Γ K

abbrev DC (Γ K : Subgroup G) : Type _ := Quotient (dcSetoid Γ K)

def stabCard (Γ K : Subgroup G) (t : G) : ℕ := Nat.card {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}

def mass (Γ K : Subgroup G) : ℚ := ∑ᶠ c : DC Γ K, ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹

theorem finite_dc_of_le {Γ W K : Subgroup G} (hWK : W ≤ K) [Finite (DC Γ W)] : Finite (DC Γ K) := by
  let f : DC Γ W → DC Γ K := Quotient.map' (s₁ := dcSetoid Γ W) (s₂ := dcSetoid Γ K) id (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, e⟩ := hab
    exact ⟨γ, hγ, κ, hWK hκ, e⟩)
  refine Finite.of_surjective f ?_
  rintro ⟨x⟩
  exact ⟨Quotient.mk'' x, rfl⟩

theorem finite_dc_of_cover {Γ K : Subgroup G} (hT : ∃ T : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ t ∈ T, ∃ κ ∈ K, g = γ * t * κ) :
    Finite (DC Γ K) := by
  obtain ⟨T, hT⟩ := hT
  refine Finite.of_surjective (fun t : T => (Quotient.mk'' (t : G) : DC Γ K)) ?_
  rintro ⟨g⟩
  obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g
  refine ⟨⟨t, ht⟩, Quotient.sound' ⟨γ, hγ, κ, hκ, e⟩⟩

theorem stabCard_pos {Γ K : Subgroup G} (t : G) (h : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    0 < stabCard Γ K t := by
  haveI := h
  haveI : Nonempty {γ : Γ // t⁻¹ * (γ : G) * t ∈ K} := ⟨⟨1, by simp [K.one_mem]⟩⟩
  exact Nat.card_pos

theorem mass_pos {Γ K : Subgroup G} [Finite (DC Γ K)]
    (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) : 0 < mass Γ K := by
  haveI := Fintype.ofFinite (DC Γ K)
  rw [mass, finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (DC Γ K)).Nonempty := ⟨Quotient.mk'' 1, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun c _ => ?_) hne
  have := stabCard_pos c.out (hfin c.out)
  positivity

end GlobalTheory.UnimodMass

namespace GlobalTheory.UnimodMass

variable {G : Type*} [Group G]

theorem stabCard_eq {Γ K : Subgroup G} {t t' : G} (hr : (dcSetoid Γ K) t t') :
    stabCard Γ K t' = stabCard Γ K t := by
  obtain ⟨γ, hγ, κ, hκ, rfl⟩ := hr
  unfold stabCard
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨γ⁻¹ * (x.1 : G) * γ, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) x.1.2) hγ⟩, ?_⟩
      invFun := fun x => ⟨⟨γ * (x.1 : G) * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ x.1.2) (Γ.inv_mem hγ)⟩, ?_⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  · have := K.mul_mem (K.mul_mem hκ x.2) (K.inv_mem hκ)
    convert this using 1
    simp [mul_assoc]
  · have := K.mul_mem (K.mul_mem (K.inv_mem hκ) x.2) hκ
    convert this using 1
    simp [mul_assoc]

theorem stabCard_out (Γ K : Subgroup G) (x : G) :
    stabCard Γ K (Quotient.mk (dcSetoid Γ K) x).out = stabCard Γ K x :=
  (stabCard_eq (Quotient.mk_out (s := dcSetoid Γ K) x)).symm

theorem stabCard_conj (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by
  unfold stabCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

def dcConj (Γ K : Subgroup G) (h : G) : DC Γ (K.map (MulAut.conj h).toMonoidHom) ≃ DC Γ K :=
  Quotient.congr (Equiv.mulRight h) (by
    intro a b
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      rw [Subgroup.mem_map_equiv] at hκ
      refine ⟨γ, hγ, _, hκ, ?_⟩
      simp [e, MulAut.conj_symm_apply, mul_assoc]
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      refine ⟨γ, hγ, h * κ * h⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_map_equiv]
        simpa [MulAut.conj_symm_apply, mul_assoc] using hκ
      · have e' : b = γ * a * h * κ * h⁻¹ := by
          have := congrArg (· * h⁻¹) e
          simpa [mul_assoc] using this
        rw [e']
        simp [mul_assoc])

theorem mass_conj (Γ K : Subgroup G) (h : G) :
    mass Γ (K.map (MulAut.conj h).toMonoidHom) = mass Γ K := by
  unfold mass
  rw [← finsum_comp_equiv (dcConj Γ K h)]
  refine finsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    have e1 : dcConj Γ K h (Quotient.mk _ x) = Quotient.mk (dcSetoid Γ K) (x * h) := rfl
    rw [e1, stabCard_out, stabCard_out, stabCard_conj]

end GlobalTheory.UnimodMass
