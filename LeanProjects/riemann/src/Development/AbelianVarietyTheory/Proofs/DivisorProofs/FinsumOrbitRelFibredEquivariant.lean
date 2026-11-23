import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex

namespace GlobalTheory

open MulAction

theorem finsum_orbitRel_fibred : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  intro H X B E _ _ _ _ π hπ S hS j hinj hjπ hjsurj hjeq s hs g hg
  let ρ : orbitRel.Quotient H X → orbitRel.Quotient H B :=
    Quotient.map π (fun x y hxy => by
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hxy)
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h, by rw [← hπ, hh]⟩))
  have hρ : ∀ x, ρ (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl
  rw [GlobalTheory.finsum_fiberwise_of_finite_support ρ g hg]
  refine finsum_congr (fun q => ?_)
  set b := s q with hb

  have key : ∀ e e' : E, (orbitRel (S b) E) e e' →
      Quotient.mk (orbitRel H X) (j b e) = Quotient.mk (orbitRel H X) (j b e') := by
    intro e e' hee
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hee)
    apply Quotient.sound
    refine orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨(k : H), ?_⟩)
    rw [← hjeq b k k.2 e', ← hk]
    rfl
  let φ : orbitRel.Quotient (S b) E → {o // ρ o = q} := fun o' =>
    ⟨Quotient.mk _ (j b (Quotient.out o')), by rw [hρ, hjπ, hb, hs]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro o₁ o₂ h12
      have h12' : Quotient.mk (orbitRel H X) (j b (Quotient.out o₁))
          = Quotient.mk (orbitRel H X) (j b (Quotient.out o₂)) := congrArg Subtype.val h12
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h12'))
      have hbh : h • b = b := by
        have := congrArg π hh
        rwa [hπ, hjπ, hjπ] at this
      have hmem : h ∈ S b := hS b (mem_stabilizer_iff.mpr hbh)
      have he : h • Quotient.out o₂ = Quotient.out o₁ := by
        apply hinj b
        rw [hjeq b h hmem, hh]
      rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨h, hmem⟩, he⟩)
    · rintro ⟨o, ho⟩
      have hx : Quotient.mk (orbitRel H B) (π (Quotient.out o)) = Quotient.mk (orbitRel H B) b := by
        rw [← hρ, Quotient.out_eq, ho, hb, hs]
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hx))
      obtain ⟨e, he⟩ := hjsurj b (h⁻¹ • Quotient.out o) (by rw [hπ, ← hh, inv_smul_smul])
      refine ⟨Quotient.mk _ e, Subtype.ext ?_⟩
      show Quotient.mk (orbitRel H X) (j b (Quotient.out (Quotient.mk (orbitRel (S b) E) e))) = o
      rw [key _ e (Quotient.exact (Quotient.out_eq _)), he]
      conv_rhs => rw [← Quotient.out_eq o]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩)
  exact (finsum_comp_equiv (Equiv.ofBijective φ hφ) (f := fun o : {o // ρ o = q} => g o.1)).symm

end GlobalTheory
