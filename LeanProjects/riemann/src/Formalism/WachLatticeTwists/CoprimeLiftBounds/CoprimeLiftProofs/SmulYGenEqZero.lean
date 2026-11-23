import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.ImportsAlt

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section SlopeTestRemainingChoices
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

def cobZ (ρ : Representation O G M) (v : M) : coZ1s ρ :=
  ⟨coD0 ρ v, fun g h => by
    show ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
    rw [map_mul, map_sub, Module.End.mul_apply]; abel⟩

lemma mkQ_cobZ (ρ : Representation O G M) (v : M) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) (cobZ ρ v) : H1z ρ) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self (coD0 ρ) v

lemma mkQ_eq_zero_of (ρ : Representation O G M) (z : coZ1s ρ) (v : M)
    (h : ∀ g, (z : G → M) g = ρ g v - v) :
    (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype) z : H1z ρ) = 0 := by
  have hz : z = cobZ ρ v := Subtype.ext (funext h)
  rw [hz]
  exact mkQ_cobZ ρ v

end SlopeTestRemainingChoices

section Y
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

lemma ycoc_eq (r : G →* A) (χ : G →* T'ˣ) (E : A) (g : G) :
    ycoc r χ E g =
      (((χ g)⁻¹ : T'ˣ) : T') • ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) := by
  show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = _
  rw [sub_mul, sub_mul, smul_sub, one_mul, smul_mul_assoc,
    Algebra.smul_def (((χ g)⁻¹ : T'ˣ) : T') (algebraMap T' A ((χ g : T'ˣ) : T') * E), ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]

lemma smul_yGen_eq_zero (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A) (a : A) (g : G)
    (h : a * ycoc r χ E g = 0) : a • yGen r χ E e₁ δ D j Kc k0 g = 0 := by
  unfold yGen
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  convert Submodule.zero_mem _ using 1
  exact Prod.ext (Subtype.ext h) (smul_zero _)

end Y

theorem qAlg : StatQAlg := by
  intro A T' G _ _ _ _ r χ E γ ζ h hζ
  rw [ycoc_eq, mul_smul_comm, hζ, ← mul_assoc, h, zero_mul, smul_zero]

theorem colChiC : StatColChiC := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 he hE hk φ l
  obtain ⟨_, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) (D l)
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) (D l)))
  rw [Submodule.Quotient.mk_eq_zero]
  show ((restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) :
      coZ1s (resRep (uRep O (M := M) r χ) (D l))) : D l → M) ∈
    LinearMap.range (coD0 (resRep (uRep O (M := M) r χ) (D l)))
  rw [LinearMap.mem_range]
  refine ⟨-φ (nuGen r χ E e₁ δ D j Kc k0 l), ?_⟩
  funext g
  show uElt r χ (g : G) • -φ (nuGen r χ E e₁ δ D j Kc k0 l) - -φ (nuGen r χ E e₁ δ D j Kc k0 l) =
    φ (yGen r χ E e₁ δ D j Kc k0 (g : G))
  obtain ⟨a0, ha0⟩ := hk l g
  have h := hy g g.2
  simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, ha0, mul_smul, hE] at h
  rw [eq_neg_of_add_eq_zero_left h, smul_neg]
  abel

theorem colChiOne : StatColChiOne := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ δO ι _ D j Kc k0 ℓ e' u hu he hE hδ hk φ l
  obtain ⟨hnu, hsig, _, hy⟩ := rel A T' G M r χ E e₁ δ ι D j Kc k0 φ l
  have hs : ∀ a, φ (sigGen r χ E e₁ δ D j Kc k0 l a) = 0 := fun a => by rw [← hsig a, he]
  have h2 : ∀ g ∈ D l, φ (yGen r χ E e₁ δ D j Kc k0 g) =
      (δO * δO * (ℓ : O) ^ e' l * u l g) • φ (sigmaZeroColumnGenerator r χ E e₁ δ D j Kc k0 l) := by
    intro g hg
    have h := hy g hg
    simp only [hs, smul_zero, Finset.sum_const_zero, zero_add, hu, sub_self, add_zero, hk l g hg,
      hδ] at h
    rw [h, smul_smul]
    congr 1
    ring
  refine ⟨by rw [← hE]; exact hnu, h2, fun I hI => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ))) =
    (0 : H1z (resRep (resRep (uRep O (M := M) r χ) (D l)) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (resRep (uRep O (M := M) r χ) (D l)) I
      (restrictCocycles1 (uRep O (M := M) r χ) (D l) (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 ((g : D l) : G)) = 0
    rw [h2 _ (g : D l).2, hI g g.2, mul_zero, zero_smul]
  rw [hz]
  exact Submodule.zero_mem _

theorem unrOutside : StatUnrOutside := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI
  have hy : ∀ g ∈ I, ycoc r χ E g = 0 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hI g hg
    show ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1) * E = 0
    rw [h1, h2, inv_one, Units.val_one, one_smul, sub_self, zero_mul]
  refine ⟨hy, fun φ => ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    have h0 := smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 (1 : A) (g : G)
      (by rw [one_mul]; exact hy g g.2)
    rw [one_smul] at h0
    rw [h0, map_zero]
  rw [hz]
  exact Submodule.zero_mem _

theorem unrS : StatUnrS := by
  intro O _ A T' G _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 I hI φ
  have hy0 : ∀ g ∈ I, φ (yGen r χ E e₁ δ D j Kc k0 g) = 0 := by
    intro g hg
    obtain ⟨a, ha, hinj⟩ := hI g hg
    apply hinj
    rw [← map_smul, smul_yGen_eq_zero r χ E e₁ δ D j Kc k0 a g
      (by rw [ycoc_eq, mul_smul_comm, ha, smul_zero]), map_zero]
  refine ⟨hy0, ?_⟩
  apply LinearMap.mem_ker.mpr
  show Submodule.Quotient.mk (restrictCocycles1 (uRep O (M := M) r χ) I
      (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ)) =
    (0 : H1z (resRep (uRep O (M := M) r χ) I))
  rw [Submodule.Quotient.mk_eq_zero]
  have hz : restrictCocycles1 (uRep O (M := M) r χ) I (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) = 0 := by
    apply Subtype.ext
    funext g
    show φ (yGen r χ E e₁ δ D j Kc k0 (g : G)) = 0
    exact hy0 g g.2
  rw [hz]
  exact Submodule.zero_mem _

end Formalism.RepresentationBoundsCohomology.BR
