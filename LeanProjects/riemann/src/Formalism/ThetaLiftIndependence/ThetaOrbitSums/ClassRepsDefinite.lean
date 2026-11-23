import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep

noncomputable section

namespace Formalism.ThetaLiftIndependence

namespace DefiniteClassRepresentatives

open Formalism.HermitianLatticesTheory LatticeLiftIndependence

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def isoSetoid (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Setoid (Submodule (NumberField.RingOfIntegers K) V) where
  r N M := ∃ g ∈ isom h, gmap g N = M
  iseqv := by
    refine ⟨fun N => ⟨1, (isom h).one_mem, gmap_one N⟩, ?_, ?_⟩
    · rintro N M ⟨g, hg, e⟩
      exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← e, gmap_inv_gmap]⟩
    · rintro N M P ⟨g, hg, e⟩ ⟨g', hg', e'⟩
      exact ⟨g' * g, (isom h).mul_mem hg' hg, by rw [gmap_mul, e, e']⟩

open Classical in

def pick (h : V →ₗ⋆[K] V →ₗ[K] K) (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (q : Quotient (isoSetoid h)) : Submodule (NumberField.RingOfIntegers K) V :=
  if hq : ∃ N ∈ s₀, Quotient.mk (isoSetoid h) N = q then Classical.choose hq else ⊥

theorem pick_spec (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    {M : Submodule (NumberField.RingOfIntegers K) V} (hM : M ∈ s₀) :
    pick h s₀ (Quotient.mk (isoSetoid h) M) ∈ s₀ ∧
      Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) M)) =
        Quotient.mk (isoSetoid h) M := by
  have hq : ∃ N ∈ s₀, Quotient.mk (isoSetoid h) N = Quotient.mk (isoSetoid h) M := ⟨M, hM, rfl⟩
  have e : pick h s₀ (Quotient.mk (isoSetoid h) M) = Classical.choose hq := by
    unfold pick
    exact dif_pos hq
  rw [e]
  exact Classical.choose_spec hq

theorem exists_reps (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (h₁ : ∀ M ∈ s₀, M ∈ genus h L) (h₂ : ∀ M ∈ genus h L, ∃ N ∈ s₀, ∃ g ∈ isom h, gmap g N = M) :
    ∃ s, IsClassReps h L s := by
  classical
  have hsound : ∀ A B : Submodule (NumberField.RingOfIntegers K) V,
      (∃ g ∈ isom h, gmap g A = B) → Quotient.mk (isoSetoid h) A = Quotient.mk (isoSetoid h) B :=
    fun A B hAB => Quotient.sound hAB
  have hexact : ∀ A B : Submodule (NumberField.RingOfIntegers K) V,
      Quotient.mk (isoSetoid h) A = Quotient.mk (isoSetoid h) B → ∃ g ∈ isom h, gmap g A = B :=
    fun A B e => Quotient.exact e
  refine ⟨s₀.image (fun N => pick h s₀ (Quotient.mk (isoSetoid h) N)), ?_, ?_⟩
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
    exact h₁ _ (pick_spec h s₀ hN).1
  · intro M hM
    obtain ⟨N, hN, g, hg, e⟩ := h₂ M hM
    obtain ⟨g', hg', e'⟩ := hexact _ _ (pick_spec h s₀ hN).2
    have hE : gmap (g * g') (pick h s₀ (Quotient.mk (isoSetoid h) N)) = M := by
      rw [gmap_mul, e', e]
    refine ⟨pick h s₀ (Quotient.mk (isoSetoid h) N),
      ⟨Finset.mem_image.mpr ⟨N, hN, rfl⟩, g * g', (isom h).mul_mem hg hg', hE⟩, ?_⟩
    rintro P ⟨hP, g₁, hg₁, e₁⟩
    obtain ⟨N₁, hN₁, rfl⟩ := Finset.mem_image.mp hP
    have hrel : Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) N₁)) =
        Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) N)) := by
      apply hsound
      refine ⟨(g * g')⁻¹ * g₁,
        (isom h).mul_mem ((isom h).inv_mem ((isom h).mul_mem hg hg')) hg₁, ?_⟩
      rw [gmap_mul, e₁, ← hE, gmap_inv_gmap]
    have hN : Quotient.mk (isoSetoid h) N₁ = Quotient.mk (isoSetoid h) N :=
      (pick_spec h s₀ hN₁).2.symm.trans (hrel.trans (pick_spec h s₀ hN).2)
    rw [hN]

end DefiniteClassRepresentatives

open Formalism.HermitianLatticesTheory LatticeLiftIndependence DefiniteClassRepresentatives in
theorem classRepsDefinite : ClassRepsDefinite := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos L hL
  classical

  have hcard : ∀ M ∈ genus h L, 0 < Nat.card (autL h M) := by
    intro M hM
    have hfin : Set.Finite (autL h M) := final_autFinite K V h hsymm hpos M hM.1
    have : Finite (autL h M) := hfin.to_subtype
    have : Nonempty (autL h M) := ⟨⟨1, (isom h).one_mem, gmap_one M⟩⟩
    exact Nat.card_pos
  obtain ⟨s₀, h₁, h₂⟩ := final_classSetFinite K V h hsymm hpos L hL
  obtain ⟨s, hs⟩ := exists_reps h L s₀ h₁ h₂
  refine ⟨⟨s, hs⟩, fun M hM => ⟨Nat.card (autL h M), hcard M hM, rfl⟩, ?_⟩
  refine ⟨∏ N ∈ s, Nat.card (autL h N), Finset.prod_pos fun N hN => hcard N (hs.1 N hN), ?_⟩
  intro M hM
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 M hM
  refine ⟨((∏ N' ∈ s.erase N, Nat.card (autL h N') : ℕ) : ℤ), ?_⟩
  rw [← e, latWt_gmap h hg N, ← Finset.mul_prod_erase s _ hN]
  have hne : ((Nat.card (autL h N) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (hcard N (hs.1 N hN)).ne'
  unfold latWt
  push_cast
  field_simp

end Formalism.ThetaLiftIndependence
