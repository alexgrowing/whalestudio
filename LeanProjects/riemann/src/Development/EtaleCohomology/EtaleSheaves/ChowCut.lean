import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
