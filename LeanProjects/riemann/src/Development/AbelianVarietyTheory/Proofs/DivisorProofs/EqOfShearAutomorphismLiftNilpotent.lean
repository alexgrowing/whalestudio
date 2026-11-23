import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidityStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

theorem eq_of_fst_snd_left {C : Type*} [Category C] [Limits.HasPullbacks C] {B : C} {Y : Over B} {T : C}
    {a b : T ⟶ (Y ⊗ Y).left} (h₁ : a ≫ (fst Y Y).left = b ≫ (fst Y Y).left)
    (h₂ : a ≫ (snd Y Y).left = b ≫ (snd Y Y).left) : a = b := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact Limits.pullback.hom_ext h₁ h₂

theorem eq_of_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i → IsIso (lift (fst X X) m) →
    ∀ (P : Over (Sp R)) (P₀ : Over (Sp R₀)) (k : P₀.left ⟶ P.left), IsPullback k P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f f' : P ⟶ X), k ≫ f.left = k ≫ f'.left → ε ≫ f.left = ε ≫ f'.left → f = f' := by
  intro R R₀ _ _ π hπ hnil A₀ _ X i hi l hl1 hl2 m hm hσ P P₀ k hk hsm hpr hgc ε hε f f' hk' hε'
  have hσl : IsIso (lift (fst X X) m).left := Functor.map_isIso (Over.forget (Sp R)) (lift (fst X X) m)

  have hsq : (k ≫ f.left) ≫ X.hom = P₀.hom ≫ spMap π := by
    rw [Category.assoc, Over.w f]; exact hk.w
  let f₀ : P₀ ⟶ A₀ := Over.homMk (hi.lift (k ≫ f.left) P₀.hom hsq) (hi.lift_snd _ _ _)
  have hf₀i : f₀.left ≫ i = k ≫ f.left := hi.lift_fst _ _ _

  have hlσ : l ≫ (lift (fst X X) m).left = (lift (fst A₀ A₀) μ).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hm, hl2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have hred : k ≫ (lift f f).left = (lift f₀ f₀).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst, hf₀i]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hl2, ← Category.assoc, ← Over.comp_left, lift_snd, hf₀i]
  let h₀ : P₀ ⟶ A₀ ⊗ A₀ := lift f₀ (toUnit P₀ ≫ η)
  have hh₀ : h₀ ≫ lift (fst A₀ A₀) μ = lift f₀ f₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [h₀]
    · simp only [h₀, Category.assoc, lift_snd]
      exact lift_comp_one_right _ _
  obtain ⟨gu, hgu_def⟩ : ∃ g, g = lift f f' ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  obtain ⟨gv, hgv_def⟩ : ∃ g, g = lift f f ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  have eu : gu.left ≫ (lift (fst X X) m).left = (lift f f').left := by
    rw [← Over.comp_left, hgu_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ev : gv.left ≫ (lift (fst X X) m).left = (lift f f).left := by
    rw [← Over.comp_left, hgv_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hgv : k ≫ gv.left = h₀.left ≫ l := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, ev, hred, Category.assoc, hlσ,
      ← Category.assoc, ← Over.comp_left, hh₀]
  have hpair_k : k ≫ (lift f f').left = k ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hk'.symm
  have hpair_ε : ε ≫ (lift f f').left = ε ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hε'.symm
  have hgu_k : k ≫ gu.left = k ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_k]
  have hgu_ε : ε ≫ gu.left = ε ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_ε]

  have e2 : (h₀ ≫ snd A₀ A₀).left = P₀.hom ≫ (η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left := by
    simp only [h₀, lift_snd, Over.comp_left, Over.toUnit_left]
  have hv₀ : k ≫ (gv ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    calc k ≫ (gv ≫ snd X X).left = (k ≫ gv.left) ≫ (snd X X).left := by
          rw [Over.comp_left, Category.assoc]
      _ = h₀.left ≫ (l ≫ (snd X X).left) := by rw [hgv, Category.assoc]
      _ = (h₀ ≫ snd A₀ A₀).left ≫ i := by rw [hl2, Over.comp_left, Category.assoc]
      _ = _ := by rw [e2, Category.assoc]
  have hu₀ : k ≫ (gu ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    rw [Over.comp_left, ← Category.assoc, hgu_k, Category.assoc, ← Over.comp_left]; exact hv₀
  have cu := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hu₀
  have cv := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hv₀
  have huv : gu ≫ snd X X = gv ≫ snd X X := by
    apply Over.OverMorphism.ext
    rw [cu, cv, Over.comp_left, Over.comp_left, ← Category.assoc ε gu.left, hgu_ε, Category.assoc]
  have hinvfst : inv (lift (fst X X) m) ≫ fst X X = fst X X := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hg : gu = gv := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hgu_def, hgv_def, Category.assoc, Category.assoc, hinvfst, lift_fst, lift_fst]
    · exact huv
  rw [hgu_def, hgv_def] at hg
  have hff : lift f f' = lift f f := (cancel_mono (inv (lift (fst X X) m))).1 hg
  have := congrArg (· ≫ snd X X) hff
  simp only [lift_snd] at this
  exact this.symm

end GlobalTheory.ShearLift
