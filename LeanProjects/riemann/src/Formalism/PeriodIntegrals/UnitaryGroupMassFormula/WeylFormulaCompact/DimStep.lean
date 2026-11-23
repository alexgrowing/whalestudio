import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStepB

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix DimensionInduction

lemma dimStep_one_mem {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

lemma dimStep_good {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset (allPos n)) σ) :
    Good (fun g : Kset (allPos n) => σ g.1) where
  isom := fun g v => hσ.2.1 g.1 g.2 v
  inv := fun g => ⟨⟨star g.1, Kset_star _ g.2⟩, fun v => by
    show σ g.1 (σ (star g.1) v) = v
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ g.2 _ (Kset_star _ g.2),
      Unitary.mul_star_self_of_mem g.2.1, hσ.1.1]
    rfl⟩
  mul := fun g g' => ⟨⟨g.1 * g'.1, Kset_mul _ g.2 g'.2⟩, fun v => by
    show σ g.1 (σ g'.1 v) = σ (g.1 * g'.1) v
    rw [hσ.1.2 _ g.2 _ g'.2]
    rfl⟩
  one := ⟨⟨1, dimStep_one_mem _⟩, fun v => by
    show σ 1 v = v
    rw [hσ.1.1]
    rfl⟩

lemma dimStep_stab {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H} :
    IsKStableOn (allPos n) σ W ↔ Stab (fun g : Kset (allPos n) => σ g.1) W :=
  ⟨fun h g v hv => h g.1 g.2 v hv, fun h g hg v hv => h ⟨g, hg⟩ v hv⟩

theorem dimension_induction_holds : DimStep := by
  intro p q H _ _ σ₁ σ₂ S X Y h1 h2 hcomm hS hS1 hS2 hSirr hXS hX0 hX1 hXi hYS hY0 hY2 hYi
  exact main (dimStep_good h1) (dimStep_good h2)
    (fun g g' v => by
      show σ₁ g.1 (σ₂ g'.1 v) = σ₂ g'.1 (σ₁ g.1 v)
      rw [← ContinuousLinearMap.comp_apply, hcomm _ g.2 _ g'.2]
      rfl)
    (dimStep_stab.1 hS1) (dimStep_stab.1 hS2)
    (fun S' h s1 s2 => hSirr S' h (dimStep_stab.2 s1) (dimStep_stab.2 s2))
    hXS hX0 (dimStep_stab.1 hX1) (fun X' h s => hXi X' h (dimStep_stab.2 s))
    hYS hY0 (dimStep_stab.1 hY2) (fun Y' h s => hYi Y' h (dimStep_stab.2 s))

end PI.WeylForKWork
