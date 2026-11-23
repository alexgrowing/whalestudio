import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IdealId' : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (r s r' s' i j i' j' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ i j → H'.IsAdapted σ B W W₁ i' j' → i < n → j < n → i' < d → j' < d →
    ∀ u (e₁ e₂ : ℤˣ), (u = shiftA H H' ∧ e₁ = a₁ ∧ e₂ = a₂) ∨ (u = shiftB σ H H' ∧ e₁ = b₁ ∧ e₂ = b₂) →
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 ∧ (∀ v l, idem F v • u l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E)) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w 𝔞 = 0) ∧
      ∀ ν : Chr F E, Continuous ν → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range ν 0 → UnrOff ν (B.P : Set (Pl F)) →
        idealVal ν 𝔞 = idealVal ν H.𝔟 ^ (e₁ : ℤ) * idealVal ν H'.𝔟 ^ (e₂ : ℤ)

def IdealId0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (r s r' s' i j i' j' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ i j → H'.IsAdapted σ B W W₁ i' j' →
    ∀ u, u = shiftA H H' ∨ u = shiftB σ H H' →
    ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 ∧ (∀ v l, idem F v • u l ∈ latAtV X W v ↔ InAt 𝔞 v (l : AE F E))

end PositivityTheory.ThKG.Loc.Cone

end
