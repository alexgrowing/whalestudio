import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem idem_mul_eq_of_subset : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b →
    A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  intro F _ _ A₁ B₁ A₂ B₂ a b ha hb h1 h2
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, -, hb3, -⟩ := hb
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    refine ainf_ext fun w => ?_
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb1 w (h1 hw), one_mul]
    · rw [ha2 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb3 v (h2 hv), one_mul]
    · rw [ha4 v hv, mul_zero]

end GlobalTheory.CompanionTheory.SaGen
