import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionBasisRealMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointDefinedOverBaseStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem toUnit_comp_injective {Ω : Type} [Field Ω] (t : Sp Ω ⟶ Sp ℂ) {A : Over (Sp ℂ)}
    {z z' : 𝟙_ (Over (Sp ℂ)) ⟶ A} (h : toUnit (Over.mk t) ≫ z = toUnit (Over.mk t) ≫ z') : z = z' := by
  obtain ⟨_, _⟩ := GlobalTheory.PolIsoDescent.flat_surjective t
  have : Epi t := Flat.epi_of_flat_of_surjective _
  have e : (toUnit (Over.mk t)).left = t := by
    have := Over.w (toUnit (Over.mk t))
    simpa using this
  apply Over.OverMorphism.ext
  apply (cancel_epi t).1
  have := congrArg CommaMorphism.left h
  simpa [e] using this

theorem exists_torsion_basis (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ)
    (hN : 1 ≤ N) :
    ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ i, pt i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (pt 0 ≫ X.rm.act a) * (pt 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ X.rm.act a) * (pt 1 ≫ X.rm.act b) := by
  obtain ⟨L, u, Fa, h⟩ := GlobalTheory.T.exists_real_multiplication_uniformization F 𝔠 X
  exact GlobalTheory.T.exists_torsion_basis_real_multiplication F X.A X.rm L u Fa h N hN

theorem nonempty_level_complex : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ),
    1 ≤ N → ∀ X : Obj F 𝔠 (Sp ℂ), Nonempty (X.Level N) := by
  intro F _ _ _ 𝔠 N hN X
  obtain ⟨pt, htor, hinj, hsurj⟩ := exists_torsion_basis F 𝔠 X N hN
  refine ⟨{ pt := pt, tors := htor, inj := ?_, surj := ?_ }⟩
  · intro Ω _ _ t a b h
    apply hinj a b
    apply toUnit_comp_injective t
    rw [MonObj.comp_mul, MonObj.comp_one, ← Category.assoc, ← Category.assoc]
    exact h
  · intro Ω _ _ t y hy
    obtain ⟨z, rfl⟩ := GlobalTheory.T.torsion_point_defined_over_base F 𝔠 X N hN Ω t y hy
    have hz : z ^ N = 1 := by
      apply toUnit_comp_injective t
      rw [MonObj.comp_pow, hy, MonObj.comp_one]
    obtain ⟨a, b, rfl⟩ := hsurj z hz
    exact ⟨a, b, by rw [MonObj.comp_mul]⟩

end GlobalTheory.RealMult.Obj
