import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeChar_trivOn_realSubfield_infinityType : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (e : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ0 : ∀ v : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), (∀ w ∈ S, ∀ w', ConjPl c.toRingEquiv w w' → w' ∉ S) → (∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) → (∏ i, φ i ((ζ : 𝓞 L) : L) ^ (-e i)) * ∏ w ∈ S, ((θ0 w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => -2 * e i) ∧ (∀ v, χ.TameAt v) ∧ (∀ v, v ∉ S → (∀ w ∈ S, ¬ ConjPl c.toRingEquiv w v) → χ.UnrAt v) ∧ (∀ w ∈ S, ∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ w.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal y → χ.locK w k = θ0 w b) ∧ (∀ w ∈ S, ∀ n : ℕ, ((∀ x, IsUnitAt w x → χ.loc w x ^ n = 1) ↔ θ0 w ^ n = 1) ∧ ∀ w', ConjPl c.toRingEquiv w w' → ((∀ x, IsUnitAt w' x → χ.loc w' x ^ n = 1) ↔ θ0 w ^ n = 1)) := by
  first | exact @GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | exact GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn | (intros; apply GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn <;> assumption)
