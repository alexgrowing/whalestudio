import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)

namespace UpperTheory.Gal.Int.Geo.Pl

def InIdUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : Plc E) (𝔟 𝔠 : Ideal (𝓞 E)), (∃ s ∈ 𝔠, s ∉ w.asIdeal) →
  ∀ y, InId w (𝔟 * 𝔠) y ↔ InId w 𝔟 y

def ProjLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
    (_ : Frame S) (N : Lv p) (v : Plc E) (σ : Site S N v) (q' k : ℕ), q'.Prime → q' ≠ σ.q → ∀ K₁ : Subgroup S.G.GAf,
    IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞) K₁ → ∀ u ∈ σ.K₀, ∃ x ∈ S.L.KN N.1, x⁻¹ * u ∈ K₁

end UpperTheory.Gal.Int.Geo.Pl

end
