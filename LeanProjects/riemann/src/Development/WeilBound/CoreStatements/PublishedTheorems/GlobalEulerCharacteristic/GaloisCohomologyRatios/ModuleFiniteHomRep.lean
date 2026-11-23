import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NormalOfGsOpenSubgroupNormal
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GEqAddOfExactOfFiniteCokernel
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Stabilizers
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaCount
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]

instance moduleFinite_homRep (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [Module.Finite (ZMod ℓ) M] :
    Module.Finite (ZMod ℓ) (homRep (gsRootsZMod S ℓ) M) :=
  inferInstanceAs (Module.Finite (ZMod ℓ) (gsRootsZMod S ℓ →ₗ[ZMod ℓ] M))

noncomputable abbrev PP : Subgroup (galUnramifiedOutside K.1 ℚ̄ S) := (gsOpenSubgroup S hL : Subgroup _)

noncomputable abbrev AA (i : ℕ) := cohomology (Rep.res (PP hL).subtype (galSUnitsMax K.1 ℚ̄ S)) i

noncomputable abbrev actA (i : ℕ) : DistribMulAction (L.1 ≃ₐ[K.1] L.1) (AA hL i) :=
  conjActionOf (PP hL) (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL)
    (galSUnitsMax K.1 ℚ̄ S) i

noncomputable def dMod (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) (i : ℕ) [Finite (ModN (AA hL i) ℓ)] : ℤ :=
  letI := actA hL i
  d.toFun (ModN (AA hL i) ℓ) (modNRep _ (AA hL i) ℓ)

noncomputable def dTors (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1)) (i : ℕ) [Finite (TorsN (AA hL i) ℓ)] : ℤ :=
  letI := actA hL i
  d.toFun (TorsN (AA hL i) ℓ) (torsNRep _ (AA hL i) ℓ)

noncomputable def nRep (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    Representation (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (homRep (gsRootsZMod S ℓ) M) :=
  (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M)
    (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)).comp
    (gsQuotientGalEquiv hL).symm.toMonoidHom

noncomputable def dN (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
    (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ) : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1) :=
  AdditiveFunction.invariantsTensor.{0} ℓ _ hΓ (nRep hL hζ M hM)

end PositivityTheory.Lit1.GEN.X
