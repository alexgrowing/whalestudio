import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isVecLine_mem_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf i ℓ h c
  obtain ⟨hgood, hp, -⟩ := h
  choose M cl hM hcl hc using hp
  obtain ⟨h1, -, h3⟩ := local_global_ideal_lattice K
  refine (h1 ℓ.I cl hgood.1 hcl c).trans (Iff.trans ?_ (h3 _ _ _).symm)
  refine forall_congr' fun p => ?_
  refine (hc p c).symm.trans (Iff.trans ?_ (isModelAt_integral_iff_mem_lieLat K A x φ hf p (M p) (hM p) _))
  have e : (Pi.single i c : Fin x.P.g → K) = c • (Pi.single i 1 : Fin x.P.g → K) := by
    rw [← Pi.single_smul', smul_eq_mul, _root_.mul_one]
  rw [e, Matrix.smul_vecMul]

end GlobalTheory.LamF
