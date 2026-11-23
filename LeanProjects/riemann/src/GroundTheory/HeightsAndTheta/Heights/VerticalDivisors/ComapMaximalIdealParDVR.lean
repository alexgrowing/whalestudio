import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Objects

variable {K : Type*} [Field K] [NumberField K]

theorem comap_maximalIdeal_parDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (IsLocalRing.maximalIdeal (ParDVR e n v)).comap (algebraMap (𝓞 K) (ParDVR e n v)) = v.asIdeal := by
  have h1 : algebraMap (𝓞 K) (ParDVR e n v) =
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)).comp C :=
    IsScalarTower.algebraMap_eq _ _ _
  have h2 : (IsLocalRing.maximalIdeal (ParDVR e n v)).comap
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v)) = parPrime e n v :=
    Localization.AtPrime.comap_maximalIdeal
  rw [h1, ← Ideal.comap_comap, h2]
  ext x
  simp only [Ideal.mem_comap, parPrime]
  constructor
  · intro hx
    rw [MvPolynomial.mem_map_C_iff] at hx
    simpa using hx 0
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

def resToKappa (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.ResidueField →+* (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  Ideal.ResidueField.map v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
    (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm

def parYκ (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    Par e n → (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField :=
  fun p => algebraMap (ParDVR e n v) (IsLocalRing.maximalIdeal (ParDVR e n v)).ResidueField (parY e n v p)

end Objects

def SpecCompDim.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      IsProjPrime (reduceMod v W) ∧
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ reduceMod v W) = ((e + 1 : ℕ) : WithBot ℕ∞)

def ChartDomain.Statement : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n),
    Q.IsPrime → (∀ c : D, C c ∈ Q → c = 0) → X j ∉ Q →
      IsDomain (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)) ∧
        Function.Injective (algebraMap D
          (Localization.Away (secCoord (Q.map (MvPolynomial.map (C : D →+* MvPolynomial (Par e n) D))) X j)))

def SecAlgField.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsField (SecAlg (Q.map (MvPolynomial.map (algebraMap k (FractionRing (MvPolynomial (Par e n) k)))))
        (fun p => algebraMap (MvPolynomial (Par e n) k) (FractionRing (MvPolynomial (Par e n) k)) (X p)))

def ParFracIsFractionRing.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (parToFrac e n v).toAlgebra
    IsFractionRing (ParDVR e n v) (ParFrac K e n)

def ResidueAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    letI := (resToKappa e n v).toAlgebra
    AlgebraicIndependent v.asIdeal.ResidueField (parYκ e n v)

end

end GroundTheory.Heights₂.Heights.Vertical
