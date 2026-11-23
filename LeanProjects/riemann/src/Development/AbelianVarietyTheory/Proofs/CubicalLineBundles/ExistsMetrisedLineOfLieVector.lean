import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_single_mem {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K))
    (hfg : Λ.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (i : Fin n) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ c : K, c ∈ I ↔ Pi.single i c ∈ Λ := by
  let J : Submodule (𝓞 K) K := Λ.comap (LinearMap.single (𝓞 K) (fun _ : Fin n => K) i)
  have hle : J ≤ Λ.map (LinearMap.proj i) := fun c hc => ⟨_, hc, by simp⟩
  have hJ : J.FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (hfg.map (LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) i))
    exact isNoetherian_submodule.1 this _ hle
  refine ⟨⟨J, FractionalIdeal.isFractional_of_fg hJ⟩, fun h0 => ?_, fun c => Iff.rfl⟩
  have h1 : (Pi.single i 1 : Fin n → K) ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ _ h1
  rw [Submodule.span_eq] at ht
  have h2 : algebraMap (𝓞 K) K t ∈ J := by
    change Pi.single i _ ∈ Λ
    rw [Algebra.algebraMap_eq_smul_one, Pi.single_smul]
    exact ht
  have h3 : J = ⊥ := (congrArg FractionalIdeal.coeToSubmodule h0).trans FractionalIdeal.coe_zero
  rw [h3, Submodule.mem_bot] at h2
  exact nonZeroDivisors.coe_ne_zero t (FaithfulSMul.algebraMap_injective _ K (h2.trans (map_zero _).symm))

theorem exists_length_of_lieVec (hU : ThetaUnifAV) {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) (σ : K →+* ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ (xσ : KeyIn ℂ) (u : HolUnif xσ.P.A xσ.P.L xσ.P.g) (Hm : Matrix (Fin xσ.P.g) (Fin xσ.P.g) ℂ)
      (χ : u.Λ → ℂ) (W : Fin xσ.P.g → ℂ) (hg : xσ.P.g = x.P.g),
      KeyPB xσ x σ ∧ u.IsAH Hm χ ∧ u.IsDiff W (xσ.v (i.cast hg.symm)) ∧
      r ^ 2 = Real.pi * (W ⬝ᵥ Hm.mulVec (star W)).re := by
  obtain ⟨xσ, hx⟩ := KeyPow.exists_keyPB x σ
  have hg : xσ.P.g = x.P.g := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact hg
  obtain ⟨u, Hm, χ, -, hA, -, hd, hd', -⟩ := hU xσ.P xσ.rig xσ.rig_gen
  choose W hW using fun i => (hd _ (xσ.basis.1 i)).exists
  have hne := (LieMetric.linearIndependent_of_isLieBasis u hd' xσ.basis hW).ne_zero (i.cast hg.symm)
  have hpos := mul_pos Real.pi_pos (hA.2.1 _ hne)
  exact ⟨_, Real.sqrt_pos.2 hpos, xσ, u, Hm, χ, _, hg, hx, hA, hW _, Real.sq_sqrt hpos.le⟩

theorem exists_isVecLine : Out.SecTwistSt → ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ i : Fin x.P.g, ∃ ℓ : MLine K, IsVecLine A x φ i ℓ := by
  intro hT hU _ K _ _ A x φ hφ i
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ := (isFibreOf_iff_isPolFibre _ _ _ A x φ).1 hφ
  obtain ⟨hfg, hsp⟩ := GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K A (GenFib.mk x.P φ hf x.v x.basis)
  obtain ⟨I, hI, hmem⟩ := exists_fractionalIdeal_single_mem _ hfg hsp i
  choose r hr H using exists_length_of_lieVec hU x i
  refine ⟨⟨I, r⟩, ⟨hI, hr⟩, fun p => ?_, H⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_dvrModel_lieBasis_at_prime hT K A x φ hφ p
  obtain ⟨⟨cl, -, hcl⟩, hiff⟩ := (local_global_ideal_lattice K).2.1 I p hI
  refine ⟨M, cl, hM, hcl, fun c => ?_⟩
  rw [((hiff cl).1 hcl).2 c, ← Matrix.smul_vecMul, isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [hmem, Pi.single_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]

end GlobalTheory.LamF
