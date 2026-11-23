import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrimeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberRay

theorem containsRayField_sub (P : Pre) (δ : FieldDat P) (K : IntermediateField ℚ ℂ) [NumberField K]
    (hKE : K ≤ P.host.φ₀.toRatAlgHom.fieldRange) (hKR : K ≤ δ.ray) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hKR).toRingHom (modulus P) := by
  obtain ⟨hm, hNF, hray⟩ := δ.isRay
  letI := algOf P.host.φ₀ δ.ray hm
  obtain ⟨hab, hun, -, hart⟩ := hray
  haveI : IsGalois P.host.E δ.ray := hab.toIsGalois
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P) :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)
  let e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom
  let φKE : K →+* P.host.E :=
    ((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp
      (IntermediateField.inclusion hKE).toRingHom
  have hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom := by
    refine RingHom.ext fun x => Subtype.ext ?_
    have := congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))
    exact this
  rw [← hcomp]
  exact GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC

theorem weberSet_subset_ray : ∀ (P : Pre) (δ : FieldDat P) (L : PeriodPair), (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) → ∀ n : ℕ, Odd n → 3 ≤ n → n ∣ modulus P → weberSet L n ⊆ δ.ray := by
  intro P δ L hL n _ hn hdvd
  obtain ⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩ := GlobalTheory.FieldSize.exists_hostK P.R P.host
  have hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
  have hKR : K ≤ δ.ray := fun z hz => by
    obtain ⟨x, rfl⟩ := hKE hz
    exact δ.isRay.emb_mem x
  have hCK := containsRayField_sub P δ K hKE hKR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd L hP n hn
  haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)
  have hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0 := by
    exact_mod_cast modulus_ne_zero P
  haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _
  have hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_
    refine ((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hCK 𝔓 hc.1
    have h1' : (n : 𝓞 K) ∣ α - 1 := (Nat.cast_dvd_cast hdvd).trans h1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin δ.ray _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberRay
