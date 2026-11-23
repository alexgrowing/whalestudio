import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem norm_not_mem_sq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (hd : u.asIdeal.inertiaDeg ℤ = 1) (he : u.asIdeal.ramificationIdx ℤ = 1) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 := by
  classical
  have hprime : Nat.Prime (Ideal.absNorm u.asIdeal) :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 u).2 hd
  haveI : Fact (Nat.Prime (Ideal.absNorm u.asIdeal)) := ⟨hprime⟩
  have hmemZ : ((Ideal.absNorm u.asIdeal : ℕ) : ℤ) ∈ u.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem u.asIdeal
  have hspan : u.asIdeal.under ℤ = Ideal.span {((Ideal.absNorm u.asIdeal : ℕ) : ℤ)} :=
    ((Int.ideal_span_isMaximal_of_prime (Ideal.absNorm u.asIdeal)).eq_of_le
      Ideal.IsPrime.ne_top' ((Ideal.span_singleton_le_iff_mem _).2 hmemZ)).symm
  have hp0 : u.asIdeal.under ℤ ≠ ⊥ := by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have he' : (u.asIdeal.under ℤ).ramificationIdx' u.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (u.asIdeal.under ℤ) u.asIdeal hp0]
    exact he
  have hmap : (u.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 F)) ≤ u.asIdeal := Ideal.map_comap_le
  intro hmem
  refine (Ideal.ramificationIdx'_ne_one_iff hmap).2 ?_ he'
  rw [hspan, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
  simpa using hmem

private theorem dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

theorem splitPlace : SplitPlace := by
  intro F Ω _ _ _ _ _ U hU T hT
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup Ω F U hU
  have hc : GlobalTheory.TwSys.Cheb :=
    GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne'
  unfold GlobalTheory.TwSys.Cheb at hc
  obtain ⟨v, hvA, hd, he, B, hB, hIB, σ, hσ, hσN⟩ := hc F Ω N hNo hNn 1 hT.toFinset
  have hvT : v ∉ T := fun h => hvA (hT.mem_toFinset.2 h)
  have hσN' : σ ∈ N := by simpa using hσN
  have hdec := dec_le hNo hB hIB hσ hσN'
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨v, hvT, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
  · rw [hnorm]
    exact Ideal.absNorm_mem _
  · rw [hnorm]
    exact norm_not_mem_sq v hd he
  · intro A hA ρ hρ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hB hA
    apply hNU
    have h1 : τ⁻¹ * ρ * τ ∈ Dec (F := F) B := by
      rw [mem_Dec] at hρ ⊢
      rw [← hτ] at hρ
      rw [mul_smul, mul_smul, hρ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 := hNn.conj_mem _ (hdec h1) τ
    simpa [mul_assoc] using h2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
