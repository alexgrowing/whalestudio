import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem specComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1

theorem vertComps_finite' {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

open Classical in

theorem OrdEq.proof (hni : NormIdentity.Statement) (hnl : NormLength.Statement)
    (hld : LengthDecomp.Statement) (hmax : SpecMax.Statement) (hlen : SpecLength.Statement)
    (hres : SpecResidue.Statement) (hvs : VertSpec.Statement) (hinj : SecBLinInj.Statement)
    (hfin : SecBFinite.Statement) (htf : SecBTorsionFree.Statement) (hdvr : ParDVRIsDVR.Statement) :
    OrdEq.Statement := by
  intro K _ _ n e I g u v hI hf hu hprim
  have := hdvr K e n v
  set f := g.map (algebraMap (𝓞 K) K)
  set ℓ := secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))
  obtain ⟨w, hw⟩ := hni K n e I g u v hI hf hu hprim
  rw [hw, Ring.ord_mul_of_isUnit_left w.isUnit]
  have hfinB : Module.Finite (ParDVR e n v) (SecB e I v) := hfin K n e I f v hI hf
  have htfB : Module.IsTorsionFree (ParDVR e n v) (SecB e I v) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r b h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · exact Or.inr (htf K n e I v hI r b hr h)
  have hfreeB : Module.Free (ParDVR e n v) (SecB e I v) := Module.free_of_finite_type_torsion_free'
  have hℓ : Function.Injective fun b : SecB e I v => ℓ * b := hinj K n e I f u v hI hf hu
  rw [hnl _ _ ℓ hℓ]

  have hN0 : Algebra.norm (ParDVR e n v) ℓ ≠ 0 := by
    rw [Algebra.norm_apply, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hℓ
  have hfinite : Module.length (ParDVR e n v) (SecB e I v ⧸ Ideal.span {ℓ}) ≠ ⊤ := by
    rw [← hnl _ _ ℓ hℓ]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hN0)
  rw [hld _ _ ℓ hfinite]

  obtain ⟨hmax1, hmax2⟩ := hmax K n e I f v hI hf
  choose W hW hWu using fun 𝔫 : MaximalSpectrum (SecB e I v) => hmax2 𝔫.asIdeal 𝔫.isMaximal
  set G : Ideal (MvPolynomial (Fin n) (𝓞 K)) → ℕ∞ := fun W =>
    (if linForm u ∈ W then (localMult (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0) *
      (chowDegree (reduceMod v W) (e + 1) : ℕ∞) with hG
  have hbij : Set.BijOn W Set.univ (specComps I v) := by
    refine ⟨fun 𝔫 _ => (hW 𝔫).1, fun 𝔫₁ _ 𝔫₂ _ h => ?_, fun W' hW' => ?_⟩
    · apply MaximalSpectrum.ext
      rw [← (hW 𝔫₁).2, ← (hW 𝔫₂).2, h]
    · refine ⟨⟨secIdealOf e I v W', hmax1 W' hW'⟩, Set.mem_univ _, ?_⟩
      exact (hWu _ W' ⟨hW', rfl⟩).symm
  rw [← finsum_mem_univ, finsum_mem_eq_of_bijOn W hbij (g := G) fun 𝔫 _ => by
    rw [hlen K n e I f u v hI hf hu 𝔫 (W 𝔫) (hW 𝔫).1 (hW 𝔫).2, ← (hW 𝔫).2,
      hres K n e I f v hI hf (W 𝔫) (hW 𝔫).1]]

  have hs := specComps_finite I v
  have hv := vertComps_finite' I u v
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, vertDeg, Nat.cast_finsum_mem hv,
    finsum_mem_eq_finite_toFinset_sum _ hv]
  have hset : hv.toFinset = hs.toFinset.filter fun W => linForm u ∈ W := by
    ext W
    simp [hvs K n e I f u v hI hf hu]
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  simp only [hG]
  split_ifs <;> simp

end

end GroundTheory.Heights₂.Heights.Vertical
