import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SimpLemmas

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

namespace UpperTheory.Prune

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)}

private theorem val_int_le (A : LocAt F E sig p) (c : 𝓞 F) : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F c)) ≤ 1 := by
  have h := (A.val (algebraMap (𝓞 F) F c) 1).2 (by rw [map_one]; exact p.valuation_le_one c)
  rw [map_one] at h
  simpa using (Valuation.vle_iff_le (valuation A.Fp)).1 h

private theorem exists_small (A : LocAt F E sig p) {W : Set A.Fp} (hW : W ∈ nhds (0 : A.Fp)) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y, valuation A.Fp y ≤ valuation A.Fp (A.ιF (algebraMap (𝓞 F) F c)) → y ∈ W := by
  haveI := A.lf
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).1 hW
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hlt : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F π)) < 1 := by
    refine lt_of_not_ge fun h => ?_
    have h1 : A.ιF 1 ≤ᵥ A.ιF (algebraMap (𝓞 F) F π) := (Valuation.vle_iff_le (valuation A.Fp)).2 (by simpa using h)
    have h2 := (A.val _ _).1 h1
    rw [map_one] at h2
    exact absurd ((p.valuation_lt_one_iff_mem (K := F) π).2 hπ) (not_lt.2 h2)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt γ
  refine ⟨π ^ n, pow_ne_zero n hπ0, fun y hy => hγ ?_⟩
  rw [map_pow, map_pow, map_pow] at hy
  exact lt_of_le_of_lt hy hn

private theorem mem_O (A : LocAt F E sig p) {β : E} (hβ : IsIntegral (𝓞 F) β) : A.ιE β ∈ A.O := by
  let φ : 𝓞 F →+* 𝒪[A.Fp] := (A.ιF.comp (algebraMap (𝓞 F) F)).codRestrict _ fun c => val_int_le A c
  refine (A.O_def _).2 (hβ.map_of_comp_eq φ A.ιE (RingHom.ext fun c => ?_))
  show algebraMap A.Fp A.Ep (A.ιF (algebraMap (𝓞 F) F c)) = A.ιE (algebraMap (𝓞 F) E c)
  rw [← A.compat, ← IsScalarTower.algebraMap_apply]

private theorem smul_mem_O (A : LocAt F E sig p) {y : A.Fp} (hy : y ∈ (valuation A.Fp).integer) {z : A.Ep} (hz : z ∈ A.O) :
    y • z ∈ A.O := (A.O_def _).2 (((A.O_def _).1 hz).smul (⟨y, hy⟩ : 𝒪[A.Fp]))

theorem approx (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (U : ∀ p, AddSubgroup (A p).Ep)
    (hU : ∀ p, IsOpen (U p : Set (A p).Ep)) (hf : {p | (U p : Set (A p).Ep) ≠ ((A p).O : Set (A p).Ep)}.Finite)
    (x : ∀ p, (A p).Ep) (hx : {p | x p ∉ (A p).O}.Finite) : ∃ t : E, ∀ p, (A p).ιE t - x p ∈ U p := by
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨s, β, hβ⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hsum : ∀ p (f : s → F), (A p).ιE (∑ i, f i • β i) = ∑ i, (A p).ιF (f i) • (A p).ιE (β i) := fun p f => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, map_mul, (A p).compat, Algebra.smul_def]
  have hb : ∀ p, ∃ b : s → (A p).Fp, ∑ i, b i • (A p).ιE (β i) = x p := fun p => by
    refine (Submodule.mem_span_range_iff_exists_fun _).1 (?_ : x p ∈ _)
    have : (⊤ : Submodule (A p).Fp (A p).Ep) ≤ Submodule.span (A p).Fp (Set.range fun i => (A p).ιE (β i)) := by
      rw [← (A p).span, Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      rw [← β.sum_repr t, hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact this trivial
  choose b hb using hb
  have hc : ∀ p i, ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y, valuation (A p).Fp y ≤ valuation (A p).Fp ((A p).ιF (algebraMap (𝓞 F) F c)) →
      y • (A p).ιE (β i) ∈ U p := fun p i => by
    haveI := (A p).lf
    haveI := (A p).top
    haveI : ContinuousSMul (A p).Fp (A p).Ep := IsModuleTopology.toContinuousSMul _ _
    have hcont : Continuous fun y : (A p).Fp => y • (A p).ιE (β i) := continuous_id.smul continuous_const
    exact exists_small (A p) (W := (fun y : (A p).Fp => y • (A p).ιE (β i)) ⁻¹' (U p))
      (((hU p).preimage hcont).mem_nhds (by simp))
  choose c hc0 hc using hc
  let S := (hf.union hx).toFinset
  have hf' := fun i => UpperTheory.Reformulated.B.ApproximationIntegralOutsideFinset.approxF A S (∏ q ∈ S, c q i) (Finset.prod_ne_zero_iff.2 fun q _ => hc0 q i) fun p => b p i
  choose f hf1 hf2 using hf'
  refine ⟨∑ i, f i • β i, fun p => ?_⟩
  rw [hsum]
  by_cases hp : p ∈ S
  · rw [← hb p, ← Finset.sum_sub_distrib]
    refine sum_mem fun i _ => ?_
    rw [← sub_smul]
    refine hc p i _ ((hf1 i p hp).trans ?_)
    rw [← Finset.mul_prod_erase S _ hp, map_mul, map_mul, map_mul]
    exact mul_le_of_le_one_right' (val_int_le _ _)
  · have hp' : ¬ ((U p : Set (A p).Ep) ≠ ((A p).O : Set (A p).Ep) ∨ x p ∉ (A p).O) := fun h => hp (by simpa [S] using h)
    push Not at hp'
    have : ∑ i, (A p).ιF (f i) • (A p).ιE (β i) - x p ∈ (A p).O :=
      sub_mem (sum_mem fun i _ => smul_mem_O _ (hf2 i p hp) (mem_O _ (hβ i))) hp'.2
    rw [← SetLike.mem_coe, hp'.1]
    exact this

end UpperTheory.Prune

theorem UpperTheory.Prune.fundamentalExactSequence_continuity_all_theories : ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum.adm6 D :=
  fun D U hU hf x hx => UpperTheory.Prune.approx D.s.atP U hU hf x hx
