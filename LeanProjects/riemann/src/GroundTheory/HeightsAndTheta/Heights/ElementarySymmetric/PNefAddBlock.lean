import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]

omit [∀ k, Fintype (ι k)] in

theorem red_component (f : NumbersDVR.MRing ι ℤ) (b : K → ℕ) :
    Bridge.GeoNum.red p (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b (Bridge.GeoNum.red p f) := by
  ext d
  simp only [Bridge.GeoNum.red, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isMultiProjPrime_comap_red {Q : Ideal (NumbersDVR.MRing ι (ZMod p))}
    (hQ : NumbersDVR.IsMultiProjPrime Q) :
    Geo.IsMultiProjPrime (Q.comap (Bridge.GeoNum.red p)) := by
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ _, ?_, (Bridge.GeoNum.isRelevant_comap_iff p Q).mpr hQ.relevant⟩
  rw [← Bridge.isMultiHomogIdeal_iff]
  intro f hf b
  rw [Ideal.mem_comap, red_component]
  exact hQ.multiHomog _ hf b

theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

theorem rename_mem_mCoordIdeal {K K' : Type} [Fintype K] [Fintype K'] (j : K ↪ K')
    {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω']
    (y : (Σ k, ι' (j k)) → Ω) (Y : (Σ k', ι' k') → Ω')
    (hY : ∀ k i, Y ⟨j k, i⟩ = algebraMap Ω Ω' (y ⟨k, i⟩))
    {f : Geo.MRing (fun k => ι' (j k))} (hf : f ∈ Geo.mCoordIdeal y) :
    rename (FieldNumbers.blockIncl j ι') f ∈ Geo.mCoordIdeal Y := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] MvPolynomial K' Ω' :=
    ((rename j).toRingHom.comp (MvPolynomial.map (algebraMap Ω Ω'))).toIntAlgHom
  have e : (Geo.mConeMap Y).comp (rename (FieldNumbers.blockIncl j ι')) =
      φ.comp (Geo.mConeMap y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, i⟩
    simp [φ, Geo.mConeMap, FieldNumbers.blockIncl, hY]
    change _ = (rename j) (MvPolynomial.map (algebraMap Ω Ω')
      ((aeval fun p => C (y p) * X p.fst) (X ⟨k, i⟩)))
    simp
  have h := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply] at h
  rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  rw [h, hf, map_zero]

theorem proof (hPF : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) : NefAddBlock.Statement := by
  classical
  intro K _ ι _ κ _ Ω Ω' _ _ _ y z a hnef W' hW' hyz hchar hdim
  have hhor : ¬ Geo.IsHorizontal W' := fun h => hchar (by
    unfold Geo.charOf
    rw [(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h]
    rfl)
  set p := Geo.charOf W' with hp_def
  have hp : p.Prime := Geo.charOf_prime hW'.1 hhor
  have : Fact p.Prime := ⟨hp⟩
  have hpW' : (C (p : ℤ) : Geo.MRing (addBlockIdx ι κ)) ∈ W' := Inter.C_charOf_mem W'
  rw [← Bridge.intNum_map_eq_geoNum p 1 W' hW' hpW' hdim (fun _ => addBlockDeg a)]
  obtain ⟨hQ', hQ'd⟩ := map_red p hW' hpW' 1 hdim
  set Q' := W'.map (Bridge.GeoNum.red p) with hQ'_def
  let j : K ↪ Option K := Function.Embedding.some
  have hpull : (fun _ : Fin 1 => FieldNumbers.pullDeg j a) = fun _ => addBlockDeg a := by
    funext _ o
    cases o with
    | none =>
      exact Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => Option.some_ne_none k hk)
    | some k =>
      exact Option.some_injective _ |>.extend_apply a 0 k
  set Q := FieldNumbers.contractPrime j Q' with hQ_def
  have hQ : NumbersDVR.IsMultiProjPrime Q :=
    FieldNumbers.isMultiProjPrime_contractPrime j (addBlockIdx ι κ) hQ'
  have hle := FieldNumbers.ContractRelDimLe.proof (ZMod p) K (Option K) j (addBlockIdx ι κ) Q' hQ'
  rw [hQ'd] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h0 := FieldNumbers.ProjectionFormulaContracted.full (ZMod p) K (Option K) j
      (addBlockIdx ι κ) Q' hQ' 1 hQ'd hlt (fun _ => a)
    rw [← hpull, h0]
  · obtain ⟨-, h1⟩ := hPF (ZMod p) K (Option K) j (addBlockIdx ι κ) Q' hQ' 1 hQ'd heq (fun _ => a)
    rw [← hpull, h1]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [Bridge.GeoNum.intNum_eq_geoNum_comap p 1 Q hQ heq (fun _ => a)]
    let y' : (Σ k, addBlockIdx ι κ (j k)) → Ω := y
    have hnef' : Geo.NefOnFibres (Geo.mCoordIdeal y') a := hnef
    refine hnef' (Q.comap (Bridge.GeoNum.red p)) (isMultiProjPrime_comap_red p hQ) ?_ ?_ ?_
    · intro f hf
      rw [Ideal.mem_comap, hQ_def, FieldNumbers.contractPrime, Ideal.mem_comap, Bridge.GeoNum.red,
        ← map_rename]
      exact Ideal.mem_map_of_mem _ (hyz (rename_mem_mCoordIdeal j y' (addBlockPt y z)
        (fun _ _ => rfl) hf))
    · refine ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero ?_
      rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]
      exact Q.zero_mem
    · rw [ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q)]
      exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q 1).mp heq

end NefAddBlock

end GroundTheory.Heights₂.Heights
