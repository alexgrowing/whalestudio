import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVerticalTwistGenDeg
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PVerticalGenericDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalTwistGenDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem intNum_snoc_eq_zero {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n p : ℕ} {b : K → ℤ} {f g : MRing ι}
    (hP : IsArithVar P (n + 1 + 1)) (hp : p.Prime) (hV : IsVerticalDivisorAt P p b f g)
    (L : Fin n → K → ℤ) :
    NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
      (Fin.snoc (α := fun _ => K → ℤ) L b) = 0 := by
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hPN : NumbersDVR.IsMultiProjPrime P := (Bridge.isMultiProjPrime_iff P).mpr hP.2.1
  have : P.IsPrime := hPN.isPrime
  have hPh : IsHorizontal P := hP.2.2.1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpP : (C (p : ℤ) : MRing ι) ∉ P := by
    intro h
    have h0 : (p : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hPh, Ideal.mem_bot] at h0
    exact hp0 h0
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfN : NumbersDVR.IsMultiHomog f bf := (Bridge.isMultiHomog_iff f bf).mpr hf
  have hgN : NumbersDVR.IsMultiHomog g bg := (Bridge.isMultiHomog_iff g bg).mpr hg

  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre P ‹_› le_rfl hP.2.1.2.2 hpP
  obtain ⟨u', v', e, e', hu', hv', hdeg, hu'P, hv'P, huv'⟩ :=
    NumbersDVR.exists_form_pair hPN.multiHomog le_rfl hfN hgN hV.num_not_mem hV.den_not_mem hu hv huv

  have hkey : ∀ W' : Ideal (MRingOver ℚ ι), W'.IsPrime → P.map φ ≤ W' → NumbersDVR.IsRelevant W' →
      NumbersDVR.divCycle (P.map φ) (φ v') W' = NumbersDVR.divCycle (P.map φ) (φ u') W' := by
    intro W' hW' hle hrel
    have hPle : P ≤ W'.comap φ := fun x hx => hle (Ideal.mem_map_of_mem φ hx)
    have hrel' : IsRelevant (W'.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel k
      refine ⟨i, fun h => hi ?_⟩
      have h' : φ (X ⟨k, i⟩) ∈ W' := h
      rwa [hφ, map_X] at h'
    have hpW' : (C (p : ℤ) : MRing ι) ∉ W'.comap φ := by
      intro h
      have hu : IsUnit (φ (C (p : ℤ))) := by
        rw [hφ, map_C]
        exact (isUnit_iff_ne_zero.mpr (by simpa using hp0)).map C
      exact hW'.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    obtain ⟨s, t, hs, ht, hst⟩ := hV.unit_off_fibre _ (Ideal.comap_isPrime φ W') hPle hrel' hpW'
    have h1 : g * (s * v' - t * u') ∈ P := by
      have e1 : g * (s * v' - t * u') = u' * (s * f - t * g) - s * (u' * f - v' * g) := by ring
      rw [e1]
      exact P.sub_mem (P.mul_mem_left _ hst) (P.mul_mem_left _ huv')
    have h2 : s * v' - t * u' ∈ P := (‹P.IsPrime›.mem_or_mem h1).resolve_left hV.den_not_mem
    have h3 : φ s * φ v' - φ t * φ u' ∈ P.map φ := by
      rw [← map_mul, ← map_mul, ← map_sub]
      exact Ideal.mem_map_of_mem φ h2
    have hs' : φ s ∉ W' := hs
    have ht' : φ t ∉ W' := ht
    exact NumbersDVR.divCycle_eq_of_mul_sub_mem hs' ht' h3
  have hrat : NumbersDVR.ratDiv (P.map φ) (φ v') (φ u') = 0 := by
    funext W'
    show NumbersDVR.divCycle _ _ W' - NumbersDVR.divCycle _ _ W' = 0
    by_cases h1 : NumbersDVR.divCycle (P.map φ) (φ v') W' = 0
    · by_cases h2 : NumbersDVR.divCycle (P.map φ) (φ u') W' = 0
      · rw [h1, h2, sub_zero]
      · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h2
        rw [hkey W' a1 a2 a3, sub_self]
    · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h1
      rw [hkey W' a1 a2 a3, sub_self]

  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hv'Q : φ v' ∉ P.map φ := fun h => hv'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh v').mp h)
  have hu'Q : φ u' ∉ P.map φ := fun h => hu'P ((NineStatements.VerticalGenericDeg.map_mem_map_iff ‹_› hPh u').mp h)
  have hab : ∀ k, (e' k : ℤ) - e k = b k := by
    intro k
    have h1 : (e' k : ℤ) + bg k = e k + bf k := by exact_mod_cast congrFun hdeg k
    have h2 : (bf k : ℤ) - bg k = b k := congrFun hb k
    rw [← h2]
    linarith
  have hR := NumbersDVR.IntNumRatSection.proof FieldNumbers.CutRational.full ℚ K ι n (P.map φ) hXN hX.2
    L b (φ v') (φ u') e' e (NineStatements.VerticalGenericDeg.isMultiHomog_map hv')
    (NineStatements.VerticalGenericDeg.isMultiHomog_map hu') hv'Q hu'Q hab
  rw [hrat] at hR
  rw [hR]
  simp [NumbersDVR.cycEval]

end VerticalTwistGenDeg

theorem VerticalTwistGenDeg.proof : VerticalTwistGenDeg.Statement := by
  intro K _ ι _ P d a s b f g hP hs
  classical
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  obtain _ | n := d
  · unfold genDeg
    congr 1
    funext i
    exact i.elim0
  have hX : IsProjVarF (P.map φ) (n + 1) := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map φ) = (n + 1 : ℕ) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set F := intNumMultilinear (P.map φ) (n + 1) hXN.multiHomog hXN.relevant hd with hF

  have hposition : ∀ p ∈ s, ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = b p → F bs = 0 := by
    intro p hps bs i hi
    obtain ⟨hp, hV⟩ := hs p hps
    have h := FieldNumbers.IntNumSymm.full ℚ K ι (P.map φ) (n + 1) bs (Equiv.swap i (Fin.last n))
    rw [hF, intNumMultilinear_apply, ← h]
    have e1 : bs ∘ Equiv.swap i (Fin.last n) = Fin.snoc (α := fun _ => K → ℤ)
        (fun j => bs (Equiv.swap i (Fin.last n) (Fin.castSucc j))) (b p) := by
      funext j
      induction j using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [e1]
    exact VerticalTwistGenDeg.intNum_snoc_eq_zero hP hp hV _

  have hB : ∀ (bs : Fin (n + 1) → K → ℤ) (i : Fin (n + 1)), bs i = ∑ p ∈ s, b p → F bs = 0 := by
    intro bs i hi
    have e2 : bs = Function.update bs i (∑ p ∈ s, b p) := by rw [← hi, Function.update_eq_self]
    rw [e2, ← MultilinearMap.toLinearMap_apply, map_sum]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [MultilinearMap.toLinearMap_apply]
    exact hposition p hp _ i (Function.update_self _ _ _)
  have hg : ∀ c, genDeg P (n + 1) c = F (fun _ => c) := fun c => by
    rw [hF, intNumMultilinear_apply, genDeg]
  rw [hg, hg, show (fun _ : Fin (n + 1) => a + ∑ p ∈ s, b p) =
    (fun _ => a) + (fun _ => ∑ p ∈ s, b p) from rfl, F.map_add_univ,
    Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ]
  · intro S _ hS
    obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
      by_contra h
      exact hS (Finset.eq_univ_iff_forall.2 fun i => not_not.1 (not_exists.1 h i))
    exact hB _ i (by simp [Finset.piecewise, hi])
  · intro h
    exact absurd (Finset.mem_univ _) h

end GroundTheory.Heights₂.Heights.LowerBoundFree
