import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StatementsVerticalGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalGenericDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem map_mem_map_iff {W : Ideal (MRing ι)} (hW : W.IsPrime) (hh : IsHorizontal W) (x : MRing ι) :
    MvPolynomial.map (Int.castRingHom ℚ) x ∈ W.map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ x ∈ W := by
  classical
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = MvPolynomial.map (Int.castRingHom ℚ) := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hdisj : Disjoint (S : Set (MRing ι)) W := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmW
    have h0 : m ∈ W.comap (C : ℤ →+* MRing ι) := hmW
    rw [hh, Ideal.mem_bot] at h0
    exact zero_notMem_nonZeroDivisors (h0 ▸ hm)
  have h := IsLocalization.under_map_of_isPrime_disjoint S (MRingOver ℚ ι) hW hdisj
  constructor
  · intro hx
    rw [← h]
    show algebraMap (MRing ι) (MRingOver ℚ ι) x ∈ Ideal.map (algebraMap (MRing ι) (MRingOver ℚ ι)) W
    rw [hφ]
    exact hx
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

theorem isMultiHomog_map [DecidableEq K] {x : MRing ι} {e : K → ℕ} (h : NumbersDVR.IsMultiHomog x e) :
    NumbersDVR.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℚ) x) e := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end VerticalGenericDeg

theorem VerticalGenericDeg.proof : VerticalGenericDeg.Statement := by
  intro K _ ι _ P W d p b f g hP hp hV hW hPW
  classical
  set φ : MRing ι →+* MRingOver ℚ ι := MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hPN : NumbersDVR.IsMultiProjPrime P := (Bridge.isMultiProjPrime_iff P).mpr hP.2.1
  have : P.IsPrime := hPN.isPrime
  have hWN : NumbersDVR.IsMultiProjPrime W := (Bridge.isMultiProjPrime_iff W).mpr hW.2.1
  have : W.IsPrime := hWN.isPrime
  have hWh : IsHorizontal W := hW.2.2.1
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpW : (C (p : ℤ) : MRing ι) ∉ W := by
    intro h
    have h0 : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := h
    rw [hWh, Ideal.mem_bot] at h0
    exact hp0 h0
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfN : NumbersDVR.IsMultiHomog f bf := (Bridge.isMultiHomog_iff f bf).mpr hf
  have hgN : NumbersDVR.IsMultiHomog g bg := (Bridge.isMultiHomog_iff g bg).mpr hg

  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre W ‹_› hPW hW.2.1.2.2 hpW
  obtain ⟨u', v', e, e', hu', hv', hdeg, hu'W, hv'W, huv'⟩ :=
    NumbersDVR.exists_form_pair hPN.multiHomog hPW hfN hgN hV.num_not_mem hV.den_not_mem hu hv huv

  have hkey : ∀ W' : Ideal (MRingOver ℚ ι), W'.IsPrime → W.map φ ≤ W' → NumbersDVR.IsRelevant W' →
      NumbersDVR.divCycle (W.map φ) (φ v') W' = NumbersDVR.divCycle (W.map φ) (φ u') W' := by
    intro W' hW' hle hrel
    have hPle : P ≤ W'.comap φ := fun x hx => hle (Ideal.mem_map_of_mem φ (hPW hx))
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
    have h3 : φ s * φ v' - φ t * φ u' ∈ W.map φ := by
      rw [← map_mul, ← map_mul, ← map_sub]
      exact Ideal.mem_map_of_mem φ (hPW h2)
    have hs' : φ s ∉ W' := hs
    have ht' : φ t ∉ W' := ht
    exact NumbersDVR.divCycle_eq_of_mul_sub_mem hs' ht' h3
  have hrat : NumbersDVR.ratDiv (W.map φ) (φ v') (φ u') = 0 := by
    funext W'
    show NumbersDVR.divCycle _ _ W' - NumbersDVR.divCycle _ _ W' = 0
    by_cases h1 : NumbersDVR.divCycle (W.map φ) (φ v') W' = 0
    · by_cases h2 : NumbersDVR.divCycle (W.map φ) (φ u') W' = 0
      · rw [h1, h2, sub_zero]
      · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h2
        rw [hkey W' a1 a2 a3, sub_self]
    · obtain ⟨a1, a2, a3⟩ := NumbersDVR.le_and_isRelevant_of_divCycle_ne_zero h1
      rw [hkey W' a1 a2 a3, sub_self]

  have hX : IsProjVarF (W.map φ) 1 := isProjVarF_map_of_isArithVar (D := 1) hW
  have hXN : NumbersDVR.IsMultiProjPrime (W.map φ) := (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hdim : ringKrullDim (MRingOver ℚ ι ⧸ W.map φ) = ((0 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hX.2, Nat.zero_add]
  have hv'Q : φ v' ∉ W.map φ := fun h => hv'W ((VerticalGenericDeg.map_mem_map_iff ‹_› hWh v').mp h)
  have hu'Q : φ u' ∉ W.map φ := fun h => hu'W ((VerticalGenericDeg.map_mem_map_iff ‹_› hWh u').mp h)
  have hab : ∀ k, (e' k : ℤ) - e k = b k := by
    intro k
    have h1 : (e' k : ℤ) + bg k = e k + bf k := by exact_mod_cast congrFun hdeg k
    have h2 : (bf k : ℤ) - bg k = b k := congrFun hb k
    rw [← h2]
    linarith
  have hR := NumbersDVR.IntNumRatSection.proof FieldNumbers.CutRational.full ℚ K ι 0 (W.map φ) hXN hdim
    (![] : Fin 0 → K → ℤ) b (φ v') (φ u') e' e (VerticalGenericDeg.isMultiHomog_map hv')
    (VerticalGenericDeg.isMultiHomog_map hu') hv'Q hu'Q hab
  have hsnoc : (Fin.snoc (α := fun _ => K → ℤ) (![] : Fin 0 → K → ℤ) b) = fun _ : Fin 1 => b := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, hrat] at hR
  unfold genDeg
  rw [hR]
  simp [NumbersDVR.cycEval]

end GroundTheory.Heights₂.Heights.NineStatements
