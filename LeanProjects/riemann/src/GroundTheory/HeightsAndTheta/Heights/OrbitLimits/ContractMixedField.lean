import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ContractMixedField

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [Fintype K'] in

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

omit [Fintype K] [Fintype K'] in

theorem isMultiProjPrime_imageVar {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := F) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

theorem exists_dim {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem mem_divSupp_of_ne_zero {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : divCycle P s W ≠ 0) : W ∈ divSupp P s := by
  classical
  by_contra hW
  apply h
  simp [divCycle, Finsupp.ofSupportFinite_coe, hW]

theorem component [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {V' : Ideal (MRingOver F ι')} {n d₀ : ℕ} (hV' : IsProjVarF V' (n + 1))
    (hI : IsProjVarF (imageVar F v V') d₀) {t : MRingOver F ι} {a : K → ℕ} (ht : IsMultiHomog t a)
    (htV : t ∉ imageVar F v V') {W : Ideal (MRingOver F ι')} (hW : divCycle V' (rename v t) W ≠ 0) :
    IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
  classical
  have hWs := mem_divSupp_of_ne_zero hW
  have hVW : V' ≤ W := le_sup_left.trans hWs.1.1.2
  have htW : rename v t ∈ W := hWs.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hrel : FieldNumbers.relDim V' = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    NumbersDVR.relDim_eq_of_ringKrullDim V' (n + 1) hV'.2
  have hW' : NumbersDVR.divCycle V' (rename v t) W ≠ 0 := by
    rw [← NumbersDVR.VocabDivCycle.proof F K' ι' V' (rename v t) W]
    exact_mod_cast hW
  obtain ⟨hWm, hWd⟩ := FieldNumbers.DivCycleSupport.full F K' ι' V' ((Bridge.isMultiProjPrime_iff V').mpr hV'.1)
    n hrel (Function.extend κ a 0) (rename v t)
    ((Bridge.isMultiHomog_iff _ _).mpr (isMultiHomog_rename hv ht)) (fun h => htV h) W hW'
  have hWm' := (Bridge.isMultiProjPrime_iff W).mp hWm
  refine ⟨⟨hWm', NumbersDVR.Numbers.ringKrullDim_eq_of_relDim W n hWd⟩, ?_⟩
  have hIm := isMultiProjPrime_imageVar hv hWm'
  obtain ⟨D, hKD, hD⟩ := exists_dim hIm
  have hle : imageVar F v V' ≤ imageVar F v W := Ideal.comap_mono hVW
  have : (imageVar F v V').IsPrime := hI.1.1
  have hdim := Inter.krullDim_quot_add_one_le hle (show t ∈ imageVar F v W from htW) htV
  rw [hD, hI.2] at hdim
  have hD' : D + 1 ≤ d₀ + Fintype.card K := by exact_mod_cast hdim
  refine ⟨D - Fintype.card K, by omega, hIm, ?_⟩
  rw [hD, Nat.sub_add_cancel hKD]

open Classical in

theorem intNum_eq_zero [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by
  intro n
  induction n with
  | zero =>
    intro V' d₀ bs _ _ h
    simp at h
  | succ n ih =>
    intro V' d₀ bs hV' hI hcount
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_gt (lt_of_le_of_lt (Nat.zero_le d₀) hcount))
    obtain ⟨a, ha⟩ : ∃ a : K → ℤ, bs i = pullDeg κ a := by
      by_contra h
      exact hi (if_neg h)
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = i :=
      ⟨Equiv.swap i (Fin.last n), Equiv.swap_apply_right _ _⟩
    rw [← FieldNumbers.IntNumSymm.full F K' ι' V' (n + 1) bs σ]
    have hlast : (bs ∘ σ) (Fin.last n) = pullDeg κ a := by
      show bs (σ (Fin.last n)) = _
      rw [hσ, ha]
    have e : bs ∘ σ = Fin.snoc (α := fun _ => K' → ℤ) (Fin.init (bs ∘ σ)) (pullDeg κ a) := by
      rw [← hlast]
      exact (Fin.snoc_init_self _).symm

    have hsum : (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) =
        (∑ j : Fin n, if ∃ a : K → ℤ, Fin.init (bs ∘ σ) j = pullDeg κ a then 1 else 0) + 1 := by
      rw [← Equiv.sum_comp σ (fun j => if ∃ a : K → ℤ, bs j = pullDeg κ a then 1 else 0),
        Fin.sum_univ_castSucc, hσ, if_pos ⟨a, ha⟩]
      rfl

    classical
    obtain ⟨bf, bg, f, g, hf, hg, hfI, hgI, hfg⟩ :=
      FieldNumbers.ExistsForm.full F K ι _ ((Bridge.isMultiProjPrime_iff _).mpr hI.1) a
    have hf' := (Bridge.isMultiHomog_iff f bf).mp hf
    have hg' := (Bridge.isMultiHomog_iff g bg).mp hg
    have hsec : IsRatSection V' (pullDeg κ a) (rename v f) (rename v g) := by
      refine ⟨Function.extend κ bf 0, Function.extend κ bg 0, isMultiHomog_rename hv hf',
        isMultiHomog_rename hv hg', fun h => hfI h, fun h => hgI h, fun k' => ?_⟩
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, hv.1.extend_apply, ← hfg]
      · simp only [ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg, Function.extend_apply' _ _ _ hk, Pi.zero_apply,
          Nat.cast_zero, sub_zero]
    have key := (NumbersDVR.IntNumIsFieldIntersection.full F K' ι').2 V' n (Fin.init (bs ∘ σ)) _ _ _ hV' hsec
    dsimp only at key
    rw [e, key]
    unfold cycEval Finsupp.sum
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Finsupp.mem_support_iff] at hW
    suffices h0 : NumbersDVR.intNum F W (Fin.init (bs ∘ σ)) = 0 by simp only [h0, mul_zero]
    have hcases : divCycle V' (rename v f) W ≠ 0 ∨ divCycle V' (rename v g) W ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hW
      simp [ratDiv, hc.1, hc.2]
    have hpair : IsProjVarF W n ∧ ∃ d₁ : ℕ, d₁ < d₀ ∧ IsProjVarF (imageVar F v W) d₁ := by
      rcases hcases with hc | hc
      · exact component hv hV' hI hf' (fun h => hfI h) hc
      · exact component hv hV' hI hg' (fun h => hgI h) hc
    obtain ⟨hWn, d₁, hd₁, hWI⟩ := hpair
    exact ih W d₁ _ hWn hWI (by omega)

end ContractMixedField

open ContractMixedField in

theorem contractMixedField : ReciprocityTheory.ChartRestriction.G.AI.I4.ContractMixedFieldStatement := by
  intro F _ K _ ι _ K' _ ι' _ J' hJ' κ v V' d₀ d r L N hv hV' hI hd
  classical
  rw [NumbersDVR.Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
    FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full J' hJ' V' (d + r) _ hV']
  refine intNum_eq_zero hv (d + r) V' d₀ _ hV' hI ?_
  rw [Fin.sum_univ_add]
  have h1 : ∀ j : Fin d, (if ∃ a : K → ℤ, Fin.append (fun j => pullDeg κ (L j)) N (Fin.castAdd r j) =
      pullDeg κ a then 1 else 0) = 1 := fun j => if_pos ⟨L j, by rw [Fin.append_left]⟩
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

end GroundTheory.Heights₂.Heights.Targets
