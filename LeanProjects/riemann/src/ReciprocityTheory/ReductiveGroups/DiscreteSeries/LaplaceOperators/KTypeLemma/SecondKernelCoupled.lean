import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.InnerCompactWordActionAdjoint
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.DatumLinkStd

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Irr

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def k2cS (μ : Fin n → ℝ) : ℝ := ∑ k ∈ range (n + 1), kirrPs k μ

def k2cT (A : Fin n → Fin n → Module.End ℂ X) : Module.End ℂ X := ∑ k ∈ range (n + 1), kirrH A k

end Irr

section Main

theorem lowestKType_casimir_cone (n : ℕ) : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsKIrrHW ε E (lowK ε lam) V →
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) →
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
      (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) → StrictAnti lam →
      GapAtLeast ε lam h →
      max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
        (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) < h →
      1 ≤ pOf ε → 1 ≤ qOf ε →
      ∀ (μ : Fin n → ℝ) (w : D), w ∈ genSub E V → w ≠ 0 → IsKHWVec ε E μ w →
        InRootCone (μ - lowK ε lam) := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hbig hp hq ν w hw hw0 hk
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  have hstd : StdGap ε lam := ⟨hanti, h, hgap, lt_of_le_of_lt (le_max_left _ _) hbig⟩
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 := lt_of_le_of_lt (le_max_right _ _) hbig
    have e : (min (pOf ε) (qOf ε) : ℝ) = (S7.q0 ε : ℝ) := by simp [S7.q0, Nat.cast_min]
    rw [e] at h1
    have : 0 ≤ (n : ℝ) * S7.q0 ε := by positivity
    nlinarith [Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))]
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := exists_isMu hlam
  obtain ⟨ι, hcoef, -, hιK⟩ := datum_link_std hσ hD hV hc hVK hlam hgap hstd h8 (le_min hp hq) T hμ
  obtain ⟨hEM, hlow, hwt, hgen⟩ := k2vM lam μ hμ
  have hVst := hV.2.1
  have : FiniteDimensional ℂ V := hV.1
  have hw1 := lowestKType_vector_exists ε lam σ D E V hσ hD hV T ι hιK
  have hU := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hℓ : ∀ (a : Fin n) (v w : V), (w : D) = E a a v →
      submoduleEvaluationFunctional V (ι.symm T.w) w = ((lowK ε lam a : ℝ) : ℂ) * submoduleEvaluationFunctional V (ι.symm T.w) v := by
    intro a v w hw
    have e1 : submoduleEvaluationFunctional V (ι.symm T.w) w = inner ℂ ((ι.symm T.w : V) : D) (w : D) := rfl
    have e2 : submoduleEvaluationFunctional V (ι.symm T.w) v = inner ℂ ((ι.symm T.w : V) : D) (v : D) := rfl
    rw [e1, e2, hw, ← hU a a rfl, hw1.1 a, inner_smul_left, Complex.conj_ofReal]
  obtain ⟨u, hu, hTu⟩ := Cone.lift0 hVst hD.glRep hU (f := fun _ => w) (fun _ => hw) (fun _ => hk)
  have hA := Cone.isKRelation_compactWordAction hVst hD.glRep
  set θ := sθ V (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) with hθ
  have hex : ∃ l, KirrLow ε l ∧ θ (kirrWord (Cone.compactWordAction ε E V hVst) u l) ≠ 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨W, h1, h2, h3⟩ := Cone.exists_stable hVst (eMM μ) (phiMM μ) (submoduleEvaluationFunctional V (ι.symm T.w)) _
      (wordSpan_isKStable hA hu) (fun x hx =>
        (Submodule.span_le (p := LinearMap.ker θ)).mpr (by rintro _ ⟨l, hl, rfl⟩; exact hno l hl) hx)
    have h4 := lowestKType_trace_integral ε lam H σ D E V hσ hD hV hint hanti T μ ι hμ hcoef W h2 h3 u
      (h1 (kirrWord_mem (l := []) u (by simp [KirrLow])))
    rw [hTu] at h4
    have hn : 0 < n := lt_of_lt_of_le hp (by
      simpa [pOf] using Finset.card_filter_le (univ : Finset (Fin n)) fun a => ε a = true)
    exact hw0 (congrFun h4 ⟨0, hn⟩)
  obtain ⟨l, hl, hx⟩ := hex
  set x := kirrWord (Cone.compactWordAction ε E V hVst) u l with hxd
  obtain ⟨c, hc0⟩ := Function.ne_iff.mp hx
  have hwt2 : ∀ a, eMM μ a a (θ x c) =
      (((kirrWt ν l - lowK ε lam + (lam + rho n)) a : ℝ) : ℂ) • θ x c := by
    intro a
    have h1 := congrFun (sθ_sA ε E V hVst (eMM μ) hEM (phiMM μ) (lam + rho n) (lowK ε lam) hwt
      (submoduleEvaluationFunctional V (ι.symm T.w)) hℓ a x) c
    have h2 := congrFun (congrArg θ (word_isWeightVector hA hu.1 l hl a)) c
    rw [← hxd, Cone.compactWordAction, LinearMap.sub_apply, map_sub, map_smul, Pi.sub_apply, h1, Cone.sθ_sC,
      Pi.add_apply, Cone.tensV_eq] at h2
    simp only [Pi.smul_apply, ← hθ] at h2
    have h3 : eMM μ a a (θ x c) = (kirrWt ν l a : ℂ) • θ x c -
        ((lowK ε lam a - (lam + rho n) a : ℝ) : ℂ) • θ x c := by rw [← h2]; abel
    rw [h3, ← sub_smul]
    congr 1
    simp only [Pi.add_apply, Pi.sub_apply]; push_cast; ring
  have h5 := Cone.verma_weight (eMM μ) hEM (phiMM μ) (lam + rho n) hlow hwt hgen hc0 hwt2
  have h6 := root_swap_eq_neg (weight_sub_mem_rootCone ν l hl) h5
  convert h6 using 1
  abel

end Main

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
