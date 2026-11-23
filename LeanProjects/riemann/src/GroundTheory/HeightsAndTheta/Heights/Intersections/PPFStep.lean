import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFSecRed
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isSmoothHerm_of_isPullHerm' {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem arithDim_lt_of_lt {P Q : Ideal (MRing ι)} {d d₀ : ℕ} (hP : IsArithVar P d) (hQ : IsArithVar Q d₀)
    (hle : P ≤ Q) (hne : P ≠ Q) : d₀ < d := by
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  have := hP.2.1.1
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
  have h2 : ringKrullDim (MRing ι ⧸ Q) ≤
      ringKrullDim ((MRing ι ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P f}) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_) ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hfQ, mul_zero]
    · intro z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk P z), rfl⟩
  rw [hP.2.2.2] at h1
  rw [hQ.2.2.2] at h2
  have h3 : ((d₀ + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    le_trans (by gcongr) h1
  have h4 : ((d₀ + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast h3
  have h5 : d₀ + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
  omega

end SlopeTestRemainingChoices

theorem PFStep.proof (hSec : PFSecRed.Statement) (hVert : PFVert.Statement) (hInt : PFIntZero.Statement)
    (hHor : PFHoriz.Statement) (hSum : PFFibreSum.Statement) (hIm : ImageArithStatement) (hCM : ContractMixedStatement) : PFStep.Statement := by
  intro I hI r hr
  refine hSec I hI r ?_
  intro K _ ι _ K' _ ι' _ κ v P' d G J L L' N s a hv hP' hP hJ hL hL' hN ha hs hsP
  have hP1 : IsArithVar P' (d + r + 1) := hP'
  have hsec : IsSectionOn P' (N (Fin.last r)) s := ⟨a, ha, hs, hsP⟩
  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact isSmoothHerm_of_isPullHerm' hv (hL i) (hL' i)
    | right i => rw [Fin.append_right]; exact hN _
  have hR := (hI K' ι').2.2 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) s a hP1 hM (hN _) ha hs hsP
  rw [← Fin.append_snoc, Fin.snoc_init_self] at hR
  refine hR.trans ?_
  rw [recR_eq, hInt K ι K' ι' κ v P' d r L L' (Fin.init N) (N (Fin.last r)) s hv hP1 hP hL hL', sub_zero, cycR,
    ← hSum K ι K' ι' κ v P' d r G J N s a hv hP1 hP hJ ha hs hsP, finsum_mem_mul]
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · have hWa : IsArithVar W (d + r) := (divSuppArith K' ι' P' (d + r) (N (Fin.last r)) s W hP1 hsec hW).1 hh
    by_cases hd : imageZ v W = imageZ v P'
    · rw [if_pos hh, if_pos ⟨hh, hd⟩,
        hHor I r hr K ι K' ι' κ v P' W d G J L L' (Fin.init N) hv hWa hd hP hJ hL hL' (fun j => hN _)]
      exact (mul_assoc _ _ _).symm
    · rw [if_pos hh, if_neg (fun h => hd h.2), mul_zero, zero_mul]
      obtain ⟨d₀, -, hd₀⟩ := hIm K ι K' ι' κ v W (d + r) hP.1 hv hWa
      have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono (le_sup_left.trans hW.1.1.2)
      rw [hCM I hI K ι K' ι' κ v W d₀ d r L L' (Fin.init N) hv hWa hd₀
        (arithDim_lt_of_lt hP hd₀ hle (Ne.symm hd)) hL hL' (fun j => hN _), mul_zero]
  · rw [if_neg hh, if_neg (fun h => hh h.1),
      hVert K ι K' ι' κ v P' d r L L' (Fin.init N) s a W hv hP1 hP hL' hs hsP hW hh]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
