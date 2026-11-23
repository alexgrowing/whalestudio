import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefEmbed
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PoleMatch
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section SlopeTestRemainingChoices

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem ccA_sigLam_eq : sigLam ε Ψ v₀ = closRep (rreg ε) (closGen (smE ε (rreg ε)) (datumV ε Ψ v₀)) := rfl

theorem ccA_sqInt (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    Formalism.MainNotions.S.IsSqIntOn ε (closRep (rreg ε) (closGen (smE ε (rreg ε)) (datumV ε Ψ v₀))) :=
  (isDS_sigLam hgap hP hv₀).2.2.2.2.1

theorem ccA_fdeg_eq (w : Hlam ε Ψ v₀) : Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w =
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (closRep (rreg ε) (closGen (smE ε (rreg ε)) (datumV ε Ψ v₀))) w := rfl

theorem ccA_fdeg_pos (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {w : Hlam ε Ψ v₀} (hw : w ≠ 0) :
    0 < Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w := by
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam (sigLam ε Ψ v₀) (isDS_sigLam hgap hP hv₀)
  rw [fdegOf_of_isFdeg' hd hw]
  exact hd.1

end SlopeTestRemainingChoices

theorem ccA_arith {a b r r₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : a / b ≤ r) (h2 : b / a ≤ r₂)
    (hm : r * r₂ = 1) : a / b = r := by
  have hr : 0 < r := lt_of_lt_of_le (div_pos ha hb) h1
  refine le_antisymm h1 ?_
  rw [div_le_iff₀ ha] at h2
  rw [le_div_iff₀ hb]
  nlinarith

theorem ccA_ratio_mul (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} (hgap : StdGap ε lam)
    (hgap' : StdGap ε lam') (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    ratioF dual lam s * ratioF (!dual) lam' s = 1 := by
  cases dual
  · subst hlam'
    simp only [ratioF, shiftF, Bool.not_false, cond_true, cond_false] at hgap' ⊢
    rw [mul_comm]
    exact ratioVd_add_single_mul s hgap.1.injective hgap'.1.injective
  · subst hlam'
    simp only [ratioF, shiftF, Bool.not_true, cond_true, cond_false] at hgap' ⊢
    have h := ratioVd_add_single_mul (μ := lam - Pi.single s 1) s hgap'.1.injective
      (by rw [sub_add_cancel]; exact hgap.1.injective)
    rw [sub_add_cancel] at h
    exact h

theorem ccA_shift_back (dual : Bool) {lam lam' : Fin n → ℝ} (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    lam = shiftF (!dual) lam' s := by
  cases dual <;> subst hlam' <;> simp [shiftF]

theorem ccA_ratio_zero (dual : Bool) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam) (s : Fin n)
    (hsing : ¬ Function.Injective (shiftF dual lam s)) : ratioF dual lam s = 0 := by
  cases dual
  · obtain ⟨s', hs', heq⟩ := (not_injective_shift_iff hgap.1.injective s 1
      (ν := shiftF false lam s) (by simp [shiftF])
      (fun x hx => by simp [shiftF, Pi.single_eq_of_ne hx])).1 hsing
    simp only [ratioF, cond_false, ratioV]
    exact prod_eq_zero hs' (by rw [heq, sub_self, zero_div])
  · obtain ⟨s', hs', heq⟩ := (not_injective_shift_iff hgap.1.injective s (-1)
      (ν := shiftF true lam s) (by simp [shiftF, sub_eq_add_neg])
      (fun x hx => by simp [shiftF, Pi.single_eq_of_ne hx])).1 hsing
    simp only [ratioF, cond_true, ratioVd]
    exact prod_eq_zero hs' (by rw [sub_eq_add_neg (lam s), heq, sub_self, zero_div])

theorem cc_gk (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {h h' : ℝ} (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) (hh' : GapAtLeast ε lam' h') (hth' : thrStar ε < h')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))) (hW' : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hG' : HasGelfandChar (smE ε (rreg ε)) lam' (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s) {w : Hlam ε Ψ v₀} (hw : w ≠ 0) {w' : Hlam ε Ψ' v₀'} (hw' : w' ≠ 0) :
    (∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι ∧
      (∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x) ∧
      ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f →
        ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), f = ι x) ∧
    Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ' v₀') w' / Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) (sigLam ε Ψ v₀) w =
      ratioF dual lam s := by
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  have hV := datumV_isKIrrHW hP hv₀
  have hV' := datumV_isKIrrHW hP' hv₀'
  have hc := datumV_casimir hP v₀
  have hc' := datumV_casimir hP' v₀'
  have hVK := datumV_kStable hP v₀
  have hVK' := datumV_kStable hP' v₀'
  have hSq := ccA_sqInt hgap hP hv₀
  have hSq' := ccA_sqInt hgap' hP' hv₀'

  obtain ⟨ι, hι, hιe⟩ := occ_exists dual hgap hP hv₀ hgap' hP' hv₀' hh hth hh' hth' hpos hpos' hW s hlam'
  obtain ⟨P, hPG, hPP, hPz, hP1, hP0⟩ := eigenProj_exists dual hσ hD hgap hV hc hVK hW (poleF dual lam s)
  have hPB := eigenProj_formB dual hσ hD hgap hV hc hVK hW (poleF dual lam s) hPG.1 hPz hP1 hP0
  have hptr := (pole_match dual hσ hD hsm hgap hV hc hVK hW hG).2 s P hPG hPP hPB hPz hP1 hP0
  have hιP : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P (ι x) = ι x :=
    fun x hx => hP1 _ (hι.1 x hx) (hιe x hx)
  obtain ⟨hle, heq⟩ := trace_ge dual hσ hD hsm hgap hV hc hVK hW hgap' hV' hc' hVK' hSq hSq' hPG hPP hPB hPz hptr hι hιP hw hw'

  have hlam := ccA_shift_back dual s hlam'
  obtain ⟨ι₂, hι₂, hιe₂⟩ := occ_exists (!dual) hgap' hP' hv₀' hgap hP hv₀ hh' hth' hh hth hpos' hpos hW' s hlam
  obtain ⟨P₂, hPG₂, hPP₂, hPz₂, hP1₂, hP0₂⟩ :=
    eigenProj_exists (!dual) hσ hD hgap' hV' hc' hVK' hW' (poleF (!dual) lam' s)
  have hPB₂ := eigenProj_formB (!dual) hσ hD hgap' hV' hc' hVK' hW' (poleF (!dual) lam' s) hPG₂.1 hPz₂ hP1₂ hP0₂
  have hptr₂ := (pole_match (!dual) hσ hD hsm hgap' hV' hc' hVK' hW' hG').2 s P₂ hPG₂ hPP₂ hPB₂ hPz₂ hP1₂ hP0₂
  have hιP₂ : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), P₂ (ι₂ x) = ι₂ x :=
    fun x hx => hP1₂ _ (hι₂.1 x hx) (hιe₂ x hx)
  obtain ⟨hle₂, -⟩ := trace_ge (!dual) hσ hD hsm hgap' hV' hc' hVK' hW' hgap hV hc hVK hSq' hSq hPG₂ hPP₂ hPB₂ hPz₂ hptr₂
    hι₂ hιP₂ hw' hw
  simp only [Complex.ofReal_re] at hle hle₂ heq
  rw [← ccA_fdeg_eq, ← ccA_fdeg_eq] at hle hle₂ heq
  have hEq := ccA_arith (ccA_fdeg_pos hgap' hP' hv₀' hw') (ccA_fdeg_pos hgap hP hv₀ hw) hle hle₂
    (ccA_ratio_mul dual hgap hgap' s hlam')
  refine ⟨⟨ι, hι, hιe, fun f hf hfe => ?_⟩, hEq⟩
  obtain ⟨x, hx, hPx⟩ := heq hEq.symm f hf
  exact ⟨x, hx, by rw [← hPx, hP1 f hf hfe]⟩

theorem cc_gk_singular (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) (s : Fin n)
    (hsing : ¬ Function.Injective (shiftF dual lam s)) :
    ∀ f ∈ tensSub (genSub E V), eeF dual E f = poleF dual lam s • f → f = 0 := by
  exact (pole_zero dual hσ hD hsm hgap hV hc hVK hW hG s).1 (ccA_ratio_zero dual hgap s hsing)

end ReciprocityTheory.ChartRestriction.DS
