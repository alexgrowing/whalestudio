import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.GammaZetaNablaCancel

noncomputable section

open NumberField
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

namespace RegH

theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ ≠ τ := by
  intro h
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    exact RingHom.ext fun x => by simpa using congrArg (fun f : E →+* ℂ => f x) h
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]; exact hr
  · rw [e, ComplexEmbedding.isReal_iff.1 hr]; exact hr

theorem conj_eq_conjugate {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl

theorem mk_conj {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    InfinitePlace.mk ((starRingEnd ℂ).comp τ) = InfinitePlace.mk τ := by
  rw [conj_eq_conjugate, InfinitePlace.mk_conjugate_eq]

theorem dec_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk ((starRingEnd ℂ).comp τ)).embedding) =
      !decide (τ = (InfinitePlace.mk τ).embedding) := by
  rw [mk_conj]
  have hne := conj_ne τ
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [e]
    simp [hne]
  · rw [e, ← conj_eq_conjugate]
    have : τ ≠ (starRingEnd ℂ).comp τ := fun h => hne h.symm
    simp [this]

theorem infOf_not {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) :
    PositivityTheory.RgBcC.infOf lam (!s) a = -PositivityTheory.RgBcC.infOf lam s a := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_im {n : ℕ} (lam : Fin n → ℤ) (s : Bool) (a : Fin n) : (PositivityTheory.RgBcC.infOf lam s a).im = 0 := by
  cases s <;> simp [PositivityTheory.RgBcC.infOf]

theorem infOf_sep {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) (a b : Fin n) (hab : a ≠ b) :
    (1 : ℝ) ≤ ‖PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b‖ := by
  have key : ∀ a b : Fin n, a < b → (1 : ℝ) ≤ ((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) := by
    intro a b h
    have h1 : lam b ≤ lam a := hl h.le
    have h2 : (a : ℕ) + 1 ≤ (b : ℕ) := h
    have h1' : (lam b : ℝ) ≤ lam a := by exact_mod_cast h1
    have h2' : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast h2
    linarith
  have e : ∀ a b : Fin n, PositivityTheory.RgBcC.infOf lam s a - PositivityTheory.RgBcC.infOf lam s b =
      ((if s then 1 else -1 : ℂ)) * ((((lam a : ℝ) - (a : ℕ)) - ((lam b : ℝ) - (b : ℕ)) : ℝ) : ℂ) := by
    intro a b
    simp only [PositivityTheory.RgBcC.infOf]
    push_cast
    ring
  have hs : ‖(if s then 1 else -1 : ℂ)‖ = 1 := by cases s <;> simp
  rcases lt_or_gt_of_ne hab with h | h
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (key a b h).trans (le_abs_self _)
  · rw [e, norm_mul, hs, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := key b a h
    exact le_abs.mpr (Or.inr (by linarith))

theorem infOf_inj {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (s : Bool) :
    Function.Injective (PositivityTheory.RgBcC.infOf lam s) := by
  intro a b h
  by_contra hab
  have := infOf_sep lam hl s a b hab
  rw [h, sub_self, norm_zero] at this
  norm_num at this

end RegH

open RegH

theorem regDom : RegDom := by
  intro E _ _ _ n l
  refine ⟨fun τ => ⟨?_, ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · intro x hx
    simp only [mOf, Multiset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact infOf_im _ _ _
  · simp only [mOf]
    rw [mk_conj, show decide ((starRingEnd ℂ).comp τ = (InfinitePlace.mk τ).embedding) =
        !decide (τ = (InfinitePlace.mk τ).embedding) from by rw [← dec_conj τ, mk_conj], Multiset.map_map]
    congr 1
    funext a
    exact infOf_not _ _ _
  · simp only [mOf]
    exact Multiset.Nodup.map (infOf_inj _ (l _).anti _) Finset.univ.nodup
  · intro x hx y hy hxy
    simp only [mOf, Multiset.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact le_trans (by norm_num) (infOf_sep _ (l _).anti _ a b hab)

theorem reg_of (h : GelfInj) : Reg := by
  intro E _ _ _ n l χ hχ
  have e : mOf χ = mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) := by
    funext τ
    simp only [mOf]
    exact h n _ _ (hχ _ _)
  rw [e]
  exact regDom E n l

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
