import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnWhittakerTransformKeepsLaterLaw
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic PositivityTheory.ThKEnd.Two

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

structure Pre (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : Prop where
  cont : Continuous f
  left : ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, f (ratGL E a γ * g) = f g
  law : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g

theorem pre_top {f : GA E a → ℂ} (hc : Continuous f) (hl : ∀ γ g, f (ratGL E a γ * g) = f g) : Pre ψ (a - 1) f := by
  refine ⟨hc, fun γ _ => hl γ, fun k hk y g => ?_⟩
  have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  obtain rfl : y = 0 := Subsingleton.elim _ _
  rw [show dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad E) = 0 by simp [dot], AddChar.map_zero_eq_one, one_mul, blkU, posU_zero, one_mul]

theorem Pre.per (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hf : Pre ψ m f) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a m m)) fun x => ψ (-dot (eLast a m) x) * f (blkU x * g) :=
  per_coef hψ _ hf.cont (fun c g' => hf.left _ (isMir_blkU c) g') g

theorem pre_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hma : m + 1 < a) (hf : Pre ψ (m + 1) f) : Pre ψ m (colT ψ (m + 1) f) := by
  refine ⟨?_, fun γ hγ g => ?_, fun k hk y g => ?_⟩
  · exact GlobalTheory.T.continuous_quotientAverage_periodic_family _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) (GA E a)
      (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1))
      ((hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
        (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))) fun g γ hγ y => (hf.per hψ g).2 γ hγ y
  · rw [colT, GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g]
    congr 1
    funext t
    let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
    rw [Finset.sum_eq_single s0 (fun s _ hs => ?_) fun h => absurd (Finset.mem_univ _) h]
    · rw [show eLast (E := E) a (m + 1) s0 = 1 by simp [eLast, s0], one_mul, hγ _ _ (Or.inl (le_refl m))]
      have ht := t.2.1
      simp only [eLast, Matrix.one_apply]
      by_cases h : (t.1.1 : ℕ) = m
      · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
      · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
    · rw [eLast, if_neg, zero_mul]
      intro e
      have h2 := s.2.2
      exact hs (Subtype.ext (Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))))
  · rcases Nat.lt_or_ge (m + 1) k with h1 | h1
    · simp only [colT, coefF]
      rw [← avg_const_mul]
      congr 1
      funext x
      rw [← mul_assoc (blkU x), blkU_mul_blkU h1 x y, mul_assoc, hf.law k h1, dot_eLast_shift h1 x y]
      ring
    · obtain rfl : k = m + 1 := by omega
      have hT := GlobalTheory.T.quotientAverage_translate_invariant _ _ (isCoLat_ratV E _) _ (hf.per hψ g) y
      simp only [colT, coefF]
      rw [← hT, ← avg_const_mul]
      congr 1
      funext x
      have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hd, show (blkU (x + y) : GA E a) = blkU x * blkU y from posU_add _ x y, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul,
        mul_assoc (blkU x)]
      congr 2
      abel

theorem whit_pre (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Pre ψ m f → Pre ψ 0 (whit ψ m f) := by
  induction m with
  | zero => exact fun _ f hf => hf
  | succ m ih => exact fun h f hf => ih (Or.inl (by omega)) (pre_colT hψ (by omega) hf)

theorem whit_add' (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Pre ψ m f → Pre ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have e : colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := funext fun g => by
      simp only [colT, coefF, mul_add]
      exact GlobalTheory.T.quotientAverage_add_of_periodic _ _ (isCoLat_ratV E _) _ _ (hf.per hψ g) (hf'.per hψ g)
    rw [whit_succ, whit_succ, whit_succ, e]
    exact ih (Or.inl (by omega)) (pre_colT hψ (by omega) hf) (pre_colT hψ (by omega) hf')

section Mult

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [T2Space X] {Γ : AddSubgroup X}

instance : LocallyCompactSpace (Multiplicative X) := inferInstanceAs (LocallyCompactSpace X)
instance : SecondCountableTopology (Multiplicative X) := inferInstanceAs (SecondCountableTopology X)
instance : T2Space (Multiplicative X) := inferInstanceAs (T2Space X)

theorem lat_mult (h : IsCoLat Γ) : Lat Γ.toSubgroup := by
  have := h.1
  haveI : SecondCountableTopology Γ := TopologicalSpace.Subtype.secondCountableTopology _
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, a, b⟩ := h.2
  exact ⟨‹Countable Γ›, h.1, K, a, b⟩

theorem avg_eq_of_isAv (h : IsCoLat Γ) [MeasurableSpace (Multiplicative X)] [hB : BorelSpace (Multiplicative X)] {H : Type} [Mul H]
    {ι : Multiplicative X → H} {f c : H → ℂ} (ha : IsAv Γ.toSubgroup ι f c) (x : H)
    (hp : Per Γ fun y => f (ι (Multiplicative.ofAdd y) * x)) : avg Γ (fun y => f (ι (Multiplicative.ofAdd y) * x)) = c x := by
  letI : MeasurableSpace X := ‹MeasurableSpace (Multiplicative X)›
  haveI : BorelSpace X := ⟨hB.1⟩
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice X Γ h
  have h4 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average X Γ h μ 𝓕 h1 h2 _ hp).2.2.2
  rw [h3, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h4
  rw [← h4]
  exact (ha μ 𝓕
    { map_mul_left_eq_self := h1.map_add_left_eq_self, lt_top_of_isCompact := h1.lt_top_of_isCompact, open_pos := h1.open_pos } ⟨h2.1, h2.2, h2.3⟩ h3 x).symm

end Mult

end PositivityTheory.ThKEnd.Cusp

end
