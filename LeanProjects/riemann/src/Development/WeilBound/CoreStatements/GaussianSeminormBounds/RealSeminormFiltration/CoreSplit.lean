import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreHarm

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {p q r s : ℕ}

theorem chiTr_Eab (c : ℂ) (a b : Ix p q) : chiTr c (Eab a b) = if a = b then c else 0 := by
  unfold chiTr Eab
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.trace_single_eq_of_ne _ _ _ h]
    simp [h]

theorem minusPart_small {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) {d : ℕ} (hd : d < 2)
    {Q : MvPolynomial σ ℂ} (hQ : Q ∈ homog σ d) : minusPart A Q = 0 := by
  unfold minusPart
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rw [homogeneousComponent_of_mem hQ, if_neg (by omega), map_zero, map_zero]

theorem charSplit (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ) (W : Submodule ℂ (Pol p q r s))
    (hWd : W ≤ homog (Ix p q × Ix r s) d) (hW : KSt (units (fockAct1 p q r s)) W) :
    W.map (thMkC p q r s c) ≤ (W ⊓ polChi p q r s c).map (thMkC p q r s c) := by
  subst hc
  classical
  rintro _ ⟨x, hx, rfl⟩
  let D : Ix p q → Ix p q → Module.End ℂ (Pol p q r s) := fun a b =>
    fockAct1 p q r s (Eab a b) - (if a = b then ((c0 : ℚ) : ℂ) else 0) • 1
  have hDa : ∀ a b w, D a b w =
      fockAct1 p q r s (Eab a b) w + (-(if a = b then ((c0 : ℚ) : ℂ) else 0)) • w := by
    intro a b w
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hDW : ∀ a b, sameBlock a b → ∀ w ∈ W, D a b w ∈ W := by
    intro a b hab w hw
    rw [hDa]
    exact W.add_mem (hW a b hab w hw) (W.smul_mem _ hw)
  let K : Submodule ℂ (Pol p q r s) :=
    ⨆ ab : {ab : Ix p q × Ix p q // sameBlock ab.1 ab.2}, W.map (D ab.1.1 ab.1.2)
  have hKW : K ≤ W := iSup_le fun ab => by
    rintro _ ⟨w, hw, rfl⟩
    exact hDW _ _ ab.2 w hw
  have hKc : K ≤ coinvSub (act1 p q r s) (chiTr ((c0 : ℚ) : ℂ)) := iSup_le fun ab => by
    rintro _ ⟨w, -, rfl⟩
    refine Submodule.mem_iSup_of_mem (Eab ab.1.1 ab.1.2) ⟨w, ?_⟩
    rw [chiTr_Eab]
    rfl
  obtain ⟨y, hy, hz⟩ := PI.FHS.exists_orth K d (hKW.trans hWd) x
  have hzW : x - y ∈ W := W.sub_mem hx (hKW hy)
  refine ⟨x - y, ⟨hzW, ?_⟩, ?_⟩
  · refine (mem_polChi_iff _ _).2 fun a b hab => ?_
    have hw := hDW a b hab _ hzW
    have hba : sameBlock b a := PI.FHS.sameBlock_symm hab
    have h0 := hz (D b a (D a b (x - y)))
      (Submodule.mem_iSup_of_mem (⟨(b, a), hba⟩ : {ab : Ix p q × Ix p q // sameBlock ab.1 ab.2})
        ⟨_, hw, rfl⟩)
    have h1 : fockInner (D a b (x - y)) (D a b (x - y)) = 0 := by
      have e : ∀ w : Pol p q r s, fockInner w (D a b (x - y)) = fockInner (D b a w) (x - y) := by
        intro w
        rw [hDa, hDa, PI.FHS.fockInner_add_right, PI.FHS.fockInner_add_left, PI.FHS.fockInner_smul_right,
          PI.FHS.fockInner_smul_left, PI.FockOneDegW.fock_kernel_adjoint p q r s a b hab]
        congr 2
        by_cases h : a = b
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [e, h0]
    have h2 := PI.FHS.fockInner_self_eq_zero h1
    rw [hDa, neg_smul, add_neg_eq_zero] at h2
    exact h2
  · rw [map_sub]
    have : thMkC p q r s ((c0 : ℚ) : ℂ) y = 0 := (Submodule.Quotient.mk_eq_zero _).2 (hKc hy)
    rw [this, sub_zero]

theorem polChi_small (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ)
    (hd : (d : ℚ) < degW (cPair r s) (fun _ : Ix p q => c0)) {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) d) (hχ : g ∈ polChi p q r s c) : g = 0 := by
  by_contra h0
  have := (highestWeightDegree_le p q r s).1 d (fun _ => c0) g hg ⟨h0, (mem_polChi_iff_hw c c0 hc g).1 hχ⟩
  linarith

theorem th_small (c : ℂ) (c0 : ℚ) (hc : c = c0) (d : ℕ)
    (hd : (d : ℚ) < degW (cPair r s) (fun _ : Ix p q => c0)) {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) d) : thMkC p q r s c g = 0 := by
  obtain ⟨e, ⟨he, hχ⟩, h⟩ := charSplit c c0 hc d _ le_rfl (homogeneous_stable_first_action d) ⟨g, hg, rfl⟩
  rw [← h, polChi_small c c0 hc d hd he hχ, map_zero]

theorem th_plus1 (c : ℂ) {Z : Mat p q} (hZ : IsPC Z) (g : Pol p q r s) :
    thMkC p q r s c (plusPart (fockAct1 p q r s Z) g) = - thMkC p q r s c (minusPart (fockAct1 p q r s Z) g) := by
  have h := (gradedOscillatorProperty p q r s).2.2.1 Z hZ g
  have htr : Z.trace = 0 :=
    Finset.sum_eq_zero fun a _ => hZ a a (by cases a <;> trivial)
  have h0 : thMkC p q r s c (fockAct1 p q r s Z g) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_iSup_of_mem Z ⟨g, ?_⟩)
    simp [chiTr, htr, act1]
  rw [h, map_add] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem th_next (c : ℂ) (c0 : ℚ) (hc : c = c0) (d0 : ℕ)
    (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    (homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) ≤
      (harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) := by
  have hs := harmonicSplitting_holds p q r s true false rfl d0
  have hR : (Submodule.span ℂ (raised p q r s true false d0)).map (thMkC p q r s c) = ⊥ := by
    rw [Submodule.map_span, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨Q, hQ, (⟨-, Z, hZ, rfl⟩ | ⟨h, -⟩)⟩, rfl⟩
    · rw [th_plus1 c hZ, neg_eq_zero]
      rcases lt_or_ge d0 2 with h2 | h2
      · rw [minusPart_small _ h2 hQ, map_zero]
      · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' h2
        rw [PI.FHS.minusPart_of_mem hQ]
        refine th_small c c0 hc e ?_ (homogeneousComponent_mem e _)
        rw [← hd]
        push_cast
        linarith
    · exact absurd h (by simp)
  have hK : KSt (units (fockAct1 p q r s)) (homog (Ix p q × Ix r s) (d0 + 2) ⊓ harm1 p q r s) :=
    fun a b hab x hx => ⟨homogeneous_stable_first_action _ a b hab x hx.1, harmonic_stable_first_action a b hab x hx.2⟩
  have h1 := charSplit c c0 hc (d0 + 2) _ inf_le_left hK
  conv_lhs => rw [hs]
  rw [Submodule.map_sup, hR, sup_bot_eq]
  refine h1.trans (Submodule.map_mono ?_)
  rintro x ⟨⟨a, b⟩, e⟩
  exact ⟨⟨b, e⟩, a⟩

end PositivityTheory.KReal

end
