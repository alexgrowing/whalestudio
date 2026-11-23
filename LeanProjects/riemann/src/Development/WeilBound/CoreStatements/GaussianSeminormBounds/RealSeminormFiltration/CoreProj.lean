import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem graded_orth {σ : Type} [Fintype σ] (L : Submodule ℂ (MvPolynomial σ ℂ))
    (hL : ∀ d, ∀ z ∈ L, homogeneousComponent d z ∈ L) (u : MvPolynomial σ ℂ) :
    ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
  have key : ∀ d, ∀ u ∈ homog σ d, ∃ y ∈ L, ∀ z ∈ L, fockInner z (u - y) = 0 := by
    intro d u hu
    obtain ⟨y, hy, h⟩ := PI.FHS.exists_orth (L ⊓ homog σ d) d inf_le_right u
    refine ⟨y, hy.1, fun z hz => ?_⟩
    rw [← PI.FHS.fockInner_hc_left z (u - y) (Submodule.sub_mem _ hu hy.2)]
    exact h _ ⟨hL d z hz, homogeneousComponent_mem d z⟩
  choose! f hf using fun d => key d (homogeneousComponent d u) (homogeneousComponent_mem d u)
  refine ⟨∑ i ∈ Finset.range (u.totalDegree + 1), f i, Submodule.sum_mem _ fun i _ => (hf i).1, fun z hz => ?_⟩
  have e : u - ∑ i ∈ Finset.range (u.totalDegree + 1), f i =
      ∑ i ∈ Finset.range (u.totalDegree + 1), (homogeneousComponent i u - f i) := by
    rw [Finset.sum_sub_distrib, sum_homogeneousComponent]
  rw [e, PI.FHS.fockInner_sum_right]
  exact Finset.sum_eq_zero fun i _ => (hf i).2 z hz

theorem unit_homog {p q r : ℕ} (a b : Ix p q) (i : ℕ) (P : Pol p q r 0) (hP : P ∈ homog (Ix p q × Ix r 0) i) :
    ∃ e, fockAct1 p q r 0 (Eab a b) P ∈ homog (Ix p q × Ix r 0) e := by
  by_cases hab : sameBlock a b
  · exact ⟨i, (gradedOscillatorProperty p q r 0).1 _ (PI.FockOneDegW.isKC_Eab hab) i P hP⟩
  have hP' : P.IsHomogeneous i := hP
  rw [PI.FockOneDegW.fockAct1_Eab_apply]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd trivial hab
  · refine ⟨1 + (1 + i), Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply]
      exact (isHomogeneous_X ℂ _).mul ((isHomogeneous_X ℂ _).mul hP')
    · exact c.elim0
  · refine ⟨i - 1 - 1, Submodule.sum_mem _ fun c _ => ?_⟩
    rcases c with c | c
    · rw [PI.FHS.omE_apply_of_ne (by simp)]
      simp only [raiB, lowB, linePos, if_true, Bool.false_eq_true, if_false, LinearMap.neg_apply]
      exact Submodule.neg_mem _ (hP'.pderiv.pderiv)
    · exact c.elim0
  · exact absurd trivial hab

theorem gen_graded {p q r : ℕ} (x : Pol p q r 0) (dx : ℕ) (hx : x ∈ homog (Ix p q × Ix r 0) dx) :
    ∀ d, ∀ z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}),
      homogeneousComponent d z ∈ genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) := by
  set L := genG (fockAct1 p q r 0) (Submodule.span ℂ {x}) with hLdef
  have hxL : x ∈ L := by
    rw [hLdef, genG, Submodule.mem_sInf]
    exact fun N hN => hN.1 (Submodule.mem_span_singleton_self x)
  have hst : ∀ W, ∀ z ∈ L, fockAct1 p q r 0 W z ∈ L := by
    intro W z hz
    rw [hLdef, genG, Submodule.mem_sInf] at hz ⊢
    exact fun N hN => hN.2 W z (hz N hN)
  have hhom : ∀ e d, ∀ w ∈ homog (Ix p q × Ix r 0) e, w ∈ L → homogeneousComponent d w ∈ L := by
    intro e d w hw hwL
    rw [homogeneousComponent_of_mem hw]
    split_ifs
    · exact hwL
    · exact L.zero_mem
  let L' : Submodule ℂ (Pol p q r 0) := ⨅ d, L.comap (homogeneousComponent d)
  have mem' : ∀ z, z ∈ L' ↔ ∀ d, homogeneousComponent d z ∈ L := fun z => by
    simp only [L', Submodule.mem_iInf, Submodule.mem_comap]
  have hle : L ≤ L' := by
    rw [hLdef, genG]
    refine sInf_le ⟨?_, ?_⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem']
      exact fun d => hhom dx d x hx hxL
    · intro W z hz
      rw [act_eq_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
      rw [← sum_homogeneousComponent z, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨e, he⟩ := unit_homog a b i _ (homogeneousComponent_mem i z)
      rw [mem']
      exact fun d => hhom e d _ he (hst _ _ ((mem' z).1 hz i))
  exact fun d z hz => (mem' z).1 (hle hz) d

theorem proj_gen {p q r : ℕ} (x : FV p q r 0) (dx : ℕ) (hx : (x : Pol p q r 0) ∈ homog (Ix p q × Ix r 0) dx) :
    genG (fvAct1 p q r 0) (Submodule.span ℂ {x}) ⊔ (genG (fvAct1 p q r 0) (Submodule.span ℂ {x}))ᗮ = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨y, hy, h⟩ := graded_orth (σ := Ix p q × Ix r 0) _ (gen_graded (p := p) (q := q) (r := r) x dx hx) u
  let y' : FV p q r 0 := y
  have h1 : y' ∈ genG (fvAct1 p q r 0) (Submodule.span ℂ {x}) := hy
  have h2 : u - y' ∈ (genG (fvAct1 p q r 0) (Submodule.span ℂ {x}))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact h z hz
  have := Submodule.add_mem_sup h1 h2
  rwa [add_sub_cancel] at this

end PositivityTheory.KReal

end
