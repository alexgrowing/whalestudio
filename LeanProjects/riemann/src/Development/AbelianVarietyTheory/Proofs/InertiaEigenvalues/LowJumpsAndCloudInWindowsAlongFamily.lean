import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LetterWindows

theorem wj_eq_sz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) :
    Formalism.BasicNotions.wj D j ρ = ((Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ : ℚ) : ℝ) := by
  unfold Formalism.BasicNotions.wj Formalism.MainNotions.AdmissibleParameterJ.sz
  split_ifs <;> simp

theorem sz_eq (D : D7) (j : ℕ) (ρ : D.what₂.Tau) (h : j - 1 < D.R.m) :
    Formalism.MainNotions.AdmissibleParameterJ.sz D j ρ = (D.hc ρ).e ⟨j - 1, h⟩ := by
  unfold Formalism.MainNotions.AdmissibleParameterJ.sz
  rw [dif_pos h]

theorem low_abs (D : D7) (j : ℕ) (h : j - 1 < D.R.m) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.lowT D up j ρ) :
    ∃ a : Fin D.R.m, |(z : ℝ) - ((D.R.t : ℝ) - 1) / 2| =
      |((((D.hc ρ).b a - (D.hc ρ).e ⟨j - 1, h⟩ : ℚ)) : ℝ)| := by
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.lowJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    congr 1
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.lowT, Formalism.MainNotions.AdmissibleParameterJ.lowJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, sz_eq D j ρ h, Set.mem_setOf_eq, if_true] at hz
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    rw [abs_sub_comm ((((D.hc ρ).b a : ℚ)) : ℝ)]
    congr 1
    linarith

theorem cloud_val (D : D7) (j : ℕ) (up : Bool) (ρ : D.what₂.Tau) (z : ℤ)
    (hz : (z : ℚ) ∈ Formalism.MainNotions.AdmissibleParameterJ.cloudT D up j ρ) :
    ∃ a : Fin (D.R.k - 1),
      (if up then (z : ℝ) - ((D.R.t : ℝ) - 1) / 2 else ((D.R.t : ℝ) - 1) / 2 - z) =
        Formalism.BasicNotions.wj D j ρ + ((((D.hc ρ).v a : ℚ)) : ℝ) := by
  rw [wj_eq_sz]
  cases up
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.reflS, Formalism.MainNotions.AdmissibleParameterJ.cloudJ, Formalism.MainNotions.AdmissibleParameterJ.refl,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq] at hz
    simp only [Bool.false_eq_true, if_false, Set.mem_setOf_eq] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith
  · simp only [Formalism.MainNotions.AdmissibleParameterJ.cloudT, Formalism.MainNotions.AdmissibleParameterJ.cloudJ,
      Formalism.MainNotions.AdmissibleParameterJ.c0, Set.mem_setOf_eq, if_true] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun q : ℚ => (q : ℝ)) ha
    push_cast at ha' ⊢
    linarith

theorem base_window (D : D7) (L : SizeData₂ D) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) :
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes L,
      W0 ≤ Formalism.BasicNotions.wj D j ρ ∧ Formalism.BasicNotions.wj D j ρ ≤ W0 + L.etaSz + 1 := by
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · have htop' := htop
    simp only [Formalism.BasicNotions.Host.topPlaces, Finset.mem_image] at htop'
    obtain ⟨t, ht, hte⟩ := htop'
    have hw := L.win_top j hj1 hjm ρ ⟨t, ht⟩ hte.symm
    refine ⟨(L.bT ⟨t, ht⟩ : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ), ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr ⟨⟨t, ht⟩, rfl⟩)
    · have := Int.floor_le (L.sc.b' / L.sc.x)
      linarith [hw.1]
    · have := Int.lt_floor_add_one (L.sc.b' / L.sc.x)
      linarith [hw.2]
  · by_cases hthick : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick j hj1 hjm ρ hthick
      exact ⟨L.sc.b, Or.inl rfl, hw.1, hw.2⟩
    · have hthin : D.host.IsThin (D.eTau ρ : D.R.GG) :=
        ⟨(D.eTau ρ).2, htop, hthick⟩
      have hw := L.win_thin j hj1 hjm ρ hthin
      exact ⟨L.sc.w'' D.R.n, Or.inr (Or.inl rfl), hw.1, by linarith [hw.2]⟩

end GlobalTheory.LetterWindows

namespace GlobalTheory.LetterWindows

theorem lows_cloud_windows : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x a).R.m →
    ∀ (up : Bool) (ρ : (Fm.D x a).what₂.Tau),
    (∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.lowT (Fm.D x a) up j ρ →
      |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
      2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
        |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), ∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.cloudT (Fm.D x a) up j ρ →
      W0 ≤ (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
        W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1 := by
  intro eps Fm x hx a j hj1 hjm up ρ
  have h : j - 1 < (Fm.D x a).R.m := by omega
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := low_abs (Fm.D x a) j h up ρ z hz
    rw [hi]
    refine ⟨(Fm.L x a).be_close ρ i ⟨j - 1, h⟩, ?_⟩
    have := (Fm.params x hx a).lows_far ρ i ⟨j - 1, h⟩
    have e : 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) = 2 * (Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a) := by
      ring
    rw [e]
    exact this
  · obtain ⟨W0, hW0, hlo, hhi⟩ := base_window (Fm.D x a) (Fm.L x a) j hj1 hjm ρ
    refine ⟨W0, hW0, fun z hz => ?_⟩
    obtain ⟨i, hi⟩ := cloud_val (Fm.D x a) j up ρ z hz
    rw [hi]
    have hv := (Fm.L x a).cloud_v ρ i
    constructor <;> linarith [hv.1, hv.2]

end GlobalTheory.LetterWindows
