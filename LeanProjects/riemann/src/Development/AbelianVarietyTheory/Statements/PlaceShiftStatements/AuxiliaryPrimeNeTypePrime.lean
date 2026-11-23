import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SetAtOfSizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem rec_iff (large₂ : SizeData₂ D) : Rec large₂ ↔ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ ∧ HostHyp D :=
  ⟨fun h => ⟨h.size, h.host⟩, fun h => ⟨h.1, h.2, rfl, h.1.2.1.2.2.2.2.2.2.1.2.2.2.2.2.1⟩⟩

theorem rec_fam {eps : ℝ} (he : 0 < eps) (Fm : FamP eps) (h : GlobalTheory.BigTop.FamHyp Fm) :
    ∃ x₀ : ℝ, ∀ x (hx : Fm.x1 < x), x₀ ≤ x → ∀ i, GlobalTheory.BigTop.Pt Fm x hx i → Rec (Fm.L x i) := by
  obtain ⟨x₀, H⟩ := GlobalTheory.BigTop.Fun.SetAtModel.sizeRows_fam he Fm h
  exact ⟨x₀, fun x hx h0 i p => (rec_iff _).2 ⟨H x hx h0 i, p.host⟩⟩

theorem auxiliary_prime_ne_type_prime {large₂ : SizeData₂ D} (h : Rec large₂) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := h.size.2.2.2.2.2.2.2.2.1
  have h2 := (h.size.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k k).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  rw [← e] at h2
  nlinarith

theorem exists_grid {large₂ : SizeData₂ D} (h : Rec large₂) (C : Formalism.L2.Host.CharFrame D) (h1 : D.host.pde % LevelStarExponents.condE D = 1)
    (h2 : D.host.pde' % LevelStarExponents.condE D = 1) (sc : GlobalTheory.ChiGrid.Consts) :
    ∃ Lc : LevCh D Unit, Lc.C = C ∧ Lc.Is () ∧ Nonempty (GridData Lc sc) := by
  obtain ⟨Pm, -⟩ := h.size.1
  exact GlobalTheory.ChiGridModel.exists_levCh_gridData C sc Pm.g_mod h1 h2 (auxiliary_prime_ne_type_prime h)

theorem not_gBig_false (ε : ℝ) (H : ∀ x₀ : ℝ, ∃ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε ∧ x₀ ≤ large₂.sc.x ∧ Rec large₂ ∧
    Nonempty (Formalism.L2.Host.CharFrame D) ∧ D.host.pde % LevelStarExponents.condE D = 1 ∧ D.host.pde' % LevelStarExponents.condE D = 1) :
    ¬ GBig fun _ _ _ _ _ => False := by
  rintro ⟨c, hc⟩
  obtain ⟨C0, x₀, h⟩ := hc ε c le_rfl
  obtain ⟨D, large₂, a, b, r, ⟨C⟩, h1, h2⟩ := H x₀
  obtain ⟨Lc, -, hL, ⟨G⟩⟩ := exists_grid r C h1 h2 ⟨1, c, large₂.sc.b⟩
  exact h C0 le_rfl D large₂ a b r Unit Lc () hL G

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨c, h⟩ := h
  obtain ⟨c', h'⟩ := h'
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hL G,
      h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hL G⟩⟩

theorem tower_numbers (i j : Fin D.R.m) : e0 D i j + pp D j = eTop D i j + qq D j ∧
    halfRank D i j = h0 D i j + pp D j + qq D j ∧ pp D j + qq D j = D.R.m - 1 - j ∧ 1 ≤ e0 D i j ∧ e0 D i j < h0 D i j ∧
    botBig D i j = e0 D i j + h0 D i j ∧ botSmall D i j + e0 D i j = h0 D i j ∧ eTop D i j + qq D j ≤ halfRank D i j ∧
    halfRank D i j ≤ bigN D := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := odd_sLen D
  obtain ⟨a, ha⟩ := D.R.m_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have r2 := D.R.m_add_three_le_k
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have hj := j.2
  have b1 : (j.1 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
  have b2 : (i.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
  have b3 : rankV D (i + 1) (j + 1) = D.R.r + (j.1 + 1) * D.R.t + (i.1 + 1) * sLen D := rfl
  have b4 : bigN D = D.R.k + (D.R.m * D.R.t + D.R.m * sLen D + D.R.m) := by simp only [bigN]; ring
  simp only [e0, h0, pp, qq, eTop]
  omega

variable {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}

theorem base_tuple (hL : Lc.Is μ₀) : twPl G μ₀ = ∅ ∧ Qn G μ₀ = 1 ∧ modT G μ₀ = SqNum.condE G.pl := by
  have h : twPl G μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    simp only [twPl, locPl, Finset.mem_filter, Finset.mem_union] at hw
    exact (hL.Q_ram μ₀ w).2 (Or.inl (hw.1.resolve_left hw.2)) (by rw [hL.xi_base]; intro x _; rfl)
  simp [Qn, modT, h]

theorem Qn_ne_zero (t : T) : Qn G t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot

example : ThA G μ₀ fun _ => μ₀ := fun _ h => absurd rfl h

end GlobalTheory.SqTop.Model

end
