import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.Statement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions MvPolynomial NumberField IsDedekindDomain

namespace Formalism.L2.Geo

structure Dat (D : D7) (Lev : Type) where
  S : letI := D.host.cmStar; HSpace D.host.E
  κ : Lev
  j : ℕ
  two_le : letI := D.host.cmStar; 2 ≤ S.rank
  sigOK : letI := D.host.cmStar; S.SigOK
  j_le : letI := D.host.cmStar; j ≤ S.rank
  hsig : letI := D.host.cmStar; ∀ τ : D.what₂.Tau, S.sig (DV.tauEmb D τ) = (j, S.rank - j)

namespace Dat

variable {D : D7} {Lev : Type} (w : Dat D Lev)

def N : ℕ := letI := D.host.cmStar; w.S.rank

def Indef : Prop := 1 ≤ w.j ∧ w.j < w.N

def Defin : Prop := w.j = w.N

theorem j_le_N : w.j ≤ w.N := w.j_le

end Dat

def jcl (D : D7) (j : ℕ) : ℕ := max 1 (min j D.R.m)

theorem one_le_jcl (D : D7) (j : ℕ) : 1 ≤ jcl D j := le_max_left _ _

theorem jcl_le (D : D7) (j : ℕ) : jcl D j ≤ D.R.m := by
  have := D.R.two_le_m
  unfold jcl; omega

theorem jcl_eq (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : jcl D j = j := by
  unfold jcl; omega

theorem sigW_sum (D : D7) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
  have := D.R.m_add_three_le_k
  simp only [Ranks.sigW, Ranks.r]; omega

theorem two_le_r (D : D7) : 2 ≤ D.R.r := by
  have := D.R.m_add_three_le_k; have := D.R.two_le_m
  unfold Ranks.r; omega

def datW (D : D7) {Lev : Type} (κ : Lev) (j : ℕ) : Dat D Lev :=
  letI := D.host.cmStar
  { S := D.sp.W (jcl D j)
    κ := κ
    j := (D.R.sigW (jcl D j)).1
    two_le := by
      rw [D.sp.W_rank _ (one_le_jcl D j) (jcl_le D j)]; exact two_le_r D
    sigOK := D.sp.W_sig _
    j_le := by
      rw [D.sp.W_rank _ (one_le_jcl D j) (jcl_le D j)]
      have := sigW_sum D (one_le_jcl D j) (jcl_le D j); omega
    hsig := fun τ => by
      rw [D.sp.W_sigval _ (one_le_jcl D j) (jcl_le D j), D.sp.W_rank _ (one_le_jcl D j) (jcl_le D j)]
      have := sigW_sum D (one_le_jcl D j) (jcl_le D j)
      ext
      · rfl
      · simp only; omega }

theorem datW_N (D : D7) {Lev : Type} (κ : Lev) (j : ℕ) : (datW D κ j).N = D.R.r := by
  letI := D.host.cmStar
  exact D.sp.W_rank _ (one_le_jcl D j) (jcl_le D j)

theorem datW_j (D : D7) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (datW D κ j).j = (D.R.sigW j).1 := by
  simp only [datW, jcl_eq D h1 h2]

def degFlL (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • MvPolynomial.lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem degFlL_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    degFlL ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [degFlL, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def chernOf (Tau : Type) [Fintype Tau] (N : ℕ) (vol : ℝ) : MvPolynomial (DV.Rt Tau N) ℝ →ₗ[ℝ] ℝ := by
  classical exact vol • degFlL Tau N

def orbR {ι : Type} [Fintype ι] {p q : ℕ} (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ))
    (z z' : Formalism.DegreeFormula.DomI ι p q) : Prop :=
  ∃ γ ∈ Γ, Formalism.DegreeFormula.moebI γ (z : ι → Matrix (Fin p) (Fin q) ℂ) = z'

def XCc (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) : Type :=
  Quot (orbR Γ)

def PlL (D : D7) (p : ℕ) : Type :=
  {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}

def wtL (D : D7) (p : ℕ) (v : PlL D p) : ℝ :=
  (eWL D.what₂.LL v.1 : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) /
    (Real.log (p : ℝ) * (Module.finrank ℚ D.what₂.LL : ℝ))

def finPl (D : D7) (p : ℕ) [hp : Fact p.Prime] : Fintype (PlL D p) :=
  Fintype.subtype (finite_places_over (K := D.what₂.LL) p hp.out).choose
    (finite_places_over (K := D.what₂.LL) p hp.out).choose_spec

theorem wtL_eq (D : D7) (p : ℕ) (v : PlL D p) :
    wtL D p v = lw D.what₂.LL v.1 * (eWL D.what₂.LL v.1 : ℝ) / Real.log p := by
  unfold wtL lw
  by_cases h1 : Real.log (p : ℝ) = 0
  · simp [h1]
  have h2 : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := D.what₂.LL)).ne'
  field_simp

theorem wtL_sum (D : D7) (p : ℕ) [hp : Fact p.Prime] : (letI := finPl D p; ∑ la, wtL D p la) = 1 := by
  letI := finPl D p
  have hS := (finite_places_over (K := D.what₂.LL) p hp.out).choose_spec
  have h := sum_lw_e (K := D.what₂.LL) p hp.out _ hS
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  simp only [wtL_eq]
  rw [← Finset.sum_div]
  have e : ∑ la : PlL D p, lw D.what₂.LL la.1 * (eWL D.what₂.LL la.1 : ℝ) = Real.log p := by
    rw [← h]
    exact (Finset.sum_subtype _ hS (fun w => lw D.what₂.LL w * (eWL D.what₂.LL w : ℝ))).symm
  rw [e, div_self hlog]

theorem plL_ne (D : D7) (p : ℕ) [hp : Fact p.Prime] : Nonempty (PlL D p) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have := wtL_sum D p
  simp at this

theorem wtL_nonneg (D : D7) (p : ℕ) (la : PlL D p) : 0 ≤ wtL D p la := by
  unfold wtL
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
    (mul_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))

theorem datW_indef (D : D7) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < D.R.m) : (datW D κ j).Indef := by
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, ?_⟩
  · rw [datW_j D κ h1 h2.le]; simp only [Ranks.sigW]; omega
  · rw [datW_j D κ h1 h2.le, datW_N]; simp only [Ranks.sigW, Ranks.r]; omega

theorem datW_S (D : D7) {Lev : Type} (κ : Lev) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (datW D κ j).S = (letI := D.host.cmStar; D.sp.W j) := by
  simp only [datW, jcl_eq D h1 h2]

theorem dat_ext (D : D7) {Lev : Type} (w w' : Dat D Lev) (hS : w.S = w'.S) (hκ : w.κ = w'.κ) : w = w' := by
  obtain ⟨S, κ, j, a, b, c, d⟩ := w
  obtain ⟨S', κ', j', a', b', c', d'⟩ := w'
  simp only at hS hκ
  subst hS; subst hκ
  have : j = j' := by
    have τ : D.what₂.Tau := D.eTau.symm 1
    have := (d τ).symm.trans (d' τ)
    exact (Prod.mk.inj this).1
  subst this; rfl

end Formalism.L2.Geo
