import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEvalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightPolynomialEvalStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem eval_formPoly_none_zero {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (PB.formPoly n a) =
      eval c (PB.formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, PB.killNone_formPoly]

theorem linA_zero_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (k : ℕ) :
    linA lam 0 ^ k = toA (linRoot lam ^ k) := by
  simp [linA, toA, map_pow]

theorem swapWt_uncurry {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) :
    (fun x : Ψ × Fin N => swapWt τ a b lam x.1 x.2) =
      (fun x : Ψ × Fin N => lam x.1 x.2) ∘ Equiv.swap (τ, a) (τ, b) := by
  funext ⟨σ, i⟩
  by_cases hσ : σ = τ
  · subst hσ
    by_cases h1 : i = a
    · subst h1; simp [swapWt]
    · by_cases h2 : i = b
      · subst h2; simp [swapWt]
      · simp [swapWt, Equiv.swap_apply_def, h1, h2]
  · simp [swapWt, Equiv.swap_apply_def, hσ]

theorem eval_rho_antisymDelta_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} :
    eval (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) ≠ 0 := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => ?_
  have hab : a < b := Finset.mem_Ioi.1 hb
  have hab' : (a : ℕ) < b := hab
  have : ((a : ℕ) : ℝ) < b := by exact_mod_cast hab'
  simp only [rhoWt]
  intro h
  linarith

end GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem Realis_PB_gapS_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {D : ℕ} {σ : Type} [Fintype σ]
    {S : PB.AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (II : IntersectionSystem) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (Re.PB II) = eval c ((Re.comap some).PB II) :=
  eval_formPoly_none_zero _ _ c

theorem AnSys_degPoly_gapS_zero {D : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys D (Option σ)) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) S.degPoly = eval c (S.comap some).degPoly :=
  eval_formPoly_none_zero _ _ c

theorem real_tower_I8 : PB.Antisymmetry → PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N)
    (R : RealTower T), R.Squares II → T.I8 II (hhFl Ψ N II) := by
  intro hA hAg hIn II hII Ψ _ _ N _ T R hSq B hB c τ a b hab hbj lam
  have hN : 2 ≤ N := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    omega
  have hjN : T.j ≤ N := T.j_lt.le
  have hdim : dimFl Ψ N = antisymDegree Ψ N := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  have harith : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1) := hdim ▸ (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  obtain ⟨d, S', K, _, ι, _, P, Re', ⟨F⟩, hPB, hdeg⟩ := hSq B c
  obtain ⟨⟨c₀, hc₀, hfl⟩, hprop⟩ := GlobalTheory.T.proportional' hIn Ψ N T.j hN hjN
  obtain ⟨-, hv⟩ := hprop (d + 1) S' F.dim F.unif
  have hnpos : 0 < R.n c := (GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0).1
  have hn0 : (R.n c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'

  have hvol : (R.n c : ℝ) * T.vol c = PB.volOf S' := by
    have h1 := GlobalTheory.T.real_tower_geometric_agreement hIn II hII Ψ N (T.M 2 c) (R.Sys c) (R.n c) (R.tie 2 c) (rhoWt : Wt Ψ N) 0
    have h2 := GlobalTheory.T.flag_degree_polynomial_eval hIn II hII Ψ N (rhoWt : Wt Ψ N) hN
    have hρ : flagDeg (rhoWt : Wt Ψ N) ≠ 0 := by
      rw [← h2, hfl, eval_mul, eval_C]
      exact mul_ne_zero hc₀.ne' eval_rho_antisymDelta_ne
    have h3 : eval (PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (0 / ((T.M 2 c).kA : ℝ))) (R.Sys c).degPoly =
        PB.volOf S' * flagDeg (rhoWt : Wt Ψ N) := by
      rw [zero_div]
      have e : PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) 0 =
          fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) := rfl
      rw [e, AnSys_degPoly_gapS_zero, ← hdeg, ← PB.eval_toWt_gap, hv, eval_mul, eval_C, h2]
    rw [h3, linA_zero_pow] at h1
    unfold RootTower.vol
    rw [← mul_div_assoc, h1, mul_div_cancel_right₀ _ hρ]

  have hpos : 0 < (R.Sys c).t₀ := ((R.Sys c).reg none).1
  have hconv : ∀ w, Tendsto (fun t => (R.tie B c).Re.num II t w) (𝓝[>] 0) (𝓝 ((R.tie B c).Re.limNum II w)) := by
    obtain ⟨C₃, s₀, -, h⟩ := hAg hIn (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 hpos
    exact (h II hII _ _ _ (R.tie B c).Re).1
  have hnum : ∀ mu : Wt Ψ N, (R.n c : ℝ) * T.PPc II B c (linRoot mu ^ (dimFl Ψ N + 1)) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.toWt (Re'.PB II)) := by
    intro mu
    have h1 := ((GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) mu 0).2.2 hconv hpos).2
    rw [zero_div, linA_zero_pow] at h1
    have e : PB.gapS (fun x : Ψ × Fin N => mu x.1 x.2) 0 =
        fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => mu x.1 x.2) := rfl
    rw [e, Realis_PB_gapS_zero, ← PB.eval_toWt_gap] at h1
    rw [hPB]
    exact h1
  have hh : ∀ mu : Wt Ψ N, hhFl Ψ N II (linRoot mu ^ (dimFl Ψ N + 1)) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.hFlPoly Ψ N II) :=
    fun mu => GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N mu hN harith

  have hQ := (hA hIn II hII Ψ N T.j d hN S' K ι P Re' F).2 (Equiv.swap (τ, a) (τ, b))
    ⟨τ, a, b, hab, by omega, rfl⟩
  have hE := congrArg (eval fun x : Ψ × Fin N => lam x.1 x.2) hQ
  rw [eval_rename, ← swapWt_uncurry] at hE
  simp only [map_sub, map_neg, smul_eval] at hE
  rw [← hnum, ← hnum, ← hh, ← hh, ← hvol] at hE
  apply mul_left_cancel₀ hn0
  linear_combination hE

end GlobalTheory.CompanionTheory.Ar.Top
