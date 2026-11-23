import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerIdentityAtCutoffStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinRootRemainderBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousPowerSumDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagShiftTotalLinRootPowerStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DominantPartialSumBoundsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem label_term_lower {A b K C' abelian₂ n j s t a : ℝ} (hn : 0 < n) (hK : 0 ≤ K) (hC : 0 ≤ C') (hL : 0 ≤ abelian₂)
    (hA : -(K * abelian₂) ≤ A) (hflat : |j * A + n * b| ≤ C' * n * abelian₂)
    (hc0 : 0 ≤ s - j * (t / n)) (hc1 : s - j * (t / n) ≤ a) (ht : |t| ≤ a) :
    -((K + C') * abelian₂ * a) ≤ A * s + b * t := by
  have hid : A * s + b * t = A * (s - j * (t / n)) + (j * A + n * b) * (t / n) := by
    field_simp
    ring
  have hKL : 0 ≤ K * abelian₂ := mul_nonneg hK hL
  have h1 : -(K * abelian₂ * a) ≤ A * (s - j * (t / n)) := by
    have e1 : -(K * abelian₂) * (s - j * (t / n)) ≤ A * (s - j * (t / n)) :=
      mul_le_mul_of_nonneg_right hA hc0
    have e2 : K * abelian₂ * (s - j * (t / n)) ≤ K * abelian₂ * a := mul_le_mul_of_nonneg_left hc1 hKL
    linarith
  have h2 : -(C' * abelian₂ * a) ≤ (j * A + n * b) * (t / n) := by
    have e0 : |(j * A + n * b) * (t / n)| ≤ C' * abelian₂ * a := by
      rw [abs_mul, abs_div, abs_of_pos hn]
      have e3 : |j * A + n * b| * (|t| / n) ≤ C' * n * abelian₂ * (|t| / n) :=
        mul_le_mul_of_nonneg_right hflat (div_nonneg (abs_nonneg _) hn.le)
      have e4 : C' * n * abelian₂ * (|t| / n) = C' * abelian₂ * |t| := by
        field_simp
      have e5 : C' * abelian₂ * |t| ≤ C' * abelian₂ * a := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hL)
      linarith
    exact (abs_le.mp e0).1
  rw [hid]
  nlinarith [h1, h2]

theorem linRoot_isHomogeneous {Ψ : Type} [Fintype Ψ] {N : ℕ} (u : Wt Ψ N) :
    (linRoot u : RP Ψ N).IsHomogeneous 1 := by
  unfold linRoot
  refine IsHomogeneous.neg ?_
  exact IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _

theorem spread_nonneg {Ψ : Type} [Fintype Ψ] {N : ℕ} (hN : 0 < N) (u : Wt Ψ N) : 0 ≤ spread u := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine Finset.sum_nonneg fun τ _ => ?_
  have i₀ : Fin N := ⟨0, hN⟩
  have h1 : u τ i₀ ≤ ⨆ i, u τ i := le_ciSup (Set.finite_range _).bddAbove i₀
  have h2 : (⨅ i, u τ i) ≤ u τ i₀ := ciInf_le (Set.finite_range _).bddBelow i₀
  linarith

theorem RegDominant.dominant' {Ψ : Type} {N : ℕ} {u : Wt Ψ N} (h : RegDominant u) : Dominant u := by
  intro τ a b hab
  rcases hab.lt_or_eq with h1 | h1
  · exact (h τ a b h1).le
  · rw [h1]

theorem tower_T2_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N)
    (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (K C' rd Lval : ℝ), 0 ≤ K → 0 ≤ C' → 1 ≤ rd →
    T.Proportional → FrobShape frob → I9 (Ψ := Ψ) (N := N) hh → T.Prop6 II frob → T.ThmBA II hh →
    T.PropF II C' rd Lval → T.LowerBoundAtBase II hh frob K rd Lval → T.T2 II (K + C' + 2) rd Lval := by
  intro II Ψ _ _ N T hh frob K C' rd Lval hK hC hrd hprop hshape hI9 hP6 hBA hF hA0 u g hW B hB128 hB0 hbad
  have hN2 : 2 ≤ N := by
    have := T.j_pos; have := T.j_lt; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have h0 : (linRoot u : RP Ψ N) = 0 := by simp [linRoot]
    have hPB : T.PB II B u = 0 := by
      simp [RootTower.PB, RootTower.PPt, RootTower.PPc, h0, toA]
    have hbr : T.bracket rd Lval B u = 0 := by
      simp [RootTower.bracket, l1, spread]
    rw [hPB, hbr]
    simp
  obtain ⟨hg, hreg, -, -⟩ := id hW
  have hdom : Dominant u := RegDominant.dominant' hreg

  have hfpos : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hBig : 4 * Fintype.card Ψ * N ^ 2 ≤ B := by
    have h1 : (4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2) ≤ bigB0 u g := by
      unfold bigB0
      have h2 : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hg.le
      have h3 : 0 ≤ 4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by positivity
      nlinarith
    have h4 : (4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2) < (B : ℝ) + 1 := lt_of_le_of_lt h1 hB0
    have h5 : 4 * Fintype.card Ψ * N ^ 2 < B + 1 := by exact_mod_cast h4
    omega
  obtain ⟨A₀, b₀, hId⟩ := GlobalTheory.T.tower_identity_at_cutoff II Ψ N T hh frob hprop hshape hP6 hBA B (by omega)
  have hAl := hA0 B A₀ b₀ hB128 hBig hbad hId
  have hfl := GlobalTheory.T.cutoff_coefficients_bound II Ψ N T hh frob C' rd Lval B A₀ b₀ hprop hI9 hF hB128 hbad hId
  have hHom : (linRoot u ^ (dimFl Ψ N + 1) : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
    simpa using (linRoot_isHomogeneous u).pow (dimFl Ψ N + 1)
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.homogeneous_power_sum_decomposition Ψ N _ hN2 hHom
  have hDec : IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q := ⟨hQ1, hQ2⟩
  have hEq := GlobalTheory.T.tower_height_identity_expansion II Ψ N T hh frob B A₀ b₀ _ Q hId hDec
  have hRest := GlobalTheory.T.lin_root_remainder_bound Ψ N T.j T.bad frob u g B Q T.j_pos T.j_lt hW hB0 hDec
  have hhF : 0 ≤ hh (linRoot u ^ (dimFl Ψ N + 1)) := hI9.2.1 u hdom
  have hdeg : 0 < flagDeg u := (GlobalTheory.CompanionTheory.Ar.Top.flagDeg_eq_weyl Ψ N u).2.1 hreg
  have hV : 0 < T.volT := Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hLam : 0 ≤ bigLam B rd Lval := by
    unfold bigLam
    have h1 : (1 : ℝ) ≤ (B : ℝ) * rd := by
      have : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      nlinarith
    have := Real.log_nonneg h1
    have := abs_nonneg Lval
    linarith
  set E : ℝ := ((dimFl Ψ N : ℝ) + 1) * flagDeg u with hE
  have hEpos : 0 < E := by positivity
  set abelian₂ := bigLam B rd Lval with hLamDef
  have hsum : -((K + C') * abelian₂ * l1 u) ≤
      ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) := by
    have : ∀ σ ∈ (Finset.univ : Finset Ψ), -((K + C') * abelian₂ * ∑ i, |u σ i|) ≤
        A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i := by
      intro σ _
      obtain ⟨l1', l2', l3'⟩ := GlobalTheory.T.dominant_partial_sum_bounds N T.j (u σ) T.j_lt.le (by omega) (fun a b h => hdom σ a b h)
      exact label_term_lower hNpos hK hC hLam hAl hfl l1' l2' l3'
    have h2 := Finset.sum_le_sum this
    have h3 : ∑ σ, -((K + C') * abelian₂ * ∑ i, |u σ i|) = -((K + C') * abelian₂ * l1 u) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rfl
    rwa [h3] at h2
  have hShTot : -(A₀ * ∑ σ, Sh T.j σ (linRoot u ^ (dimFl Ψ N + 1))) -
      b₀ * ∑ σ, Tot σ (linRoot u ^ (dimFl Ψ N + 1)) =
      E * ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) := by
    simp only [fun σ => (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N T.j σ u).1, fun σ => (GlobalTheory.T.flag_shift_total_lin_root_power Ψ N T.j σ u).2]
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have hSpread : 0 ≤ ((min T.j (N - T.j) : ℕ) : ℝ) * spread u :=
    mul_nonneg (Nat.cast_nonneg _) (spread_nonneg (by omega) u)
  have hl1 : 0 ≤ l1 u := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hLl : 0 ≤ abelian₂ * l1 u := mul_nonneg hLam hl1
  set R := ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B τ k (Q τ k) with hR
  set Sp := ((min T.j (N - T.j) : ℕ) : ℝ) * spread u with hSp
  have hRl : -(2 * E * Sp) ≤ R := (abs_le.mp hRest).1
  have hinner : -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) ≤
      hh (linRoot u ^ (dimFl Ψ N + 1)) - A₀ * ∑ σ, Sh T.j σ (linRoot u ^ (dimFl Ψ N + 1)) -
        b₀ * ∑ σ, Tot σ (linRoot u ^ (dimFl Ψ N + 1)) + R := by
    have e1 : E * -((K + C') * abelian₂ * l1 u) ≤ E * ∑ σ, (A₀ * (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < T.j), u σ i) + b₀ * ∑ i, u σ i) :=
      mul_le_mul_of_nonneg_left hsum hEpos.le
    rw [← hShTot] at e1
    have e2 : 0 ≤ E * (2 * (abelian₂ * l1 u)) := by positivity
    have e3 : 0 ≤ E * ((K + C') * Sp) := mul_nonneg hEpos.le (mul_nonneg (add_nonneg hK hC) hSpread)
    nlinarith [e1, e2, e3, hRl, hhF]
  have hfin : T.volT * -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) ≤ T.PB II B u := by
    have : T.PB II B u = T.PPt II B (linRoot u ^ (dimFl Ψ N + 1)) := rfl
    rw [this, hEq]
    exact mul_le_mul_of_nonneg_left hinner hV.le
  have hgoal : -((K + C' + 2) * ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) * T.bracket rd Lval B u) =
      T.volT * -((K + C' + 2) * E * (abelian₂ * l1 u + Sp)) := by
    simp only [RootTower.bracket, hE, hSp, hLamDef]
    ring
  rw [hgoal]
  exact hfin

end GlobalTheory.CompanionTheory.Ar.Top
