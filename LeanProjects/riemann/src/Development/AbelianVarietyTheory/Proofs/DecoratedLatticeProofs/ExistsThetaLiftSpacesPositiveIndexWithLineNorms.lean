import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHermitianLineVectorPrescribedNormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeeSaw.YRat

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [h1]
  haveI := D.host.isCMField_hostE
  exact IsCMField.complexEmbedding_complexConj _ _ _

theorem posDef_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

theorem defSpace {D : D7} (hX : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) {j : ℕ} (hj : j ≤ D.R.m) :
    (D.sp.X j).SigOK ∧ (∀ τ, (D.sp.X j).sig τ = (D.R.N j, 0)) ∧ CoCpt (D.sp.X j) := by
  have hs : (D.sp.X j).SigOK := D.sp.X_sig j
  have hr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j hj
  refine ⟨hs, fun τ => by rw [hX j hj τ, hr], ?_⟩
  refine (GlobalTheory.Unf.CoCptOf.coCpt_of_isAniso_or_posDef D (D.sp.X j)).2 fun τ => ?_
  have h1 := hs (tauE D τ)
  rw [hX j hj (tauE D τ)] at h1
  exact posDef_of_sig _ h1

theorem spaces_of_index : ∀ (D : D7) (u : D.what₂.Word), (∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef) → (∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (b : BesAt V (D.sp.X j) ρ), V.rank = D.R.rankY j ∧ V.SigOK ∧ (∀ τ, V.sig τ = sigYD D.R j) ∧ (star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)) ∧ ∀ j ρ, j + 2 * ρ + 2 = D.R.m → ∃ (V : HSp D) (_ : JacAt V (D.sp.X (j + 1)) ρ), V.rank = D.R.rankY (j + 1) ∧ V.SigOK ∧ ∀ τ, V.sig τ = sigYD D.R (j + 1) := by
  intro D u hX
  have hsum := GlobalTheory.T.exists_orthogonalSum_and_hyperbolicSum_spaces D
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  obtain ⟨π, -, hπ, -⟩ := D.T_norm u
  have hππ : (π : D.host.E) * star (π : D.host.E) = (((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [star_eq_conj]; exact hπ
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.ne_zero
    exact_mod_cast this
  have hπ0 : (π : D.host.E) ≠ 0 := by
    intro h0; apply hT0; rw [← hππ, h0, zero_mul]
  refine ⟨?_, ?_⟩
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j) (by omega)
    have hXr : (D.sp.X j).rank = D.R.N j := D.sp.X_rank j (by omega)
    set c : D.host.E := (π : D.host.E) / D.host.xi0 ^ (j / 2) with hc
    have hc0 : c ≠ 0 := div_ne_zero hπ0 (pow_ne_zero _ hxi)
    obtain ⟨L, ζ, hline, hLs, hLn, hLsig⟩ := GlobalTheory.T.exists_hermitianLine_vector_prescribed_norm D c (-1) hc0
    obtain ⟨V₀, o, hV₀s, hV₀sig⟩ := hsum.1 (D.sp.X j) L hXs hLs
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 V₀ ρ hV₀s
    refine ⟨V, ⟨V₀, L, d, o, ζ, hline, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_, ?_⟩
    · have h1 := d.rank_add
      have h2 := o.rank_add
      have h3 : L.rank = 1 := hline.1
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [Ranks.rankY, Ranks.r]
      rw [hXr] at h2
      simp only [Ranks.N] at h2
      omega
    · intro τ
      have hL : L.sig τ = (0, 1) := by rw [hLsig τ]; decide
      rw [hVsig τ, hV₀sig τ, hXsig τ, hL]
      have h4 : j * (D.R.t + 1) = j * D.R.t + j := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega
    · show (star ζ ⬝ᵥ L.gram *ᵥ ζ) * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = _
      rw [hLn, ← hππ, hc, star_div₀, star_pow]
      have hs0 : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
      field_simp
      push_cast
      ring
  · intro j ρ h
    obtain ⟨hXs, hXsig, hXc⟩ := defSpace hX (j := j + 1) (by omega)
    have hXr : (D.sp.X (j + 1)).rank = D.R.N (j + 1) := D.sp.X_rank (j + 1) (by omega)
    obtain ⟨V, d, hVs, hVsig⟩ := hsum.2 (D.sp.X (j + 1)) ρ hXs
    refine ⟨V, ⟨d, hXc, (hvol.2.1 _ _ _ d).some⟩, ?_, hVs, ?_⟩
    · have h1 := d.rank_add
      rw [hXr] at h1
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [Ranks.N] at h1
      simp only [Ranks.rankY, Ranks.r]
      omega
    · intro τ
      rw [hVsig τ, hXsig τ]
      have h4 : (j + 1) * (D.R.t + 1) = (j + 1) * D.R.t + (j + 1) := by ring
      simp only [sigYD, Ranks.rankY, Ranks.r, Ranks.N, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> omega

end GlobalTheory.SeeSaw.YRat

end
