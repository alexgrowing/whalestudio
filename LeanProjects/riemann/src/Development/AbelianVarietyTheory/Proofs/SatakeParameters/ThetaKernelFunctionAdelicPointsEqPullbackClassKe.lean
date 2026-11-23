import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryPeriodNeZeroAndLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelPosBadPrimesNoConjugatePairStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeTranslateEqImageClassLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumRationalTranslatesVsClassesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumPairClassesHasReaderLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTransporStatement

noncomputable section

namespace GlobalTheory.TwV.SPull

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_scal {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun v => k * Φ v) e z = k * xiL H α vol SX SA SB Φ e z := by
  have hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w := by
    intro x
    funext w
    unfold xiS Formalism.L2.Th1.H.sumU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y := by
      unfold hatS
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    beta_reduce
    rw [this]
    ring
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS x]
  simp only [Formalism.L2.Th1.H.opU]
  ring

theorem kerTh_scal {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k : ℂ) (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl N N' (fun x => k * Ξ x) z = k * kerTh B χ SS cl N N' Ξ z := by
  have hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) =
      fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v := by
    funext v
    unfold Formalism.L2.Ker.onV
    split_ifs <;> simp
  unfold kerTh thC xiV
  rw [hon]
  exact xiL_scal _ _ _ _ _ _ _ _ _ _

theorem kerTh_prop {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ Ξ' : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k k' : ℂ)
    (h : ∀ x, k * Ξ x = k' * Ξ' x) (z : TaylorLogMetric.VC D a b) :
    k * kerTh B χ SS cl N N' Ξ z = k' * kerTh B χ SS cl N N' Ξ' z := by
  rw [← kerTh_scal, ← kerTh_scal, funext h]

set_option maxHeartbeats 1000000 in

theorem kerTh_eq_pull : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' z
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hSS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hA
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA i (Nat.le_of_succ_le hi) γ hγ
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA (i + 1) hi γ' hγ'
  have hN := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA i (Nat.le_of_succ_le hi) c x γ hγ κ hx
  have hN' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA (i + 1) hi c' x' γ' hγ' κ' hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hu'
  have hc := GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hA Xi muT law i hi c c'
  have hth := GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported A dtU a hP hA Xi muT law i hi c c'
  have hmv := GlobalTheory.TwU.KerMove.kerTh_move D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (ssRec t u μ) (t.rd u μ).lev hl hSS
    _ _ _ _ _ (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c') hc _ _ hu hu'
  rw [hth, ← hmv, hN, hN']
  exact kerTh_prop _ _ _ _ _ _ _ _ _ _ hd z

end GlobalTheory.TwV.SPull

end
