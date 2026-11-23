import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPointsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftBound

variable {D : D7}

theorem entry_le (θ : InfF D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) (i j : Fin V.rank) :
    ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤ normInf θ V g := by
  unfold normInf
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j =>
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ j)

theorem norm_mM_le (θ : InfF D) (S T : HSp D) (a : GA D S) (b : GA D T) (p q : GlobalTheory.RealWeil.Ix S T) :
    ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ normInf θ S a * normInf θ T b := by
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  rw [GlobalTheory.RealWeil.mM_apply, GlobalTheory.RealWeil.blk, blockDiagonal_apply]
  split_ifs
  · rw [kroneckerMap_apply, transpose_apply, norm_mul, mul_comm]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) ha
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (entry_le θ S a p.2 q.1.2 p.1.2)
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (entry_le θ T b p.2 p.1.1 q.1.1)
  · rw [norm_zero]
    exact mul_nonneg ha hb

theorem sum_mM_le (θ : InfF D) (S T : HSp D) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : GA D S) (b : GA D T),
    1 + ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ K * ((1 + normInf θ S a) * (1 + normInf θ T b)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Fintype.card (GlobalTheory.RealWeil.Ix S T) : ℝ) := ⟨_, rfl⟩
  have c0 : 0 ≤ c := hc ▸ Nat.cast_nonneg _
  refine ⟨1 + c * c, by positivity, fun a b => ?_⟩
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have h1 : ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ c * (c * (normInf θ S a * normInf θ T b)) := by
    refine (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => norm_mM_le θ S T a b p q).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have h2 := mul_nonneg ha hb
  have h3 := mul_nonneg c0 c0
  nlinarith [mul_nonneg h3 ha, mul_nonneg h3 hb]

theorem one_add_normInf_mul (θ : InfF D) (V : HSp D) (g h : GA D V) :
    1 + normInf θ V (g * h) ≤ (1 + normInf θ V g) * (1 + normInf θ V h) := by
  have h1 := (GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 g h
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) g
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h
  nlinarith

theorem om_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  intro D ψ hψ S T om hom θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨Ω, hosc, ⟨N, hN⟩, -⟩ :=
    GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.HM S T) GlobalTheory.RealWeil.HM_herm GlobalTheory.RealWeil.HM_det
      (GlobalTheory.RealWeil.BB ψ S T) (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.isHeis_rhoB h hψ) (GA D S × GA D T)
      (GlobalTheory.RealWeil.mM θ S T) (GlobalTheory.RealWeil.mM_unitary hθ)
  obtain ⟨K, hK0, hK⟩ := sum_mM_le θ S T
  obtain ⟨-, -, -, -, -, s6, s7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ S
  obtain ⟨-, -, -, -, -, t6, t7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ T
  refine ⟨N, fun f hf x y => ?_⟩
  obtain ⟨k, hk, a₀, ha₀, rfl⟩ := s7 x
  obtain ⟨k', hk', b₀, hb₀, rfl⟩ := t7 y
  have hf' := hom.om_pres (k, k') f hf
  have hF : IsThetaFunO ψ S T (GlobalTheory.RealWeil.toB hψ _ hf').1 := by
    rw [GlobalTheory.RealWeil.coe_toB]; exact hf'
  obtain ⟨C, hC⟩ := hN _ (GlobalTheory.RealWeil.sm_of_theta h hψ _ hF)
  refine ⟨|C| * (K * ((1 + normInf θ S a₀) * (1 + normInf θ T b₀))) ^ N, fun a ha b hb w => ?_⟩
  have haa := mul_mem ha₀ ha
  have hbb := mul_mem hb₀ hb
  obtain ⟨c, hc, hcF⟩ := GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hom Ω hosc _ haa _ hbb
  have e : ((k * a₀ * a, k' * b₀ * b) : GA D S × GA D T) = (a₀ * a, b₀ * b) * (k, k') := by
    rw [Prod.mk_mul_mk, s6 _ haa k hk, t6 _ hbb k' hk', mul_assoc, mul_assoc]
  have e2 := hcF _ hF
  rw [GlobalTheory.RealWeil.coe_toB] at e2
  rw [e, map_mul, Module.End.mul_apply, e2, Pi.smul_apply, norm_smul, hc, one_mul]
  refine (GlobalTheory.RealWeil.norm_ev_le w _).trans ((hC _).trans ?_)
  have n1 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a₀
  have n2 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b₀
  have n3 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have n4 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have n5 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) (b₀ * b)
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ((hK _ _).trans ?_) N) (by positivity)
    (abs_nonneg C)
  rw [mul_assoc K]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  refine (mul_le_mul (one_add_normInf_mul θ S a₀ a) (one_add_normInf_mul θ T b₀ b) (by positivity)
    (by positivity)).trans_eq ?_
  ring

end GlobalTheory.Mem.LiftBound

end
