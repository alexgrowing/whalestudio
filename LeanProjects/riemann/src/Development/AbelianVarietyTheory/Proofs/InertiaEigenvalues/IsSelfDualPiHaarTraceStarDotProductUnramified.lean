import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.PiSelfDual

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem finite : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)

theorem isModuleTopology : IsModuleTopology F E := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Module.Finite F E := finite
  exact IsModuleTopology.iso (R := F) (A := Fin 2 → F)
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Unram.finrank_eq (F := F) (E := E)]))

theorem star_smul_F {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, Unram.star_fix (E := E) a, mul_comm]

theorem trace_star (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  apply (algebraMap F E).injective
  rw [(GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1, (GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1, star_star, add_comm]

def trForm (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp [star_add, add_dotProduct])
    (fun a c b => by rw [star_smul_F, smul_dotProduct, LinearMap.map_smul])
    (fun c b b' => by simp [dotProduct_add])
    (fun a c b => by rw [dotProduct_smul, LinearMap.map_smul])

theorem trForm_apply (r : ℕ) (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trForm_isSymm (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [trForm_apply, trForm_apply, star_dotProduct, trace_star]

theorem trForm_separatingLeft (r : ℕ) (c : Fin r → E) (hc : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  classical
  funext i
  obtain ⟨e, -, he⟩ := (GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).2.1
  have h0 := hc (Pi.single i (c i * e))
  rw [trForm_apply, dotProduct_single, Pi.star_apply] at h0
  have h1 : algebraMap F E (Algebra.trace F E (star (c i) * (c i * e))) = star (c i) * c i * (e + star e) := by
    rw [(GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E).1]
    simp only [star_mul, star_star]
    ring
  rw [h0, map_zero, he, mul_one] at h1
  rcases mul_eq_zero.1 h1.symm with h | h
  · simpa using h
  · simpa using h

theorem trForm_nondegenerate (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate :=
  ⟨fun c hc => trForm_separatingLeft r c hc, fun b hb => trForm_separatingLeft r b (fun c => by
    rw [(trForm_isSymm (F := F) r).eq]; exact hb c)⟩

def intLat (r : ℕ) : AddSubgroup (Fin r → E) :=
  haveI : IsUltrametricDist E := Unram.ultraE F
  { carrier := {b | ∀ i, ‖b i‖ ≤ 1}
    add_mem' := fun {a b} ha hb i => by
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    zero_mem' := fun i => by simp
    neg_mem' := fun {a} ha i => by simpa using ha i }

theorem intLat_eq (r : ℕ) :
    ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) =
      Set.univ.pi (fun _ => Metric.closedBall (0 : E) 1) := by
  ext b
  simp [intLat, Metric.mem_closedBall, dist_zero_right]

theorem dual_intLat (r : ℕ) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    {y : Fin r → E | ∀ x ∈ intLat (F := F) (E := E) r, ψ (trForm (F := F) r x y) = 1} =
      ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
  classical
  haveI : IsUltrametricDist E := Unram.ultraE F
  have key := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  ext y
  constructor
  · intro hy i
    refine (key (y i)).1 (fun e he => ?_)
    have hx : Pi.single i (star e) ∈ intLat (F := F) (E := E) r := by
      intro j
      by_cases hj : j = i
      · subst hj; simp [Unram.norm_star (F := F), he]
      · simp [Pi.single_apply, hj]
    have := hy _ hx
    rwa [trForm_apply, Pi.star_single, star_star, single_dotProduct] at this
  · intro hy x hx
    have hn : ‖star x ⬝ᵥ y‖ ≤ 1 := by
      unfold dotProduct
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => ?_)
      rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hy i)
    have := (key 1).2 (by simp) (star x ⬝ᵥ y) hn
    rwa [mul_one] at this

end GlobalTheory.JR.PiSelfDual

open GlobalTheory.JR.PiSelfDual in

theorem GlobalTheory.JR.selfDual_pi_trace : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → @SelfDual (Fin r → E) _ _ (@MeasurableSpace.pi (Fin r) (fun _ => E) (fun _ => M.mE)) (@Measure.pi (Fin r) (fun _ => E) _ (fun _ => M.mE) (fun _ => M.μE)) (fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))) := by
  intro F E _ _ _ _ _ r M ψ hψ
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : LocallyCompactSpace E := Unram.lcE F
  haveI : IsUltrametricDist E := Unram.ultraE F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : Module.Finite F E := finite
  haveI : IsModuleTopology F E := isModuleTopology
  haveI : BorelSpace (Fin r → E) := Pi.borelSpace
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hvol : (Measure.pi fun _ : Fin r => M.μE) ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) = 1 := by
    rw [intLat_eq, Measure.pi_pi]
    simp [M.volE]
  have hopen : IsOpen ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero)
  have hcpt : IsCompact ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by
    rw [intLat_eq]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  have h := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_isSymm r) (trForm_nondegenerate r)
    (Measure.pi fun _ => M.μE) inferInstance).1 (intLat r) hopen hcpt |>.1
  refine h.2 ?_
  rw [dual_intLat r ψ hψ, hvol, one_mul]
