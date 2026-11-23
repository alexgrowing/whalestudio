import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AbsThetaSemi

variable {D : D7}

theorem continuous_coord {d m n : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Continuous (coord (D := D) (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => ?_
  let L : AE D →ₗ[AF D.host.F] AF D.host.F :=
    (Finsupp.lapply p.2.2).comp (Algebra.TensorProduct.basis (AF D.host.F) ε).repr.toLinearMap
  exact (IsModuleTopology.continuous_of_linearMap L).comp
    ((continuous_apply p.2.1).comp (continuous_apply p.1))

theorem continuous_invPt (B : HSp D) {a : ℕ} (ξ : Matrix (Fin B.rank) (Fin a) D.host.E) :
    Continuous fun h : GA D B => invPt B h ξ := by
  unfold invPt
  have hmt : Continuous (Formalism.L2.Theta.mt B) := Units.continuous_val.comp continuous_subtype_val
  exact (hmt.comp continuous_inv).matrix_mul continuous_const

theorem measurable_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (absTheta B φ) := by
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin B.rank) (Fin a) D.host.E) := inferInstanceAs (Countable (Fin B.rank → Fin a → D.host.E))
  exact Measurable.ennreal_tsum fun ξ => (hφ.comp (continuous_invPt B ξ)).enorm.measurable

theorem measurable_descend_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (descend (GQ B) (absTheta B φ)) :=
  measurable_from_quotient.2 (by
    rw [show descend (GQ B) (absTheta B φ) ∘ Quotient.mk'' = absTheta B φ from (leftInv_absTheta B φ).lift_descend]
    exact measurable_absTheta B hφ)

theorem absTheta_add_le (B : HSp D) {a : ℕ} (φ ψ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (φ + ψ) h ≤ absTheta B φ h + absTheta B ψ h := by
  unfold absTheta
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun ξ => enorm_add_le _ _

theorem absTheta_smul (B : HSp D) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (c • φ) h = ‖c‖ₑ * absTheta B φ h := by
  unfold absTheta
  rw [← ENNReal.tsum_mul_left]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]

theorem absThetaInt_add_le (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ)
    (ψ : Mx D B.rank a → ℂ) : absThetaInt B m (φ + ψ) ≤ absThetaInt B m φ + absThetaInt B m ψ := by
  unfold absThetaInt
  rw [← lintegral_add_left (measurable_descend_absTheta B hφ)]
  exact lintegral_mono fun q => absTheta_add_le B φ ψ q.out

theorem absThetaInt_smul (B : HSp D) (m : Measure (GA D B)) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) :
    absThetaInt B m (c • φ) = ‖c‖ₑ * absThetaInt B m φ := by
  unfold absThetaInt
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  exact lintegral_congr fun q => absTheta_smul B c φ q.out

theorem absTheta_le_liminf (B : HSp D) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot] {φs : ι → Mx D B.rank a → ℂ}
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) (h : GA D B) :
    absTheta B φ h ≤ Filter.liminf (fun i => absTheta B (φs i) h) u := by
  unfold absTheta
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have ht : Filter.Tendsto (fun i => ∑ ξ ∈ s, ‖φs i (invPt B h ξ)‖ₑ) u (nhds (∑ ξ ∈ s, ‖φ (invPt B h ξ)‖ₑ)) :=
    tendsto_finset_sum s fun ξ _ => (hlim _).enorm
  rw [← ht.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => ENNReal.sum_le_tsum s)

theorem absThetaInt_le_liminf (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot]
    [u.IsCountablyGenerated] {φs : ι → Mx D B.rank a → ℂ} (hc : ∀ i, Continuous (φs i))
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) :
    absThetaInt B m φ ≤ Filter.liminf (fun i => absThetaInt B m (φs i)) u := by
  unfold absThetaInt
  refine le_trans (lintegral_mono fun q => absTheta_le_liminf B hlim q.out) ?_
  exact lintegral_liminf_le fun i => measurable_descend_absTheta B (hc i)

end GlobalTheory.AbsThetaSemi

namespace GlobalTheory.AbsThetaSemi

theorem absThetaInt_le_contSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  intro hP D A B m hm hA hw d ε
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), Continuous (φ.1 ∘ coord ε) :=
    fun φ => (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA D.host.F φ.2).comp (continuous_coord ε)
  have hfin : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≠ ⊤ :=
    fun φ => (hP D A.rank B hA hw θ hθ m hm ⟨_, GlobalTheory.T.schwartz_coordinates_in_infinite_family D θ hθ B.rank A.rank d ε φ⟩).ne
  let ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)) :=
    Seminorm.of (fun φ => (absThetaInt B m (φ.1 ∘ coord ε)).toReal)
      (fun φ ψ => by
        rw [← ENNReal.toReal_add (hfin φ) (hfin ψ)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin φ, hfin ψ⟩) (absThetaInt_add_le B m (hcont φ) _))
      (fun c φ => by
        show (absThetaInt B m (c • (φ.1 ∘ coord ε))).toReal = _
        rw [absThetaInt_smul, ENNReal.toReal_mul, toReal_enorm])
  refine ⟨ν, fun g => ?_, fun φ => (ENNReal.ofReal_toReal (hfin φ)).ge⟩
  let L : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ]
      WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d) :=
    { toFun := pureS g
      map_add' := fun f f' => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, add_mul])
      map_smul' := fun c f => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, mul_assoc]) }
  haveI := GlobalTheory.schwartzMap_barrelledSpace (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F)
  have hev : ∀ y, Continuous fun f : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => f y :=
    fun y => ((continuous_eval_const y : Continuous fun F : BoundedContinuousFunction (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => F y)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ).continuous
  have hN : LowerSemicontinuous fun f => absThetaInt B m ((pureS g f).1 ∘ coord ε) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro f
    exact absThetaInt_le_liminf B m (fun f' => hcont (pureS g f')) fun x => ((hev _).tendsto f).mul_const _
  refine Seminorm.continuous_of_lowerSemicontinuous (ν.comp L) fun f y hy => ?_
  by_cases hy0 : y < 0
  · exact Filter.Eventually.of_forall fun f' => hy0.trans_le ENNReal.toReal_nonneg
  · push_neg at hy0
    have h1 : ENNReal.ofReal y < absThetaInt B m ((pureS g f).1 ∘ coord ε) :=
      (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy
    filter_upwards [hN f _ h1] with f' hf'
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hf'

end GlobalTheory.AbsThetaSemi

end
