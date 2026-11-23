import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContDelta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl
private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous
private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F
private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero
end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
open UpperTheory.V.Cu.RankFourTensorSourceAtPrime in
theorem UpperTheory.V.Cu.tower_is_initial_of_ok :
    UpperTheory.V.Cu.AlNe → UpperTheory.V.Cu.WtsOf4 → UpperTheory.V.Cu.IrrOf4 → UpperTheory.V.Cu.AutOf4 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
      (d : UpperTheory.V.Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → OffW d.ι d.K' d.ρ (UpperTheory.V.Cu.tenB d.ρ₁ d.τ) →
      T.IsSeedAlt d.ι ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))) := by
  intro hne hW hI hA Ω _ _ _ l _ d T hT hok hrw
  have hi := hI Ω l d T hT hok
  obtain ⟨π, h1, h2⟩ := hA Ω l d T hT hok hi
  obtain ⟨U, j, hU, hj⟩ := d.tw.wt
  have hm := d.tau.pos
  have hk := d.big
  let φ : G ℚ Ω →* (Qbar l)ˣ := (toB d.δ)⁻¹ ^ 2 * cycBar ℚ Ω l ^ j
  have hle : U ≤ φ.ker := fun g hg => by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hg)
    rw [map_pow, map_zpow] at this
    have e : toB d.δ g ^ 2 = cycBar ℚ Ω l g ^ j := this.trans (congrArg (· ^ j) (toB_chi d.c g))
    show (toB d.δ g)⁻¹ ^ 2 * cycBar ℚ Ω l g ^ j = 1
    rw [← e, inv_pow, inv_mul_cancel]
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : Finite (G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle hU)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨hi, _, ((toB d.δ).comp (resQ T.L))⁻¹, π, -j, φ.ker.index, fun i => ?_,
    hW Ω l d T U j hU hj, ((cont_delta d).comp (cont_res T.L)).inv, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,
    ⟨(d.k : ℤ) - 1 + d.m, by simp <;> ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' h1 (autOf4W hne Ω l d T hT hok hi hrw π h1 h2), h2⟩
  · fin_cases i
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
    · exact ⟨(d.k : ℤ) - 1 - 2 * d.m, by omega, by simp <;> ring⟩
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
  · have := φ.ker.pow_index_mem (resQ T.L s)
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [neg_neg]
    exact this
end
