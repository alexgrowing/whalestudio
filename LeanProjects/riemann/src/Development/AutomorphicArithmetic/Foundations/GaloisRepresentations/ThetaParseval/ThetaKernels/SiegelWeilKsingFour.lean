import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingNStr

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem bdd_of_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {U : nA σ d.Y d.b × d.G → ℂ} (hU : Continuous U)
    (hper : ∀ β, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β + l, y) = U (β, y)) {C : Set d.G} (hC : IsCompact C) :
    ∃ M, ∀ β, ∀ y ∈ C, ‖U (β, y)‖ ≤ M := by
  obtain ⟨K, hK, hKβ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.nCocompact_k d
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hU.continuousOn
  refine ⟨M, fun β y hy => ?_⟩
  obtain ⟨l, hl, hβl⟩ := hKβ β
  have e := hper (β - l) l hl y
  rw [sub_add_cancel] at e
  rw [e]
  exact hM _ ⟨hβl, hy⟩
set_option maxHeartbeats 800000 in
theorem fc_avg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβc : Continuous β) (hβ : ∀ x, R.ι w (nr x) = nb (β x))
    (T : nF σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      fc d.B.ψ d.b nb lam 𝓖 f T z * ∫ x, ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)) := by
  have := hG
  set χ : nA σ d.Y d.b → ℂ := fun β₀ => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β₀.1))))
    with hχ
  set U : nA σ d.Y d.b × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1 with hUdef
  have hnbc := _root_.PositivityTheory.SiegelWeilFormula.KSing.continuous_nb_k d hCD.1
  have hnrc := cont_nr nr hnr
  have hιr : Continuous fun x => R.ι w (nr x) * z := ((R.cont w).comp hnrc).mul continuous_const
  have hUc : Continuous U :=
    (hf.comp ((hnbc.comp continuous_fst).mul continuous_snd)).mul ((_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_cont_k d T).comp continuous_fst)
  have hUper : ∀ β₀, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β₀ + l, y) = U (β₀, y) := by
    intro β₀ l hl y
    simp only [hUdef, hχ]
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T β₀ l, _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl, mul_one, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hCD.1 hl)]
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.bdd_of_per_k d hUc hUper ((hψs.isCompact).image hιr)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, hCD.2.2.2]; exact ENNReal.one_lt_top⟩
  have e1 : ∀ β₀ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = U (β₀, R.ι w (nr x) * z) * ψ₀ x := by
    intro β₀ x
    simp only [hUdef]
    rw [hβ x, ← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1,
      show nb β₀ * nb (β x) * z = nb β₀ * (nb (β x) * z) from mul_assoc _ _ _]
    ring
  have eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖) := by
    unfold fc
    congr 1
    funext β₀
    rw [← integral_mul_const]
    congr 1
    funext x
    exact e1 β₀ x
  have hcont : Continuous (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) :=
    (hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume) := by
    refine Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm))
      (_root_.PositivityTheory.SiegelWeilFormula.KSing.aesm_of_continuous_k d hCD hcont) (Eventually.of_forall fun p => ?_)
    show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖
    rw [norm_mul]
    by_cases hx : p.2 ∈ tsupport ψ₀
    · exact mul_le_mul_of_nonneg_right (hM p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [eL, integral_integral_swap hint]
  have e2 : ∀ x, ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1))) := by
    intro x
    rw [integral_mul_const]
    have : ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z) := by
      rw [hβ x]
      rfl
    rw [this, _root_.PositivityTheory.SiegelWeilFormula.KSing.fc_shift_k d hCD f hinv T (β x) z]
    ring
  simp_rw [e2]
  rw [integral_const_mul]
end PositivityTheory.SiegelWeilFormula.KSing
end
end
