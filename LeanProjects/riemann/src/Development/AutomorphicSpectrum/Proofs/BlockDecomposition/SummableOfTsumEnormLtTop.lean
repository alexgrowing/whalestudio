import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeVecMulLinearEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaOrbit

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {X ι : Type*} {κ : ι → Type*} [Countable X] [Countable ι] [∀ i, Countable (κ i)]

theorem summable_of_tsum_enorm_lt_top {Y : Type*} {f : Y → ℂ} (h : ∑' y, ‖f y‖ₑ < ⊤) : Summable f := by
  have h' : Summable (fun y => ‖f y‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa only [enorm_eq_nnnorm] using h.ne)
  exact Summable.of_norm ((NNReal.summable_coe.2 h').congr fun y => coe_nnnorm _)

theorem hasSum_average_descend (e : (Σ i, κ i) ≃ X) (a : G → X → ℂ) (ha : ∀ x, Measurable fun g => a g x)
    (hA : LeftInv Γ fun g => ∑' x, ‖a g x‖ₑ)
    (hL : ∀ i, LeftInv Γ fun g => ∑' k : κ i, a g (e ⟨i, k⟩))
    (hfin : ∫⁻ q, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤) :
    HasSum (fun i => ⨍ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
      (⨍ q, descend Γ (fun g => ∑' x, a g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  classical
  have hsec : Measurable (sec Γ) := measurableEmbedding_sec.measurable
  have hdescC : ∀ φ : G → ℂ, LeftInv Γ φ → descend Γ φ = φ ∘ sec Γ := by
    intro φ hφ
    funext q
    show φ q.out = φ (sec Γ q)
    apply hφ.eq_of_mk_eq
    rw [mk_sec]
    exact Quotient.out_eq q
  have hdescE : ∀ φ : G → ℝ≥0∞, LeftInv Γ φ → descend Γ φ = φ ∘ sec Γ := by
    intro φ hφ
    funext q
    show φ q.out = φ (sec Γ q)
    apply hφ.eq_of_mk_eq
    rw [mk_sec]
    exact Quotient.out_eq q
  have hNm : Measurable (descend Γ fun g => ∑' x, ‖a g x‖ₑ) := by
    rw [hdescE _ hA]
    exact (Measurable.tsum fun x => (ha x).enorm).comp hsec
  have hFm : ∀ i, AEStronglyMeasurable (descend Γ fun g => ∑' k : κ i, a g (e ⟨i, k⟩))
      (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    intro i
    rw [hdescC _ (hL i)]
    exact ((Measurable.tsum fun k => ha _).comp hsec).aestronglyMeasurable
  have hbound : ∀ g, ∑' i, ‖∑' k : κ i, a g (e ⟨i, k⟩)‖ₑ ≤ ∑' x, ‖a g x‖ₑ := by
    intro g
    calc ∑' i, ‖∑' k : κ i, a g (e ⟨i, k⟩)‖ₑ ≤ ∑' i, ∑' k : κ i, ‖a g (e ⟨i, k⟩)‖ₑ :=
          ENNReal.tsum_le_tsum fun i => enorm_tsum_le_tsum_enorm
      _ = ∑' p : Σ i, κ i, ‖a g (e p)‖ₑ := (ENNReal.tsum_sigma' fun p => ‖a g (e p)‖ₑ).symm
      _ = ∑' x, ‖a g x‖ₑ := e.tsum_eq fun x => ‖a g x‖ₑ
  have hpt : ∀ g, ∑' x, ‖a g x‖ₑ < ⊤ →
      HasSum (fun i => ∑' k : κ i, a g (e ⟨i, k⟩)) (∑' x, a g x) := by
    intro g hg
    have hs : Summable (a g) := summable_of_tsum_enorm_lt_top hg
    have hse : Summable (a g ∘ e) := e.summable_iff.2 hs
    exact (e.hasSum_iff.2 hs.hasSum).sigma fun i => (hse.sigma_factor i).hasSum
  have hlin : ∑' i, ∫⁻ q, ‖descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ < ⊤ := by
    rw [← lintegral_tsum fun i => (hFm i).enorm]
    exact lt_of_le_of_lt (lintegral_mono fun q => hbound q.out) hfin
  have hsI : Summable fun i =>
      ∫ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ :=
    summable_of_tsum_enorm_lt_top
      (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _) hlin)
  have hae : ∀ᵐ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ, descend Γ (fun g => ∑' x, ‖a g x‖ₑ) q < ⊤ :=
    ae_lt_top hNm hfin.ne
  have hint : ∫ q, descend Γ (fun g => ∑' x, a g x) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ =
      ∑' i, ∫ q, descend Γ (fun g => ∑' k : κ i, a g (e ⟨i, k⟩)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
    rw [← integral_tsum hFm hlin.ne]
    refine integral_congr_ae ?_
    filter_upwards [hae] with q hq
    exact (hpt q.out hq).tsum_eq.symm
  simp only [average_eq]
  rw [hint]
  exact hsI.hasSum.const_smul _

end Abstract

section Rows

variable {K : Type} [Field K]

open GlobalTheory.CompanionTheory.MatrixRowSpace in

theorem bijective_mul_rowBasis (m n : ℕ)
    (c : ∀ U : Submodule K (Fin n → K), Matrix (Fin (Module.finrank K U)) (Fin n) K)
    (hc : ∀ U, LinearIndependent K (c U) ∧ Submodule.span K (Set.range (c U)) = U) :
    Function.Bijective (fun q : (Σ U : Submodule K (Fin n → K),
      {x : Matrix (Fin m) (Fin (Module.finrank K U)) K // x.rank = Module.finrank K U}) => q.2.1 * c q.1) := by
  have hinj : ∀ U, Function.Injective (c U).vecMulLinear := fun U =>
    Matrix.vecMul_injective_iff.2 (hc U).1
  have hrange : ∀ U, LinearMap.range (c U).vecMulLinear = U := fun U => by
    rw [range_vecMulLinear_eq, (hc U).2]
  constructor
  · rintro ⟨U, x, hx⟩ ⟨U', x', hx'⟩ h
    dsimp only at h
    have hU : U = U' := by
      have h1 := span_rows_mul_of_rank x (c U) hx
      have h2 := span_rows_mul_of_rank x' (c U') hx'
      calc U = Submodule.span K (Set.range (c U)) := (hc U).2.symm
        _ = Submodule.span K (Set.range (x * c U)) := h1.symm
        _ = Submodule.span K (Set.range (x' * c U')) := by rw [h]
        _ = Submodule.span K (Set.range (c U')) := h2
        _ = U' := (hc U').2
    subst hU
    have hxx : x = x' := by
      ext i j
      have hi : (x * c U) i = (x' * c U) i := by rw [h]
      rw [row_mul, row_mul] at hi
      exact congrFun (hinj U hi) j
    subst hxx
    rfl
  · intro y
    obtain ⟨U, hU⟩ : ∃ U : Submodule K (Fin n → K), U = Submodule.span K (Set.range y) := ⟨_, rfl⟩
    have hrow : ∀ i, ∃ v : Fin (Module.finrank K U) → K, (c U).vecMulLinear v = y i := by
      intro i
      have hmem : y i ∈ LinearMap.range (c U).vecMulLinear := by
        rw [hrange U, hU]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact LinearMap.mem_range.1 hmem
    choose v hv using hrow
    have hxc : Matrix.of v * c U = y := by
      ext i j
      have hi : (Matrix.of v * c U) i = y i := by
        rw [row_mul]
        exact hv i
      exact congrFun hi j
    have hS : Submodule.span K (Set.range (Matrix.of v)) = ⊤ := by
      apply Submodule.map_injective_of_injective (hinj U)
      rw [Submodule.map_top, hrange U, ← span_rows_mul, hxc, hU]
    exact ⟨⟨U, Matrix.of v, (span_rows_eq_top_iff _).2 hS⟩, hxc⟩

theorem countable_submodule [Countable K] (n : ℕ) : Countable (Submodule K (Fin n → K)) := by
  have hs : Function.Surjective
      (fun s : Finset (Fin n → K) => Submodule.span K (s : Set (Fin n → K))) := fun U =>
    IsNoetherian.noetherian U
  exact hs.countable

end Rows

variable {D : D7}

private theorem exists_invPt_mul_eq_invPt_mul_of_mem_GQ (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ A : GL (Fin V.rank) D.host.E, ∀ (g : GA D V) {a : ℕ} (ξ : Matrix (Fin V.rank) (Fin a) D.host.E),
      GlobalTheory.SiegelFormula.invPt V (γ * g) ξ =
        GlobalTheory.SiegelFormula.invPt V g ((A : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * ξ) := by
  simp only [GQ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin,
    Subgroup.mem_map] at hγ
  obtain ⟨g0, -, hg0⟩ := hγ
  refine ⟨g0⁻¹, fun g a ξ => ?_⟩
  have key : ((Formalism.L2.Theta.matHom V γ⁻¹ : GL _ _) : Matrix _ _ _) =
      ((g0⁻¹ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have hγ' : Formalism.L2.Theta.matHom V γ = _ := hg0.symm
    rw [map_inv, hγ', ← map_inv]
    rfl
  simp only [GlobalTheory.SiegelFormula.invPt, Formalism.L2.Theta.mt, mul_inv_rev, map_mul, Units.val_mul,
    Matrix.map_mul, Matrix.mul_assoc, key]

theorem leftInv_rankSum (V : HSp D) {r n : ℕ} (φ : Mx D V.rank n → ℂ) (c : Matrix (Fin r) (Fin n) D.host.E) (s : ℕ) :
    LeftInv (GQ V) fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s},
      φ (GlobalTheory.SiegelFormula.invPt V h (x.1 * c)) := by
  intro γ hγ g
  obtain ⟨A, hA⟩ := exists_invPt_mul_eq_invPt_mul_of_mem_GQ V hγ
  have hrank : ∀ (B : GL (Fin V.rank) D.host.E) (x : Matrix (Fin V.rank) (Fin r) D.host.E),
      ((B : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x).rank = x.rank := fun B x =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit)
  let eqv : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s} :=
    { toFun := fun x => ⟨(A : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x.1, (hrank A x.1).trans x.2⟩
      invFun := fun x => ⟨((A⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * x.1,
        (hrank A⁻¹ x.1).trans x.2⟩
      left_inv := fun x => Subtype.ext (by simp [← Matrix.mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [← Matrix.mul_assoc]) }
  show ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s},
      φ (GlobalTheory.SiegelFormula.invPt V (γ * g) (x.1 * c)) =
    ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = s}, φ (GlobalTheory.SiegelFormula.invPt V g (x.1 * c))
  simp only [hA, ← Matrix.mul_assoc]
  exact eqv.tsum_eq fun x => φ (GlobalTheory.SiegelFormula.invPt V g (x.1 * c))

theorem pull_mt (V : HSp D) {r n : ℕ} (φ : Mx D V.rank n → ℂ) (c : Matrix (Fin r) (Fin n) D.host.E) (h : GA D V)
    (x : Matrix (Fin V.rank) (Fin r) D.host.E) :
    pull c φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.map (incA D))) = φ (GlobalTheory.SiegelFormula.invPt V h (x * c)) := by
  simp only [pull, GlobalTheory.SiegelFormula.invPt, Matrix.map_mul, Matrix.mul_assoc]

theorem thetaOrbits : ThetaOrbits := by
  intro D n V θ hθ ν hν Φ hfin c hc
  haveI := hν
  haveI : Countable D.host.E := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  haveI : Countable (Submodule D.host.E (Fin n → D.host.E)) := countable_submodule n
  haveI : ∀ r : ℕ, Countable (Matrix (Fin V.rank) (Fin r) D.host.E) := fun r =>
    inferInstanceAs (Countable (Fin V.rank → Fin r → D.host.E))
  have hcont : Continuous Φ.1 :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ V.rank n Φ.1 Φ.2).1
  have key := hasSum_average_descend (G := GA D V) (Γ := GQ V) (μ := ν)
    (κ := fun U : Submodule D.host.E (Fin n → D.host.E) =>
      {x : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E U)) D.host.E //
        x.rank = Module.finrank D.host.E U})
    (Equiv.ofBijective _ (bijective_mul_rowBasis V.rank n c hc))
    (fun g ξ => Φ.1 (GlobalTheory.SiegelFormula.invPt V g ξ))
    (fun ξ => (hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).measurable)
    (GlobalTheory.SiegelFormula.leftInv_absTheta V Φ.1)
    (fun U => leftInv_rankSum V Φ.1 (c U) (Module.finrank D.host.E U))
    hfin
  convert key using 1
  funext U
  simp only [Ifr, pull_mt]
  rfl

end GlobalTheory.CompanionTheory.ThetaOrbit

end
