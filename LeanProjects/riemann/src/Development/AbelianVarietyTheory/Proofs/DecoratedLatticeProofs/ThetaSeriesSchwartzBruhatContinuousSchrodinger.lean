import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.ThetaOf

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem exists_symplO_eq (d : HypDec S S₀ ρ) (T : HSp D) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E} (hξ : ξ ≠ 0)
    (t : AF D.host.F) : ∃ a, symplO S T (d.extX T (rat ξ)) (d.extY T a) = t := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have hv : T.gram * ξ ≠ 0 := fun h => hξ (by
    rw [← Matrix.nonsing_inv_mul_cancel_left T.gram ξ (gram_isUnit_det T), h, Matrix.mul_zero])
  obtain ⟨i, j, hij⟩ : ∃ i j, (T.gram * ξ) i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Matrix.ext h)
  let c : AE D := t ⊗ₜ[D.host.F] ((2 * D.host.xi0 * (T.gram * ξ) i j)⁻¹)
  refine ⟨adj (Matrix.single j i c), ?_⟩
  have h := d.hO_ext T (rat ξ) 0 0 (adj (Matrix.single j i c)) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_adj, gA, ← rat_mul,
    Matrix.trace_single_mul, smul_eq_mul]
  have e : incA D D.host.xi0 * (c * rat (T.gram * ξ) i j) = t ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (1 / 2)) := by
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] D.host.xi0) * (c * ((1 : AF D.host.F) ⊗ₜ[D.host.F] (T.gram * ξ) i j)) = _
    simp only [c, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [map_div₀, map_one, map_ofNat]
    field_simp
  rw [e, GlobalTheory.LatVac.trace_tmul, Algebra.trace_algebraMap, D.sp.cm.deg2]
  simp

theorem integral_char_eq_zero {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (χ : Mx D m n → ℂ) (hmul : ∀ a b, χ (a + b) = χ a * χ b)
    (hγ : ∀ γ ∈ ratMx D m n, χ γ = 1) {u : Mx D m n} (hu : χ u ≠ 1) : ∫ a in 𝓕, χ a ∂μ = 0 := by
  have h1 := covolOne_integral_add h χ (fun γ hg a => by rw [hmul, hγ γ hg, one_mul]) u
  simp only [hmul, integral_mul_const] at h1
  by_contra h0
  exact hu (mul_left_cancel₀ h0 (h1.trans (mul_one _).symm))

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_left]; ring

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO_eq_add, GlobalTheory.OrientedHeis.symplOH_add_right]; ring

theorem continuous_symplO {S T : HSp D} {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  simp only [symplO_eq_add]
  exact (GlobalTheory.OrientedHeis.continuous_symplOH hx hy).add (GlobalTheory.OrientedHeis.continuous_symplOH hx hy)

theorem integral_pair (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E}
    (hξ : ξ ≠ 0) : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) ∂μ = 0 := by
  obtain ⟨t, ht⟩ := hψ.1.2.2.2
  obtain ⟨u, hu⟩ := exists_symplO_eq d T hξ t
  refine integral_char_eq_zero h _ (fun a b => ?_) (fun γ hγ => ?_) (u := u) (by rw [hu]; exact ht)
  · rw [map_add, symplO_add_right, AddChar.map_add_eq_mul]
  · exact (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T _).2 (ratMx_mul (rat_mem _) (rat_mem _)) _
      (ratMx_mul hγ (rat_mem _))

theorem bound_translates (hψ : IsStdChar D ψ (-1)) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) : Continuous φ ∧ ∀ Q : Set (Mx D m n), IsCompact Q →
      ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨hc, K, hK, hb⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨C, hC⟩ := hb N
  refine ⟨hc, fun Q hQ => ?_⟩
  obtain ⟨b, hs, hb⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hs.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)

theorem theta_series (hψ : IsStdChar D ψ (-1)) (d : HypDec S S₀ ρ) (T : HSp D) {μ : Measure (Mx D T.rank ρ)}
    {𝓕 : Set (Mx D T.rank ρ)} (h : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {φ : Mx D T.rank ρ → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {f : WO S T → ℂ}
    (hf : ∀ w : WO S T, f w = ψ (-(symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (w ⬝ d.jY)))) *
      ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
        ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    Continuous f ∧ ∀ x, d.mixS T ψ μ 𝓕 f x 0 = φ x := by
  obtain ⟨hc, hb⟩ := bound_translates hψ hφ
  have hψc : Continuous ψ := hψ.1.1
  have hn : ∀ t, ‖ψ t‖ = 1 := hψ.1.2.1
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hjX : Continuous fun w : WO S T => (w ⬝ d.jX : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  have hjY : Continuous fun w : WO S T => (w ⬝ d.jY : Mx D T.rank ρ) := continuous_id.matrix_mul continuous_const
  constructor
  · obtain ⟨i1, i2, -⟩ := lattice_Mx D T.rank S.rank
    obtain ⟨j1, -⟩ := lattice_Mx D T.rank ρ
    rw [funext hf]
    refine (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp hjX) (hY.comp hjY)).neg).mul ?_
    refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨Q, hQ, hw⟩ := exists_compact_mem_nhds w
    obtain ⟨b, hs, hb⟩ := hb _ (hQ.image hjX)
    refine ContinuousOn.continuousAt (continuousOn_tsum (fun ξ => Continuous.continuousOn ?_) hs fun ξ y hy => ?_) hw
    · exact (hψc.comp (continuous_symplO (hX.comp (hjX.add continuous_const)) (hY.comp hjY))).mul
        (hc.comp (hjX.add continuous_const))
    · rw [norm_mul, hn, one_mul]
      exact hb _ ⟨y, hy, rfl⟩ ξ
  · intro x
    obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D T.rank ρ
    haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
    haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
    haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
    haveI : Countable (Matrix (Fin T.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (_ → _ → D.host.E))
    obtain ⟨b, hs, hb⟩ := hb {x} isCompact_singleton
    have hone : μ.real 𝓕 = 1 := by rw [Measure.real, h.2.2, ENNReal.toReal_one]
    have key : ∀ a, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T 0) f)) 0 =
        ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) := by
      intro a
      have e1 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jX : Mx D T.rank ρ) = x := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pY_jX,
          Matrix.mul_one, Matrix.mul_zero, zero_add]
      have e2 : ((d.extY T a + d.extX T x : WO S T) ⬝ d.jY : Mx D T.rank ρ) = a := by
        simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY, HypDec.pY_jY,
          Matrix.mul_one, Matrix.mul_zero, add_zero]
      rw [d.integrandS_eq, map_zero, add_zero, hf, e1, e2, ← mul_assoc, ← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.extX T), symplO_add_left,
        symplOH_skew S T (d.extX T x), symplO_eq_add S T (d.extX T x)]
      congr 2
      ring
    have hF := hasSum_integral_of_summable_integral_norm (μ := μ.restrict 𝓕)
      (F := fun (ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E) a =>
        ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ)) (fun ξ => ?_) ?_
    · rw [HypDec.mixS]
      simp only [key]
      refine hF.unique ?_
      have h0 : ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat 0)) (d.extY T a)) * φ (x + rat 0) ∂μ = φ x := by
        simp only [rat_zero, map_zero, symplO_eq_add, symplOH_zero_left, add_zero, AddChar.map_zero_eq_one, one_mul,
          setIntegral_const, hone, one_smul]
      rw [← h0]
      refine hasSum_single (f := fun ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E =>
        ∫ a in 𝓕, ψ (symplO S T (d.extX T (rat ξ)) (d.extY T a)) * φ (x + rat ξ) ∂μ) 0 fun ξ hξ => ?_
      rw [integral_mul_const, integral_pair hψ d T h hξ, zero_mul]
    · refine Integrable.mul_const (Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun a => (hn _).le)) _
      exact (hψc.comp (continuous_symplO continuous_const hY)).measurable.aestronglyMeasurable
    · simp only [norm_mul, hn, one_mul, setIntegral_const, hone, one_smul]
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb x rfl ξ) hs

theorem theta_series_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → Continuous f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 h φ hφ f hf
  obtain ⟨h1, h2⟩ := theta_series hψ (dblDec A) B h hφ hf
  exact ⟨h1, funext h2⟩

end GlobalTheory.Core.Rk.ThetaOf

end
