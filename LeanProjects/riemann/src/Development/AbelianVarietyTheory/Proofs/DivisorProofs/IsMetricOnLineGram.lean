import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open scoped Matrix ComplexOrder ContDiff

namespace GlobalTheory.ChernWeilLine

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem unitAt_mul_inv_of_generatesAt {Δ : Y.Dv} {x : Y.X} {f g : Y.Fn} (hf : Δ.GeneratesAt x f)
    (hg : Δ.GeneratesAt x g) : UnitAt x (f * g⁻¹) := by
  obtain ⟨t, ht⟩ := Δ.exists_isEqn x
  have h1 := ht.generatesAt_iff.1 hf
  have h2 := ht.generatesAt_iff.1 hg
  have e : f * g⁻¹ = (f * (t : Y.Fn)) * (g * (t : Y.Fn))⁻¹ := by
    rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero t), mul_one]
  rw [e]
  exact h1.mul h2.inv

variable {e : ℕ} {M : Man e} (I : ManIs M Y) {Δ : Y.Dv} (a : Fin (M.n + 1))

theorem pn_pos_of_isPot {m : (cxSt F).Met Y (I.ε a) Δ} {Q : LocPot (M.X a)} (hQ : IsPot (I.pt a) m Q)
    {y : Pts Y (I.ε a)} {f : Y.Fn} (hf : Δ.GeneratesAt (under y) f) :
    0 < (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) y := by
  obtain ⟨g, hg⟩ := hQ ((I.pt a).symm y)
  have hp := (hg _ (Q.mem_U _)).2.1
  rw [Homeomorph.apply_symm_apply] at hp
  obtain ⟨c, hc, e⟩ := exists_pn_eq (C := cxSt F) hf
  rw [e m]
  exact mul_pos hc hp

theorem cInfAt_locPot {Q : LocPot (M.X a)} (hQ : IsPotential (M.A a) Q) (x : M.X a) {y : Pts Y (I.ε a)}
    (hy : (I.pt a).symm y ∈ Q.U x) : CInfAt (fun z => Q.φ x ((I.pt a).symm z)) y := by
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨c, hc⟩ := I.alg a j
  have h := hQ.1 x j
  rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target] at h
  rw [hc, Homeomorph.transOpenPartialHomeomorph_source] at hj
  have hS : IsOpen ((I.pt a).symm ⁻¹' Q.U x) := (Q.isOpen_U x).preimage (I.pt a).symm.continuous
  have h' : ContDiffOn ℝ ∞ ((fun w => Q.φ x ((I.pt a).symm w)) ∘ c.finChart.symm)
      (c.finChart.target ∩ c.finChart.symm ⁻¹' ((I.pt a).symm ⁻¹' Q.U x)) := by
    exact h
  refine cInfAt_of_chart hS c ((c.contDiffOn_finChart_iff _ _ _).1 h') ?_ hy
  simpa using hj

theorem cInfAt_pn_of_isPot {m : (cxSt F).Met Y (I.ε a) Δ} {Q : LocPot (M.X a)} (hQ : IsPot (I.pt a) m Q)
    (hQ' : IsPotential (M.A a) Q) {y : Pts Y (I.ε a)} {f : Y.Fn} (hf : Δ.GeneratesAt (under y) f) :
    CInfAt (fun z => (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) z) y := by
  set x := (I.pt a).symm y
  obtain ⟨g, hg⟩ := hQ x
  have hgy : Δ.GeneratesAt (under y) g := by
    have := (hg x (Q.mem_U x)).1
    rwa [Homeomorph.apply_symm_apply] at this
  obtain ⟨V, hV, hVu⟩ := (unitAt_mul_inv_of_generatesAt hf hgy).exists_nhds
  have hW : IsOpen ((I.pt a).symm ⁻¹' Q.U x ∩ ptsIn Y.str (I.ε a) V) :=
    ((Q.isOpen_U x).preimage (I.pt a).symm.continuous).inter (isOpen_ptsIn V)
  have hyW : y ∈ (I.pt a).symm ⁻¹' Q.U x ∩ ptsIn Y.str (I.ε a) V := ⟨Q.mem_U x, mem_ptsIn.2 hV⟩
  have h1 : CInfAt (fun z => ‖ratVal (f * g⁻¹) z‖ ^ 2) y :=
    cInfAt_ratVal (κ := Unit) (f := fun _ => f * g⁻¹) (fun _ => (hVu _ hV).regAt)
      (G := fun w => ‖w ()‖ ^ 2) ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ()))
  have h2 := cInfAt_locPot I a hQ' x (y := y) (Q.mem_U x)
  refine (h1.comp₂ h2 (G := fun p => p.1 * Real.exp (-2 * p.2))
    (contDiff_fst.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)))).congr ?_
  filter_upwards [hW.mem_nhds hyW] with z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hgz := hg _ hz1
  rw [Homeomorph.apply_symm_apply] at hgz
  obtain ⟨hgen, -, hφ⟩ := hgz
  have hpos := pn_pos_of_isPot I a hQ hgen
  have ef : f = (f * g⁻¹) * g := by
    rw [mul_assoc, inv_mul_cancel₀, mul_one]
    obtain ⟨t, ht⟩ := Δ.exists_isEqn (under z)
    intro h0
    have := (ht.generatesAt_iff.1 hgen).ne_zero
    rw [h0, zero_mul] at this
    exact this rfl
  show (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) z = _
  conv_lhs => rw [ef]
  rw [(cxSt F).pn_mul Y _ Δ m _ _ z (hVu _ (mem_ptsIn.1 hz2)).regAt hgen.regularAt, hφ]
  simp only [lnN]
  congr 1
  rw [show -2 * -(Real.log ((cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) g) z) / 2) =
    Real.log ((cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) g) z) by ring, Real.exp_log hpos]

end GlobalTheory.ChernWeilLine

namespace GlobalTheory.ChernWeilLine

theorem isMetricOn_lineGram_of_isPot : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → IsMetricOn (ofDivisors Δ) ⊤ (lineGram (cxSt F) fun i => m i (I.ε a)) := by
  intro F _ _ Y e M I ι _ Δ m a Q hQ
  refine ⟨fun y _ A hA τ => ?_, fun y _ A hA τ i j => ?_, fun y _ A hA A' hA' τ => ?_⟩
  · have hp := pn_pos_of_isPot I a (hQ τ).1 (hA τ)
    have e : lineGram (cxSt F) (fun i => m i (I.ε a)) A y τ = Matrix.diagonal fun _ =>
        (((cxSt F).pn Y (I.ε a) (Δ τ) (m τ (I.ε a)) ((cxSt F).cx Y (I.ε a) (A τ 0 0)) y : ℝ) : ℂ) := by
      ext u v
      rw [Subsingleton.elim u 0, Subsingleton.elim v 0]
      simp [lineGram]
    rw [e, Matrix.posDef_diagonal_iff]
    intro _
    exact_mod_cast hp
  · have h := cInfAt_pn_of_isPot I a (hQ τ).1 (hQ τ).2 (hA τ)
    constructor
    · exact h.congr (Eventually.of_forall fun z => by simp [lineGram])
    · exact (h.comp₂ h (G := fun _ => (0 : ℝ)) contDiff_const).congr (Eventually.of_forall fun z => by simp [lineGram])
  · have hr := unitAt_mul_inv_of_generatesAt (hA' τ) (hA τ)
    have hne : A τ 0 0 ≠ 0 := by
      obtain ⟨t, ht⟩ := (Δ τ).exists_isEqn (under y)
      intro h0
      have := (ht.generatesAt_iff.1 (hA τ)).ne_zero
      rw [h0, zero_mul] at this
      exact this rfl
    have e1 : A' τ 0 0 = (A' τ 0 0 * (A τ 0 0)⁻¹) * A τ 0 0 := by
      rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    have e2 := (cxSt F).pn_mul Y (I.ε a) (Δ τ) (m τ (I.ε a)) _ _ y hr.regAt (hA τ).regularAt
    rw [← e1] at e2
    ext u v
    rw [Subsingleton.elim u 0, Subsingleton.elim v 0]
    simp only [lineGram, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, Matrix.conjTranspose_apply, Mat.map,
      Matrix.map_apply, e2]
    have e3 : (A' * A⁻¹) τ 0 0 = A' τ 0 0 * (A τ 0 0)⁻¹ := by simp [Matrix.mul_apply, Matrix.inv_def]
    rw [e3]
    set w := ratVal (A' τ 0 0 * (A τ 0 0)⁻¹) y
    push_cast
    rw [mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring

end GlobalTheory.ChernWeilLine
