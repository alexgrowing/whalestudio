import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable (σ) in

structure Cpt (J : Matrix (Fin n) (Fin n) E) : Prop where
  lc : LocallyCompactSpace (UA σ J)
  sc : SecondCountableTopology (UA σ J)
  t2 : T2Space (UA σ J)
  cnt : Countable (ratU σ J)
  cov : ∃ Ω : Set (UA σ J), IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratU σ J, γ * g ∈ Ω
  hgt : ∃ C : ℝ≥0, ∀ g : UA σ J, qht g ≤ C
  ex : ∃ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ J) D μ
  fin : ∀ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) D μ → μ D < ⊤
  right : ∀ μ : Measure (UA σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def CptAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J

theorem cptAll_of (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : PositivityTheory.ThKEst.EpsOf) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : CptAll := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem fd_ne (hD : IsFundamentalDomain Γ D μ) : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)

theorem fd_eq_zero (hD : IsFundamentalDomain Γ D μ) {f : G → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (h0 : (fun g => ‖f g‖ ^ 2) =ᵐ[μ.restrict D] 0) : f = 0 := by
  have h1 : μ {g | f g ≠ 0} = 0 := by
    refine hD.measure_zero_of_invariant _ (fun γ => Set.ext fun x => ?_) ?_
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact (congrArg (· ≠ 0) (hi _ (γ⁻¹).2 x)).to_iff
    · rw [← Measure.restrict_apply (isOpen_ne_fun hc continuous_const).measurableSet]
      exact measure_mono_null (fun g hg => by simpa using hg) (ae_iff.1 h0)
  exact (hc.ae_eq_iff_eq μ continuous_const).1 h1

end Gen

variable {J : Matrix (Fin n) (Fin n) E}

instance borelUA : BorelSpace (UA σ J) := ⟨rfl⟩

instance topUA : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

theorem Cpt.bdd (h : Cpt σ J) {f : UA σ J → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) :
    ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov g
  exact hi γ hγ g ▸ hC _ hg

theorem Cpt.bdd₂ {m : ℕ} {J' : Matrix (Fin m) (Fin m) E} (h : Cpt σ J) (h' : Cpt σ J') {f : UA σ J × UA σ J' → ℂ}
    (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ δ ∈ ratU σ J', ∀ g g', f (γ * g, δ * g') = f (g, g')) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨Ω', hΩ', cov'⟩ := h'.cov
  obtain ⟨C, hC⟩ := (hΩ.prod hΩ').exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov x.1
  obtain ⟨δ, hδ, hg'⟩ := cov' x.2
  exact (hi γ hγ δ hδ x.1 x.2 ▸ hC (γ * x.1, δ * x.2) ⟨hg, hg'⟩ :)

theorem Cpt.rapid {Y : Spc F E n} (h : Cpt σ Y.J) {f : UA σ Y.J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ Y.J, ∀ g, f (γ * g) = f g) : IsRapid f := by
  obtain ⟨C, hC⟩ := h.bdd hc hi
  obtain ⟨b, hb⟩ := h.hgt
  exact ⟨hc, hi, fun N => ⟨C * (b : ℝ) ^ N, fun g => mul_le_mul (hC g) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hb g) N)
    (by positivity) ((norm_nonneg _).trans (hC g))⟩⟩

theorem Cpt.vol_ne (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) : μ.real D ≠ 0 := by
  haveI := h.cnt
  exact ENNReal.toReal_ne_zero.2 ⟨fd_ne hD, (h.fin μ D hμ hD).ne⟩

theorem Cpt.eq_zero (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {f : UA σ J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) (h0 : pet μ D f f = 0) : f = 0 := by
  haveI := h.cnt
  obtain ⟨C, hC⟩ := h.bdd hc hi
  have hi2 : IntegrableOn (fun g => ‖f g‖ ^ 2) D μ := Measure.integrableOn_of_bounded (M := C ^ 2) (h.fin μ D hμ hD).ne
    (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun g => by
      rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hC g) 2)
  have e : pet μ D f f = ((∫ g in D, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun g => by simpa using Complex.mul_conj' (f g))
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi2] at h0
  exact fd_eq_zero hD hc hi h0

end GlobalTheory.ThK.Dbl

end
