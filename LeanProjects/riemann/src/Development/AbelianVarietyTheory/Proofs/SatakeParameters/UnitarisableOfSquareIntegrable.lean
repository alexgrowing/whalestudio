import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlHomNnrealTrivialOfScalarTrivialStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

open MeasureTheory ComplexConjugate

namespace GlobalTheory.SqIntUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable (k) in

theorem exists_ne_zero_ne_one : ∃ x : k, x ≠ 0 ∧ x ≠ 1 := by
  have h : absPow k ((1 : ℝ) : ℂ) ≠ 1 := fun e => one_ne_zero (absPow_ofReal_eq_one.1 e)
  obtain ⟨z, hz⟩ : ∃ z : kˣ, absPow k ((1 : ℝ) : ℂ) z ≠ 1 := by
    by_contra! h'
    exact h (MonoidHom.ext h')
  refine ⟨z, z.ne_zero, fun e => hz ?_⟩
  rw [show z = 1 from Units.ext e, map_one]

variable (k N) in

theorem modularCharacterFun_eq_one (g : AdGL k N) : Measure.modularCharacterFun g = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  let φ : GL (Fin N) k →* NNReal :=
    Measure.modularCharacter.comp (QuotientGroup.mk' (Subgroup.center (GL (Fin N) k)))
  refine GlobalTheory.T.gl_hom_nnreal_trivial_of_scalar_trivial k (exists_ne_zero_ne_one k) N φ (fun z => ?_) g
  have hz : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ Subgroup.center (GL (Fin N) k) :=
    Subgroup.mem_center_iff.2 fun h => (Matrix.GeneralLinearGroup.scalar_commute z h).symm
  show Measure.modularCharacter (QuotientGroup.mk' _ _) = 1
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hz, map_one]

theorem isMulRightInvariant [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor μ g, modularCharacterFun_eq_one, one_smul]

variable (k) in

theorem compactOpen_basis (n : ℕ) : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
    IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsUnitarisable π := by
  intro k _ _ _ _ N V _ _ π hs hi hsq
  classical
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (compactOpen_basis k N) hv₀
  set L : Module.Dual ℂ V := (l : Module.Dual ℂ V) with hLdef
  have hLo : IsOpen {g : GL (Fin N) k | L ∘ₗ π g = L} := by
    have h1 : IsOpen {g : GL (Fin N) k | π.dual g L = L} := l.2
    have : {g : GL (Fin N) k | L ∘ₗ π g = L} = (fun g => g⁻¹) ⁻¹' {g | π.dual g L = L} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Representation.dual_apply, inv_inv]
      rfl
    rw [this]
    exact h1.preimage continuous_inv
  borelize (AdGL k N)
  let μ : Measure (AdGL k N) := Measure.haar
  have hF : ∀ v, ∃ F : AdGL k N → ℝ, (∀ g, F (QuotientGroup.mk g) = ‖L (π g v)‖) ∧ MemLp F 2 μ := fun v => by
    obtain ⟨F, h1, h2⟩ := hsq μ inferInstance v L hLo
    exact ⟨F, h1, by simpa using h2⟩
  choose F hF1 hF2 using hF
  have hc : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
    intro z hz
    obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      exact congrArg π (Subgroup.mem_center_iff.1 hz g).symm⟩
    refine ⟨c, ?_, hc⟩
    have h1 := hF1 v₀ z
    have h2 := hF1 v₀ 1
    rw [(QuotientGroup.eq_one_iff z).2 hz] at h1
    rw [QuotientGroup.mk_one, h1, map_one, Module.End.one_apply] at h2
    have h3 : L v₀ ≠ 0 := hl
    have : ‖c‖ * ‖L v₀‖ = 1 * ‖L v₀‖ := by
      rw [one_mul, ← norm_mul, ← smul_eq_mul, ← map_smul, ← hc]
      exact h2
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 h3) this
  let f : V → V → GL (Fin N) k → ℂ := fun v w g => L (π g v) * conj (L (π g w))
  have hfz : ∀ v w g, ∀ z ∈ Subgroup.center (GL (Fin N) k), f v w (g * z) = f v w g := by
    intro v w g z hz
    obtain ⟨c, hc1, hc⟩ := hc z hz
    have h1 : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
      simp
    simp only [f, map_mul, Module.End.mul_apply, hc, map_smul, smul_eq_mul]
    linear_combination (L (π g v) * conj (L (π g w))) * h1
  let Φ : V → V → AdGL k N → ℂ := fun v w x => f v w (Quotient.out x)
  have hΦ : ∀ v w g, Φ v w (QuotientGroup.mk g) = f v w g := by
    intro v w g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    show f v w (Quotient.out (QuotientGroup.mk g : AdGL k N)) = f v w g
    rw [hz]
    exact hfz v w g z z.2
  have hfc : ∀ v w, Continuous (f v w) := by
    intro v w
    have h1 : ∀ u, Continuous fun g : GL (Fin N) k => L (π g u) := fun u =>
      ((GlobalTheory.ContraRefl.isLocallyConstant_orbit hs u).comp L).continuous
    exact (h1 v).mul (Complex.continuous_conj.comp (h1 w))
  have hΦc : ∀ v w, Continuous (Φ v w) := by
    intro v w
    refine (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin N) k))).continuous_iff.2 ?_
    have : Φ v w ∘ QuotientGroup.mk = f v w := funext (hΦ v w)
    rw [this]
    exact hfc v w
  have hnorm : ∀ v w x, ‖Φ v w x‖ = F v x * F w x := by
    intro v w x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1, hF1]
    simp [f, norm_mul]
  have hint : ∀ v w, Integrable (Φ v w) μ := by
    intro v w
    refine Integrable.mono' ((hF2 v).integrable_mul (hF2 w)) (hΦc v w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hnorm]
    rfl
  have hadd1 : ∀ v v' w, Φ (v + v') w = fun x => Φ v w x + Φ v' w x := fun v v' w => funext fun x => by
    simp only [Φ, f, map_add, add_mul]
  have hsmul1 : ∀ (a : ℂ) v w, Φ (a • v) w = fun x => a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w', Φ v (w + w') = fun x => Φ v w x + Φ v w' x := fun v w w' => funext fun x => by
    simp only [Φ, f, map_add, mul_add]
  have hsmul2 : ∀ (a : ℂ) v w, Φ v (a • w) = fun x => conj a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, map_mul]
    ring
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ x, Φ v w x ∂μ)
    (fun v v' w => by rw [hadd1, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul1, integral_const_mul, RingHom.id_apply, smul_eq_mul])
    (fun v w w' => by rw [hadd2, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul2, integral_const_mul, smul_eq_mul])
  have hB : ∀ v w, B v w = ∫ x, Φ v w x ∂μ := fun v w => rfl
  have hre : ∀ v x, (Φ v v x).re = F v x ^ 2 := by
    intro v x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1]
    simp only [f, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun h v w => ?_⟩
  · rw [hB, hB, ← integral_conj]
    congr 1
    funext x
    simp only [Φ, f, map_mul, Complex.conj_conj]
    ring
  · have hcont : Continuous fun x => F v x ^ 2 := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact Complex.continuous_re.comp (hΦc v v)
    have hi2 : Integrable (fun x => F v x ^ 2) μ := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact (hint v v).re
    have hreB : (B v v).re = ∫ x, F v x ^ 2 ∂μ := by
      rw [hB]
      show RCLike.re (∫ x, Φ v v x ∂μ) = _
      rw [← integral_re (hint v v)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hre v x)
    rw [hreB]
    refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (fun h0 => hv ?_)
    have h1 : (fun x => F v x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi2).1 h0.symm
    have h2 : (fun x => F v x ^ 2) = 0 := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 h1
    have h3 : ∀ g, L (π g v) = 0 := fun g => by
      have := congrFun h2 (QuotientGroup.mk g)
      rw [Pi.zero_apply, hF1] at this
      simpa using this
    let W : Subrepresentation π :=
      ⟨{ carrier := {u | ∀ g, L (π g u) = 0}
         add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
         zero_mem' := fun g => by simp
         smul_mem' := fun c u hu g => by simp [hu g] },
        fun g u hu h => by
          show L (π h (π g u)) = 0
          rw [← Module.End.mul_apply, ← map_mul]
          exact hu (h * g)⟩
    haveI : IsSimpleOrder (Subrepresentation π) := hi
    rcases eq_bot_or_eq_top W with hW | hW
    · have hvW : v ∈ W.toSubmodule := h3
      rw [hW] at hvW
      exact (Submodule.mem_bot ℂ).1 hvW
    · exfalso
      have hvW : v₀ ∈ W.toSubmodule := by
        rw [hW]
        exact Submodule.mem_top
      have := hvW 1
      rw [map_one, Module.End.one_apply] at this
      exact hl this
  · haveI := isMulRightInvariant μ
    have hinv : ∀ x, Φ (π h v) (π h w) x = Φ v w (x * QuotientGroup.mk h) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_mul, hΦ, hΦ]
      simp only [f, map_mul, Module.End.mul_apply]
    rw [hB, hB, funext hinv]
    exact integral_mul_right_eq_self (Φ v w) _

end GlobalTheory.SqIntUnit
