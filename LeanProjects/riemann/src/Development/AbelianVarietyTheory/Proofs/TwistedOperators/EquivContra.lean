import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyEquivOfSmoothTraceEqAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeInvariantOfConjInvariantDistributionGLStatement

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix

namespace GlobalTheory.GelfandKazhdan

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

variable [TopologicalSpace G]

theorem isAdmissible_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (h : IsAdmissible π) : IsAdmissible (π.comp φ : Representation ℂ G V) := by
  have e0 : (φ : G → G) = Φ := funext fun x => (hΦ x).symm
  have hc : Continuous φ := e0 ▸ Φ.continuous
  have ho : IsOpenMap φ := e0 ▸ Φ.isOpenMap
  refine ⟨fun v => (h.1 v).preimage hc, fun K hKo hKc => ?_⟩
  have e : fixed (π.comp φ : Representation ℂ G V) K = fixed π (K.map φ) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (ho _ hKo) (hKc.image hc)

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

theorem smoothTrace_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (hμ : μ.map Φ = μ) (h : IsAdmissible π) {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    smoothTrace (π.comp φ : Representation ℂ G V) μ (f ∘ Φ) = smoothTrace π μ f := by
  have h' := isAdmissible_comp φ Φ hΦ h
  unfold smoothTrace
  congr 1
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [h'.1.map_smoothOp (hf.comp_continuous Φ.continuous) (hc.comp_homeomorph Φ), h.1.map_smoothOp hf hc]
  conv_rhs => rw [← hμ]
  rw [Φ.measurableEmbedding.integral_map]
  simp [hΦ]

theorem smoothTrace_conj [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {π : Representation ℂ G V}
    (h : IsAdmissible π) {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (g : G) :
    smoothTrace π μ (fun x => f (g * x * g⁻¹)) = smoothTrace π μ f := by
  let Φ : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  have hΦ : ∀ x, Φ x = φ x := fun _ => rfl
  have hμ : μ.map Φ = μ :=
    ((measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)).map_eq
  rw [← smoothTrace_comp φ Φ hΦ hμ h hf hc]
  refine (h.smoothTrace_eq_of_equiv (isAdmissible_comp φ Φ hΦ h).1 (hf.comp_continuous Φ.continuous)
    (hc.comp_homeomorph Φ) ho hK
    (LinearEquiv.ofLinear (π g) (π g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])) fun x v => ?_).symm
  change π g (π x v) = π (g * x * g⁻¹) (π g v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

end General

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.SplitFlip

theorem invTranspose_invTranspose (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) :
    invTranspose n R (invTranspose n R g) = g :=
  Units.ext (transpose_transpose _)

theorem continuous_invTranspose (n : ℕ) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invTranspose n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem equiv_contra (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invTranspose n k)) (contra π)) := by
  borelize k
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  have hb : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
    intro U hU
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
    exact ⟨J, h1, isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩
  let μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n))
  haveI : μ.IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hinv := invTranspose_invTranspose n k
  have hcont := continuous_invTranspose n k
  let Ψ : GL (Fin n) k ≃ₜ* GL (Fin n) k :=
    { toFun := invTranspose n k, invFun := invTranspose n k, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul _, continuous_toFun := hcont, continuous_invFun := hcont }
  let Φ : GL (Fin n) k ≃ₜ GL (Fin n) k := Ψ.toHomeomorph
  have hΦ : ∀ x, Φ x = invTranspose n k x := fun _ => rfl
  have hμ : μ.map Φ = μ := by
    have : (μ.map Φ).IsHaarMeasure := Ψ.isHaarMeasure_map μ
    refine @eq_haarVol _ _ _ _ _ _ _ _ _ _ _ this _ isOpen_KO le_rfl ?_
    refine (Measure.map_apply (μ := μ) Φ.measurable isOpen_KO.measurableSet).trans ?_
    have e : Φ ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) = KO k (Fin n) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_KO_iff]
      exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩
    rw [e]
    exact haarVol_self isOpen_KO le_rfl
  obtain ⟨hca, hct⟩ := GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv _ μ hb V π ha
  let T : SB (GL (Fin n) k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => smoothTrace π μ φ.1
      map_add' := fun φ ψ => ha.smoothTrace_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 isOpen_KO isCompact_KO
      map_smul' := fun c φ => ha.smoothTrace_smul φ.2.1 φ.2.2 isOpen_KO isCompact_KO c }
  have hT := GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL k (Fin n) T fun g φ ψ h => by
    change smoothTrace π μ ψ.1 = smoothTrace π μ φ.1
    rw [show ψ.1 = _ from funext h]
    exact smoothTrace_conj ha isOpen_KO isCompact_KO φ.2.1 φ.2.2 g
  refine GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible _ μ hb V _ _ _ (isAdmissible_comp _ Φ hΦ ha) hca
    (isIrreducible_comp _ (fun g => ⟨_, hinv g⟩) hi)
    ((GlobalTheory.T.smoothContragredient_irreducible_and_reflexive _ hb V V π π ha ha).1 hi) fun f hf hc => ?_
  have h1 := hf.comp_continuous Φ.continuous
  have h2 := hc.comp_homeomorph Φ
  have h3 := smoothTrace_comp _ Φ hΦ hμ ha h1 h2
  rw [show (f ∘ Φ) ∘ Φ = f from funext fun x => congrArg f (hinv x)] at h3
  rw [h3, hct f hf hc]
  refine hT ⟨fun g => f g⁻¹, hf.comp_continuous continuous_inv, hc.comp_homeomorph (Homeomorph.inv _)⟩
    ⟨f ∘ Φ, h1, h2⟩ fun x y hxy => congrArg f ?_
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  change (x⁻¹).valᵀ * y.val = 1
  rw [hxy, ← transpose_mul, Units.mul_inv, transpose_one]

end GlobalTheory.GelfandKazhdan
