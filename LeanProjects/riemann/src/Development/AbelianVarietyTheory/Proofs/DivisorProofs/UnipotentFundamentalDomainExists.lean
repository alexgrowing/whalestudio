import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMassHerm

theorem exists_fundDom_pos_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ g : G, ∃ γ : Γ, γ • g ∈ K) (μ : Measure G)
    [μ.IsHaarMeasure] : ∃ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := by
  obtain ⟨μ₀, 𝓕, h0, hF, h1⟩ := GlobalTheory.T.cocompact_lattice_unit_covolume G Γ K hK hcov
  haveI := h0
  have e : μ = Measure.haarScalarFactor μ μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀
  refine ⟨𝓕, hF.mono ?_, ?_, ?_⟩
  · rw [e]; exact Measure.smul_absolutelyContinuous
  · rw [e, Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one]; exact_mod_cast hc.ne'
  · rw [e, Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one]; exact ENNReal.coe_ne_top

end GlobalTheory.UnipMassHerm

namespace GlobalTheory.UnipMassHerm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hcm
  obtain ⟨-, htc, -, hτ⟩ := hcm
  have hx : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := htc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    refine ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hτ w.embedding x
    rw [hall x] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, hσ]; ring

theorem form_smul_mat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : E) (v w : Fin n → E) :
    form σ (δ • J) v w = δ * form σ J v w := by
  unfold form
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (v w : Fin n → E) :
    form σ J (t • v) w = t * form σ J v w := by
  unfold form
  rw [smul_dotProduct, smul_eq_mul]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (v w : Fin n → E) :
    form σ J v (t • w) = σ t * form σ J v w := by
  unfold form
  rw [show (fun i => σ ((t • w) i)) = σ t • fun i => σ (w i) from funext fun i => by simp [map_mul],
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem incM_smul (δ : E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem UG_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {δ : E} (hδ : δ ≠ 0) :
    UG (cA σ) (incM F (δ • J)) = UG (cA σ) (incM F J) := by
  have hu : IsUnit (inclR (F := F) (AF F) δ) := (isUnit_iff_ne_zero.2 hδ).map _
  ext g
  show (g : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F (δ • J) * (g : Matrix _ _ _).map (cA σ) = incM F (δ • J) ↔
    (g : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J * (g : Matrix _ _ _).map (cA σ) = incM F J
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul]
  exact hu.smul_left_cancel

end GlobalTheory.UnipMassHerm

namespace GlobalTheory.UnipMassHerm

theorem exists_fundDom_unip_herm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ μN : Measure (unip σ G.V H), μN.IsHaarMeasure →
    ∃ 𝓕 : Set (unip σ G.V H), IsFundamentalDomain ((ratU σ G.V.J).subgroupOf (unip σ G.V H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG _ μN hμ
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hV := hG.hV
  have hH := hC.hH
  have hspan : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (u : Fin b → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (G.V.L : Set (Fin (b + 2) → E)) := by
      rw [hV.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hB.cm
  let W' : Spc F E (b + 2) := ⟨δ • G.V.J, G.V.L, G.V.θ, G.V.bas⟩
  let H'' : Plane E (b + 2) b := ⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩
  have hform : ∀ v w, form σ W'.J v w = δ * form σ G.V.J v w := form_smul_mat σ G.V.J δ
  have hσt : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]
  have hxx : form σ W'.J H''.x H''.x = 0 := by rw [hform]; show δ * form σ G.V.J H.x H.x = 0; rw [hH.xx, mul_zero]
  have hyy : form σ W'.J H''.y H''.y = 0 := by
    rw [hform]; show δ * form σ G.V.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
    rw [form_smul_left, form_smul_right, hH.yy]; ring
  have hxy : form σ W'.J H''.x H''.y = 1 := by
    rw [hform]; show δ * form σ G.V.J H.x ((-δ⁻¹) • H.y) = 1
    rw [form_smul_right, hH.xy, hσt, mul_one, mul_inv_cancel₀ hδ0]
  have horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0 := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [hform]; show δ * form σ G.V.J (H.ι *ᵥ u) H.x = 0; rw [(hH.orth u).1, mul_zero]
    · rw [hform]; show δ * form σ G.V.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0; rw [form_smul_right, (hH.orth u).2]; ring
  have hspan'' : ∀ v : Fin (b + 2) → E, ∃ (s t : E) (u : Fin b → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y := by
    intro v
    obtain ⟨s, t, u, hv⟩ := hspan v
    refine ⟨s, t * -δ, u, ?_⟩
    show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y
    rw [smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]
  have horthA : ∀ z, hA σ W'.J (incM F H''.ι *ᵥ z) (incV F H''.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (horth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H''.ι i j) = H''.ι.col j from rfl, h1, map_zero, mul_zero]
  have hyp : Hyp σ W' H'' := by
    refine ⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero], horthA⟩
    show σ (δ * G.V.J j i) = -(δ * G.V.J i j)
    rw [map_mul, hδ, hV.herm]; ring
  obtain ⟨K', hK', hcov'⟩ := cocompact hyp hxx hyy hxy horth hspan''
  have hUG := UG_smul (F := F) σ G.V.J hδ0
  let φ : UA σ W'.J →* UA σ G.V.J := Subgroup.inclusion hUG.le
  let φ' : UA σ G.V.J →* UA σ W'.J := Subgroup.inclusion hUG.ge
  have hmap : (unip σ W' H'').map φ ≤ unip σ G.V H := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hmap' : (unip σ G.V H).map φ' ≤ unip σ W' H'' := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  let Ψ : unip σ W' H'' → unip σ G.V H := fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩
  have hΨ : Continuous Ψ :=
    Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
  have hcov : ∀ g : unip σ G.V H, ∃ γ : (ratU σ G.V.J).subgroupOf (unip σ G.V H), γ • g ∈ Ψ '' K' := by
    intro g
    obtain ⟨γ', hγ'⟩ := hcov' ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩
    refine ⟨⟨Ψ γ'.1, ?_⟩, ⟨_, hγ', ?_⟩⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ'.2)))
    · exact unip_ext rfl
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ G.V.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ G.V H hx0
  haveI : LocallyCompactSpace (unip σ G.V H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.V H) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ G.V.J (unip σ G.V H)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ G.V.J (unip σ G.V H)
  haveI := hμ
  exact exists_fundDom_pos_finite _ (Ψ '' K') (hK'.image hΨ) hcov μN

end GlobalTheory.UnipMassHerm
