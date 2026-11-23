import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignFrameUnitaryIso
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRep
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MeasureTheory Matrix NumberField
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchPI

open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted

section Rep

variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_rep {σ : K →* (H →L[ℂ] H)} (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (k : K) (a b : H) :
    ⟪σ k a, σ k b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (LinearIsometry.mk (σ k).toLinearMap (hiso k)).inner_map_map a b

theorem rep_mul_apply (σ : K →* (H →L[ℂ] H)) (a b : K) (x : H) : σ (a * b) x = σ a (σ b x) := by
  rw [map_mul, ContinuousLinearMap.mul_apply]

theorem rep_inv_apply (σ : K →* (H →L[ℂ] H)) (k : K) (x : H) : σ k (σ k⁻¹ x) = x := by
  rw [← rep_mul_apply, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]

theorem inner_rep_inv {σ : K →* (H →L[ℂ] H)} (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (k : K) (a b : H) :
    ⟪σ k⁻¹ a, b⟫_ℂ = ⟪a, σ k b⟫_ℂ := by
  rw [← inner_rep hiso k (σ k⁻¹ a) b, rep_inv_apply]

theorem schur_scalar (σ : K →* (H →L[ℂ] H)) (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS0 : S ≠ ⊥)
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S)
    (hirr : ∀ T : Submodule ℂ H, T ≤ S → (∀ k, ∀ x ∈ T, σ k x ∈ T) → T = ⊥ ∨ T = S)
    (A : H →ₗ[ℂ] H) (hA : ∀ x ∈ S, A x ∈ S) (hc : ∀ k, ∀ x ∈ S, A (σ k x) = σ k (A x)) :
    ∃ c : ℂ, ∀ x ∈ S, A x = c • x := by
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (A.restrict hA)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : A (v : H) = c • (v : H) := congrArg Subtype.val hv.apply_eq_smul
  let T : Submodule ℂ H := S ⊓ LinearMap.ker (A - c • LinearMap.id)
  have hmem : ∀ x, x ∈ T ↔ x ∈ S ∧ A x = c • x := fun x => by
    simp [T, sub_eq_zero]
  have hT : T ≤ S := inf_le_left
  have hst : ∀ k, ∀ x ∈ T, σ k x ∈ T := fun k x hx => by
    obtain ⟨h1, h2⟩ := (hmem x).1 hx
    exact (hmem _).2 ⟨hS k x h1, by rw [hc k x h1, h2, map_smul]⟩
  refine ⟨c, ?_⟩
  rcases hirr T hT hst with h | h
  · exfalso
    have : (v : H) ∈ T := (hmem _).2 ⟨v.2, hv1⟩
    rw [h, Submodule.mem_bot] at this
    exact hv.2 (Subtype.ext this)
  · intro x hx
    exact ((hmem x).1 (h ▸ hx)).2

theorem exists_minimal_stable (σ : K →* (H →L[ℂ] H)) (S₀ : Submodule ℂ H) [FiniteDimensional ℂ S₀] (h0 : S₀ ≠ ⊥)
    (hS₀ : ∀ k, ∀ x ∈ S₀, σ k x ∈ S₀) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ (∀ k, ∀ x ∈ S, σ k x ∈ S) ∧
      ∀ T : Submodule ℂ H, T ≤ S → (∀ k, ∀ x ∈ T, σ k x ∈ T) → T = ⊥ ∨ T = S := by
  obtain ⟨S, ⟨hle, hne, hst⟩, hmin⟩ := (measure fun T : Submodule ℂ H => Module.finrank ℂ T).wf.has_min
    {T | T ≤ S₀ ∧ T ≠ ⊥ ∧ ∀ k, ∀ x ∈ T, σ k x ∈ T} ⟨S₀, le_rfl, h0, hS₀⟩
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  refine ⟨S, inferInstance, hne, hst, fun T hT hTs => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hmin T ⟨hT.trans hle, hcon.1, hTs⟩ (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hT hcon.2))

end Rep

section Avg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem exists_rankOneAvg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) (s u : H) :
    ∃ B : H →L[ℂ] H, ∀ x, B x = ∫ k, ⟪σ k s, x⟫_ℂ • σ k u ∂μ := by
  have hi : ∀ x, Integrable (fun k => ⟪σ k s, x⟫_ℂ • σ k u) μ := fun x =>
    integrable_cont (((hc s).inner continuous_const).smul (hc u))
  let L : H →ₗ[ℂ] H :=
    { toFun := fun x => ∫ k, ⟪σ k s, x⟫_ℂ • σ k u ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hi a) (hi b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (‖s‖ * ‖u‖) fun x => ?_, fun x => rfl⟩
  have hb : ∀ k, ‖⟪σ k s, x⟫_ℂ • σ k u‖ ≤ ‖s‖ * ‖u‖ * ‖x‖ := fun k => by
    rw [norm_smul, hiso]
    have := norm_inner_le_norm (𝕜 := ℂ) (σ k s) x
    rw [hiso] at this
    calc _ ≤ ‖s‖ * ‖x‖ * ‖u‖ := by gcongr
      _ = _ := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => ⟪σ k s, x⟫_ℂ • σ k u)
    (C := ‖s‖ * ‖u‖ * ‖x‖) (Filter.Eventually.of_forall hb)
  show ‖∫ k, ⟪σ k s, x⟫_ℂ • σ k u ∂μ‖ ≤ _
  simpa using this

variable [μ.IsMulLeftInvariant]

theorem rankOneAvg_comm (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {s u : H}
    {B : H →L[ℂ] H} (hB : ∀ x, B x = ∫ k, ⟪σ k s, x⟫_ℂ • σ k u ∂μ) (g : K) (x : H) :
    B (σ g x) = σ g (B x) := by
  have hi : Integrable (fun k => ⟪σ k s, x⟫_ℂ • σ k u) μ :=
    integrable_cont (((hc s).inner continuous_const).smul (hc u))
  rw [hB, hB, ← (σ g).integral_comp_comm hi,
    ← integral_mul_left_eq_self (μ := μ) (fun k => ⟪σ k s, σ g x⟫_ℂ • σ k u) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show ⟪σ (g * k) s, σ g x⟫_ℂ • σ (g * k) u = σ g (⟪σ k s, x⟫_ℂ • σ k u)
  rw [rep_mul_apply, rep_mul_apply, inner_rep hiso, map_smul]

theorem schur_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] (hS0 : S ≠ ⊥) (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S)
    (hirr : ∀ T : Submodule ℂ H, T ≤ S → (∀ k, ∀ x ∈ T, σ k x ∈ T) → T = ⊥ ∨ T = S)
    {s t : H} (hs : s ∈ S) (ht : t ∈ S) :
    (Module.finrank ℂ S : ℂ) • ∫ k, ⟪σ k s, s⟫_ℂ • σ k t ∂μ = ⟪s, t⟫_ℂ • s := by
  obtain ⟨B, hB⟩ := exists_rankOneAvg μ hiso hc s t
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S
  have hi : ∀ x, Integrable (fun k => ⟪σ k s, x⟫_ℂ • σ k t) μ := fun x =>
    integrable_cont (((hc s).inner continuous_const).smul (hc t))
  have hin : ∀ w x, ⟪w, B x⟫_ℂ = ∫ k, ⟪σ k s, x⟫_ℂ * ⟪w, σ k t⟫_ℂ ∂μ := fun w x => by
    rw [hB, ← integral_inner (hi x)]
    simp only [inner_smul_right]
  have hBS : ∀ x, B x ∈ S := fun x => by
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hin]
    have : ∀ k, ⟪w, σ k t⟫_ℂ = 0 := fun k => Submodule.inner_left_of_mem_orthogonal (hS k t ht) hw
    simp [this]
  obtain ⟨c, hcS⟩ := schur_scalar σ S hS0 hS hirr (B : H →ₗ[ℂ] H) (fun x _ => hBS x)
    fun k x _ => rankOneAvg_comm μ hiso hc hB k x
  set b := stdOrthonormalBasis ℂ S
  have h1 : ∑ i, ⟪(b i : H), B (b i)⟫_ℂ = (Module.finrank ℂ S : ℂ) * c := by
    have : ∀ i, ⟪(b i : H), B (b i)⟫_ℂ = c := fun i => by
      have e := hcS (b i) (b i).2
      have e' : B (b i : H) = c • (b i : H) := e
      have e1 : ⟪b i, b i⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
      rw [e', inner_smul_right, ← Submodule.coe_inner, e1, mul_one]
    simp [this]
  have h2 : ∑ i, ⟪(b i : H), B (b i)⟫_ℂ = ⟪s, t⟫_ℂ := by
    simp only [hin]
    rw [← integral_finsetSum _ fun i _ => integrable_cont
      (((hc s).inner continuous_const).mul (continuous_const.inner (hc t)))]
    have : ∀ k, ∑ i, ⟪σ k s, (b i : H)⟫_ℂ * ⟪(b i : H), σ k t⟫_ℂ = ⟪s, t⟫_ℂ := fun k => by
      have := b.sum_inner_mul_inner ⟨σ k s, hS k s hs⟩ ⟨σ k t, hS k t ht⟩
      simp only [Submodule.coe_inner] at this
      rw [this, inner_rep hiso]
    simp [this]
  have hs' : B s = c • s := hcS s hs
  rw [← hB, hs', smul_smul, h1.symm.trans h2]

theorem avg_idem (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {s : H} {d : ℂ}
    {E : H →L[ℂ] H} (hE : ∀ u, E u = ∫ k, (d * ⟪σ k s, s⟫_ℂ) • σ k u ∂μ) (hs : E s = s) : E * E = E := by
  have hE' : ∀ u, E u = ∫ k, (d * ⟪σ k s, s⟫_ℂ) • σ k u ∂μ := hE
  ext u
  obtain ⟨B, hB⟩ := exists_rankOneAvg μ hiso hc s u
  have h1 : E u = d • B s := by
    rw [hE, hB, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [smul_smul]
  have hi : Integrable (fun k => (d * ⟪σ k s, s⟫_ℂ) • σ k s) μ :=
    integrable_cont ((continuous_const.mul ((hc s).inner continuous_const)).smul (hc s))
  have h2 : E (B s) = B s := by
    conv_rhs => rw [← hs, hE s, ← B.integral_comp_comm hi]
    rw [hE]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show (d * ⟪σ k s, s⟫_ℂ) • σ k (B s) = B ((d * ⟪σ k s, s⟫_ℂ) • σ k s)
    rw [map_smul, rankOneAvg_comm μ hiso hc hB]
  rw [ContinuousLinearMap.mul_apply, h1, map_smul, h2]

theorem avg_symm [μ.IsInvInvariant] (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {s : H}
    {d : ℝ} {E : H →L[ℂ] H} (hE : ∀ u, E u = ∫ k, ((d : ℂ) * ⟪σ k s, s⟫_ℂ) • σ k u ∂μ) (u w : H) :
    ⟪E u, w⟫_ℂ = ⟪u, E w⟫_ℂ := by
  have hi : ∀ x, Integrable (fun k => ((d : ℂ) * ⟪σ k s, s⟫_ℂ) • σ k x) μ := fun x =>
    integrable_cont ((continuous_const.mul ((hc s).inner continuous_const)).smul (hc x))
  rw [← inner_conj_symm, hE u, hE w, ← integral_inner (hi u), ← integral_inner (hi w), ← integral_conj,
    ← integral_inv_eq_self (fun k => ⟪u, ((d : ℂ) * ⟪σ k s, s⟫_ℂ) • σ k w⟫_ℂ) μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show conj ⟪w, ((d : ℂ) * ⟪σ k s, s⟫_ℂ) • σ k u⟫_ℂ = ⟪u, ((d : ℂ) * ⟪σ k⁻¹ s, s⟫_ℂ) • σ k⁻¹ w⟫_ℂ
  have h1 : ⟪σ k u, w⟫_ℂ = ⟪u, σ k⁻¹ w⟫_ℂ := by simpa using inner_rep_inv hiso k⁻¹ u w
  rw [inner_conj_symm, inner_smul_left, inner_smul_right, inner_rep_inv hiso k s s, h1, map_mul, Complex.conj_ofReal,
    inner_conj_symm]

end Avg

theorem rFin_coef {K : Type} [Group K] [TopologicalSpace K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : K →* (H →L[ℂ] H)} (hc : ∀ v, Continuous fun x => σ x v) (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    (hS : ∀ k, ∀ x ∈ S, σ k x ∈ S) {s : H} (hs : s ∈ S) (d : ℂ) :
    RFin (fun k => d * ⟪σ k s, s⟫_ℂ) (Module.finrank ℂ S) := by
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => d * ⟪σ x (B i), s⟫_ℂ, fun i => continuous_const.mul ((hc _).inner continuous_const), fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ s, hS _ s hs⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ s = ∑ i, B.repr ⟨σ k⁻¹ s, hS _ s hs⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ s, hS _ s hs⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show d * ⟪σ (x * k⁻¹) s, s⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_projAvg (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (σ : K →* (H →L[ℂ] H)) (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) :
    ∃ (e : K → ℂ) (d : ℕ) (E : H →L[ℂ] H), Continuous e ∧ RFin e d ∧ (∀ u, E u = ∫ k, e k • σ k u ∂μ) ∧
      E ≠ 0 ∧ E * E = E ∧ ∀ u w, ⟪E u, w⟫_ℂ = ⟪u, E w⟫_ℂ := by
  obtain ⟨S₀, hfd, hne, hst⟩ : ∃ S₀ : Submodule ℂ H, FiniteDimensional ℂ S₀ ∧ S₀ ≠ ⊥ ∧ ∀ k, ∀ x ∈ S₀, σ k x ∈ S₀ := by
    have hd := GlobalTheory.CompactRep.dense_finite_vectors K H σ hiso hc
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    obtain ⟨v, hv, hv0⟩ : ∃ v ∈ {v : H | ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧
        ∀ k, ∀ x ∈ S, σ k x ∈ S}, v ≠ 0 := by
      obtain ⟨v, hv, hvm⟩ := hd.inter_open_nonempty {0}ᶜ isOpen_compl_singleton ⟨x, hx⟩
      exact ⟨v, hvm, hv⟩
    obtain ⟨S, hS, hvS, hSt⟩ := hv
    exact ⟨S, hS, fun h => hv0 (by simpa [h] using hvS), hSt⟩
  obtain ⟨S, hfd', hS0, hS, hirr⟩ := exists_minimal_stable σ S₀ hne hst
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  set s : H := ((‖s₀‖ : ℂ)⁻¹) • s₀ with hs_def
  have hs : s ∈ S := S.smul_mem _ hs₀
  have hn : ‖s‖ = 1 := by
    rw [hs_def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hs₀0)]
  have hss : ⟪s, s⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hn]; simp
  have hs0 : s ≠ 0 := fun h => by simp [h] at hn
  set d : ℕ := Module.finrank ℂ S with hd
  have hce : Continuous fun k => (((d : ℝ) : ℂ) * ⟪σ k s, s⟫_ℂ) := continuous_const.mul ((hc s).inner continuous_const)
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc hce
  have hEs : E s = s := by
    have := schur_avg μ hiso hc S hS0 hS hirr hs hs
    rw [hss, one_smul, ← integral_smul] at this
    rw [hE]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)) this
    simp only [smul_smul, Complex.ofReal_natCast, hd]
  refine ⟨_, Module.finrank ℂ S, E, hce, rFin_coef hc S hS hs _, hE, fun h => hs0 ?_, avg_idem μ hiso hc hE hEs,
    avg_symm μ hiso hc hE⟩
  rw [← hEs, h]; rfl

theorem isPIProj_of_equiv {G G' H : Type} [Group G] [Group G'] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (φ : G ≃* G') (ρ : G →* (H →L[ℂ] H)) {E : H →L[ℂ] H} (h : IsPIProj (ρ.comp φ.symm.toMonoidHom) E) :
    IsPIProj ρ E := by
  obtain ⟨h0, h1, h2, h3, M, h4⟩ := h
  refine ⟨h0, h1, h2, fun T hT => h3 T fun g => hT _, M, fun g => ?_⟩
  simpa using h4 fun i => φ (g i)

open PI.UpqRep in

theorem exists_isPIProj_UJ {n : ℕ} (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (ρ : UJ ε →* (H →L[ℂ] H)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hc : ∀ v, Continuous fun g => ρ g v) : ∃ P, IsPIProj ρ P := by
  obtain ⟨U, hU, hiwa⟩ := iwasawa_decomposition_unitary_group n ε
  let μ : Measure (KG ε) := GlobalTheory.haarProb _
  haveI : SecondCountableTopology (KG ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨e, d, E, he, hfin, hE, h0, h1, h2⟩ := exists_projAvg (KG ε) μ H (ρ.comp (KG ε).subtype)
    (fun k u => hiso k u) (fun u => (hc u).comp continuous_subtype_val)
  choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)
  let Tr : Set (UJ ε) := {s | (stdU ε hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU ε hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU ε hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g := fun g => by
      show U * (Uᴴ * toM g * U) * Uᴴ = _
      calc U * (Uᴴ * toM g * U) * Uᴴ = (U * Uᴴ) * toM g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toM g) g.2
    obtain ⟨k, rfl⟩ := exists_elt (Kset_sub hk)
    obtain ⟨s, rfl⟩ := exists_elt hs
    exact ⟨k, hk, s, ht, injective_coeMatrix ε hg⟩
  have hPI : ∀ g : Fin (d ^ 2 + 1) → UJ ε, stdPoly E (fun i => ρ (g i)) = 0 := fun g =>
    transfer_holds (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g
      (fun ι _ _ ρ' hρ' E' hE' => goodPI_of small_irreducible_representation (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin
        (Nat.lt_succ_self _) ι ρ' hρ' E' hE' g)
      H ρ hc E hE
  refine ⟨E, h0, h1, h2, fun T hT => ?_, _, hPI⟩
  ext u
  show T (E u) = E (T u)
  have hint : Integrable (fun k : KG ε => e k • (ρ.comp (KG ε).subtype) k u) μ :=
    integrable_cont (he.smul ((hc u).comp continuous_subtype_val))
  rw [hE, hE, ← T.integral_comp_comm hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show T (e k • ρ k u) = e k • ρ k (T u)
  have := DFunLike.congr_fun (hT k) u
  rw [map_smul]
  exact congrArg (e k • ·) this

theorem archPI : StArchPI := by
  intro F E _ _ _ _ _ σ hCM n J hJ w H _ _ _ _ ρ hρ
  obtain ⟨c, ε, hb⟩ := GlobalTheory.AdelicU.Frames.exists_arch_frame hCM hJ w
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  let φ : GlobalTheory.AdelicU.GArch σ J w ≃ₜ* PI.UpqRep.UJ ε := GlobalTheory.FrameIsoReal.frameEquiv σ J hCM τ c hb
  obtain ⟨P, hP⟩ := exists_isPIProj_UJ ε H (ρ.comp φ.symm.toMulEquiv.toMonoidHom)
    (fun g v => hρ.norm_apply _ v) (fun v => (hρ.continuous_apply v).comp φ.symm.continuous)
  exact ⟨P, isPIProj_of_equiv φ.toMulEquiv ρ hP⟩

end GlobalTheory.CompanionTheory.ArchPI
