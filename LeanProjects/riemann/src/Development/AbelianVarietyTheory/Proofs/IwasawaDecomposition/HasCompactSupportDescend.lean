import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarIsMulRightInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

theorem indicator_mul_left {K : Set G} : ∀ u ∈ H, ∀ g, ((H : Set G) * K).indicator (fun _ => (1 : ℂ)) (u * g) =
    ((H : Set G) * K).indicator (fun _ => (1 : ℂ)) g := by
  intro u hu g
  classical
  simp only [Set.indicator_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨v, hv, c, hc, e⟩
    exact ⟨u⁻¹ * v, H.mul_mem (H.inv_mem hu) hv, c, hc, by simp only at e; simp [mul_assoc, e]⟩
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact ⟨u * v, H.mul_mem hu hv, c, hc, mul_assoc _ _ _⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

theorem exists_invariant_form [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (hH : IsClosed (H : Set G))
    (uG : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular G) (uH : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular H)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ∃ I : (G → ℂ) →ₗ[ℂ] ℂ,
      (∀ f : G → ℂ, (∀ u ∈ H, ∀ g, f (u * g) = f g) → Continuous f →
        (∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) →
        ∀ x, I (fun g => f (g * x)) = I f) ∧
      I (((H : Set G) * (K : Set G)).indicator fun _ => 1) ≠ 0 := by
  borelize (G ⧸ H)
  obtain ⟨⟨μ, hμ⟩, -⟩ := GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause G H hH uG uH
  have := hμ.finiteOnCompacts
  have := hμ.invariant
  have := hμ.regular
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Integrable (descend H f) μ}
      zero_mem' := by simp
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact hf.add hg
      smul_mem' := fun c f hf => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact hf.smul c }
  let J : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, descend H f q ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c (descend H f) }
  obtain ⟨I, hI⟩ := J.exists_extend
  have hIJ : ∀ f, Integrable (descend H f) μ → I f = ∫ q, descend H f q ∂μ := fun f hf =>
    LinearMap.congr_fun hI ⟨f, hf⟩
  refine ⟨I, fun f hf hc ⟨C, hC, hs⟩ x => ?_, ?_⟩
  · have h1 : Integrable (descend H f) μ :=
      (continuous_descend hf hc).integrable_of_hasCompactSupport (hasCompactSupport_descend hf hC hs)
    have h2 : Integrable (descend H fun g => f (g * x)) μ := by
      rw [descend_mul_right hf]
      exact (measurePreserving_smul x⁻¹ μ).integrable_comp_of_integrable h1
    rw [hIJ _ h1, hIJ _ h2, descend_mul_right hf]
    exact integral_smul_eq_self (descend H f)
  · set U : Set (G ⧸ H) := QuotientGroup.mk '' (K : Set G)
    have hUo : IsOpen U := QuotientGroup.isOpenMap_coe _ hKo
    have hUc : IsCompact U := hKc.image QuotientGroup.continuous_mk
    have e : descend H (((H : Set G) * (K : Set G)).indicator fun _ => 1) = U.indicator fun _ => 1 := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [descend_mk indicator_mul_left]
      classical
      simp only [Set.indicator_apply]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨c⁻¹, K.inv_mem hc, QuotientGroup.eq.2 ?_⟩
        have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, show u * c = g⁻¹ from e, inv_inv]
        rw [this]
        simpa using hu
      · rintro ⟨c, hc, e⟩
        exact ⟨_, H.inv_mem (QuotientGroup.eq.1 e), _, K.inv_mem hc, by simp⟩
    have hpos : 0 < μ U :=
      measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.ne_zero hUo ⟨_, 1, K.one_mem, rfl⟩
    rw [hIJ _ (e ▸ (integrable_indicator_iff hUo.measurableSet).2
      (integrableOn_const hUc.measure_lt_top.ne)), e, integral_indicator_const _ hUo.measurableSet]
    simpa [Measure.real, ENNReal.toReal_eq_zero_iff] using ⟨hpos.ne', hUc.measure_lt_top.ne⟩

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

theorem isTestFun_indicator :
    IsTestFun (((unipB k (Fin m) : Set (GL (Fin m) k)) * (KO k (Fin m) : Set (GL (Fin m) k))).indicator
      fun _ => (1 : ℂ)) := by
  refine ⟨indicator_mul_left, ?_, _, isCompact_KO, fun g hg => ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
      ⟨isClosed_unipB.mul_right_of_isCompact isCompact_KO, isOpen_KO.mul_left⟩).isLocallyConstant
  · obtain ⟨u, hu, c, hc, e⟩ := Set.mem_of_indicator_ne_zero hg
    exact ⟨u, hu, c, hc, e.symm⟩

theorem exists_isInvIntegral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) :
    ∃ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (f : GL (Fin m) k → ℂ), IsInvIntegral I ∧ IsTestFun f ∧ I f ≠ 0 := by
  borelize k
  obtain ⟨I, h1, h2⟩ := exists_invariant_form (H := unipB k (Fin m)) isClosed_unipB
    (fun μ _ => inferInstance)
    (fun μ hμ => @UnipHaar.haar_isMulRightInvariant k _ _ _ _ (Fin m) (Fin m) (fun _ => Unit) _ _ _ _ _ _
      (points (Fin m)) (inferInstance : MeasurableSpace (unipB k (Fin m)))
      (inferInstance : BorelSpace (unipB k (Fin m))) μ hμ)
    (KO k (Fin m)) isOpen_KO isCompact_KO
  exact ⟨I, _, fun f hf => h1 f hf.1 hf.2.1.continuous hf.2.2, isTestFun_indicator, h2⟩

end GlobalTheory.LocLanglands.InvInt
