import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectQuotientMeasureConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationMeasurePreservingSemidirectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectMeasureRestrictionNormalPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableTransversalMeasureExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizingElementFundamentalDomainScalingStatement

open MeasureTheory Pointwise

namespace GlobalTheory.SupMeas

theorem mem_sup_exists_mul {G : Type} [Group G] (N Q : Subgroup G) (hQ : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) :
    ∀ h ∈ Q ⊔ N, ∃ n ∈ N, ∃ q ∈ Q, n * q = h := by
  let P : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ q ∈ Q, n * q = x}
      one_mem' := ⟨1, N.one_mem, 1, Q.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, q, hq, rfl⟩ ⟨n', hn', q', hq', rfl⟩
        exact ⟨n * (q * n' * q⁻¹), N.mul_mem hn (hQ q hq n' hn'), q * q', Q.mul_mem hq hq', by group⟩
      inv_mem' := by
        rintro _ ⟨n, hn, q, hq, rfl⟩
        exact ⟨q⁻¹ * n⁻¹ * q⁻¹⁻¹, hQ _ (Q.inv_mem hq) _ (N.inv_mem hn), q⁻¹, Q.inv_mem hq, by group⟩ }
  have hle : Q ⊔ N ≤ P :=
    sup_le (fun q hq => ⟨1, N.one_mem, q, hq, one_mul q⟩) (fun n hn => ⟨n, hn, 1, Q.one_mem, mul_one n⟩)
  intro h hh
  exact hle hh

theorem haar_invariances {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (Γ : Subgroup K) [Countable Γ] (μ : Measure K) [μ.IsHaarMeasure] (E : Set K) (hE : IsFundamentalDomain Γ E μ)
    (h0 : μ E ≠ 0) (h1 : μ E ≠ ⊤) :
    (∀ g : K, MeasurePreserving (· * g) μ μ) ∧ MeasurePreserving (fun x : K => x⁻¹) μ μ ∧
    ∀ φ : K ≃* K, Continuous φ → Continuous φ.symm → (∀ γ ∈ Γ, φ γ ∈ Γ) → (∀ γ ∈ Γ, φ.symm γ ∈ Γ) →
      MeasurePreserving φ μ μ := by

  have key : ∀ f : K → K, Measurable f → ∀ c : NNReal, μ.map f = c • μ → IsFundamentalDomain Γ (f ⁻¹' E) μ →
      MeasurePreserving f μ μ := by
    intro f hf c e hF
    have h3 : μ.map f E = μ E := by
      rw [Measure.map_apply₀ hf.aemeasurable
        (hE.nullMeasurableSet.mono_ac (by rw [e]; exact Measure.smul_absolutelyContinuous))]
      exact hF.measure_eq hE
    have hc : ((c : NNReal) : ENNReal) = 1 := by
      rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
      calc ((c : NNReal) : ENNReal) = c * μ E / μ E := (ENNReal.mul_div_cancel_right h0 h1).symm
        _ = 1 := by rw [h3, ENNReal.div_self h0 h1]
    exact ⟨hf, by rw [e, ENNReal.coe_eq_one.1 hc, one_smul]⟩
  have hRI : ∀ g : K, MeasurePreserving (· * g) μ μ := by
    intro g
    have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
    have hq : Measure.QuasiMeasurePreserving (· * g) μ μ :=
      ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
    refine key _ (measurable_mul_const g) _ e ?_
    exact hE.preimage_of_equiv hq (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  haveI : μ.IsMulRightInvariant := ⟨fun g => (hRI g).map_eq⟩
  have hinv : μ.inv = μ := by
    have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
    set c := μ.inv.haarScalarFactor μ
    have h2 : μ = (c ^ 2 : NNReal) • μ := by
      have : Measure.map Inv.inv (Measure.map Inv.inv μ) = (c ^ 2 : NNReal) • μ := by
        rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
      rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at this
      simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using this
    have h3 : ((c ^ 2 : NNReal) : ENNReal) = 1 := by
      have h4 := congrArg (fun ν : Measure K => ν E) h2
      simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
      calc ((c ^ 2 : NNReal) : ENNReal) = (c ^ 2 : NNReal) * μ E / μ E := (ENNReal.mul_div_cancel_right h0 h1).symm
        _ = 1 := by rw [← h4, ENNReal.div_self h0 h1]
    have h5 : c = 1 := by
      have : c ^ 2 = 1 := by exact_mod_cast h3
      exact (pow_eq_one_iff_of_nonneg (bot_le : (0 : NNReal) ≤ c) two_ne_zero).1 this
    rw [hc, h5, one_smul]
  refine ⟨hRI, ⟨measurable_inv, hinv⟩, ?_⟩
  intro φ hφ hφs hΓ hΓs
  haveI := MulEquiv.isHaarMeasure_map μ φ hφ hφs
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map φ) μ
  have hq : Measure.QuasiMeasurePreserving φ μ μ :=
    ⟨hφ.measurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
  refine key _ hφ.measurable _ e ?_
  refine hE.preimage_of_equiv hq (e := fun γ : Γ => (⟨φ.symm γ, hΓs γ γ.2⟩ : Γ))
    (Function.bijective_iff_has_inverse.2 ⟨fun γ => ⟨φ γ, hΓ γ γ.2⟩,
      fun γ => Subtype.ext (by simp), fun γ => Subtype.ext (by simp)⟩) fun γ x => ?_
  simp only [Subgroup.smul_def, smul_eq_mul, map_mul, MulEquiv.apply_symm_apply]

end GlobalTheory.SupMeas

namespace GlobalTheory.SupMeas

theorem exists_supMeas : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) [Countable Q] (m : G), IsClosed (N : Set G) → (∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) → (∀ n ∈ N, m * n * m⁻¹ ∈ N ∧ m⁻¹ * n * m ∈ N) → (∀ q ∈ Q, m⁻¹ * q * m * q⁻¹ ∈ N) → ∀ νN : Measure N, νN.IsHaarMeasure → ∀ E : Set N, IsFundamentalDomain (Q.subgroupOf N) E νN → νN E ≠ 0 → νN E ≠ ⊤ → ∀ c : ENNReal, c ≠ 0 → c ≠ ⊤ → (∀ S : Set N, c * νN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = νN S) → Q.map (MulAut.conj m⁻¹).toMonoidHom ≤ Q ⊔ N ∧ ∃ ν : Measure ↥(Q ⊔ N), SFinite ν ∧ MeasurePreserving (fun p : ↥(Q ⊔ N) => p⁻¹) ν ν ∧ (∀ γ ∈ Q.subgroupOf (Q ⊔ N), MeasurePreserving (fun p : ↥(Q ⊔ N) => γ * p) ν ν) ∧ (∀ γ ∈ (Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (Q ⊔ N), MeasurePreserving (fun p : ↥(Q ⊔ N) => γ * p) ν ν) ∧ ∃ E₁ E₂ : Set ↥(Q ⊔ N), IsFundamentalDomain (Q.subgroupOf (Q ⊔ N)) E₁ ν ∧ IsFundamentalDomain ((Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (Q ⊔ N)) E₂ ν ∧ c * ν E₂ = ν E₁ ∧ ν E₁ ≠ 0 ∧ ν E₁ ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ N Q _ m hN hQ hm hmQ νN hνN E hE hE0 hEtop c hc0 hctop hmod
  have memQ₂ : ∀ x, x ∈ Q.map (MulAut.conj m⁻¹).toMonoidHom ↔ ∃ q ∈ Q, m⁻¹ * q * m = x := by
    intro x; simp [Subgroup.mem_map, MulAut.conj_apply]
  have hle : Q.map (MulAut.conj m⁻¹).toMonoidHom ≤ Q ⊔ N := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (memQ₂ x).1 hx
    have e : m⁻¹ * q * m = (m⁻¹ * q * m * q⁻¹) * q := by group
    rw [e]; exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hmQ q hq)) (Subgroup.mem_sup_left hq)
  refine ⟨hle, ?_⟩
  have hdec := mem_sup_exists_mul N Q hQ
  have hnorm : ∀ h ∈ Q ⊔ N, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    obtain ⟨n₀, hn₀, q, hq, rfl⟩ := hdec h hh
    have e : n₀ * q * n * (n₀ * q)⁻¹ = n₀ * (q * n * q⁻¹) * n₀⁻¹ := by group
    rw [e]; exact N.mul_mem (N.mul_mem hn₀ (hQ q hq n hn)) (N.inv_mem hn₀)
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (Q.subgroupOf N) :=
    Function.Injective.countable (f := fun x : Q.subgroupOf N => (⟨(x : N), x.2⟩ : Q))
      (fun x y hxy => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy)))
  obtain ⟨hR, hI, hφ⟩ := haar_invariances (Q.subgroupOf N) νN E hE hE0 hEtop
  have hC : ∀ h ∈ Q ⊔ N, ∀ f : N → N, (∀ n, (f n : G) = h * n * h⁻¹) → MeasurePreserving f νN νN := by
    intro h hh f hf
    obtain ⟨n₀, hn₀, q, hq, rfl⟩ := hdec h hh
    let φ : N ≃* N :=
      { toFun := fun n => ⟨q * n * q⁻¹, hQ q hq n n.2⟩
        invFun := fun n => ⟨q⁻¹ * n * q, by simpa using hQ q⁻¹ (Q.inv_mem hq) n n.2⟩
        left_inv := fun n => Subtype.ext (by simp [mul_assoc])
        right_inv := fun n => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hφc : Continuous φ := continuous_induced_rng.2
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hφs : Continuous φ.symm := continuous_induced_rng.2
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hmp := hφ φ hφc hφs
      (fun γ hγ => by
        rw [Subgroup.mem_subgroupOf] at hγ ⊢
        exact Q.mul_mem (Q.mul_mem hq hγ) (Q.inv_mem hq))
      (fun γ hγ => by
        rw [Subgroup.mem_subgroupOf] at hγ ⊢
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hγ) hq)
    have e : f = (fun x => (⟨n₀, hn₀⟩ : N) * x) ∘ (· * (⟨n₀, hn₀⟩ : N)⁻¹) ∘ φ := by
      funext x; apply Subtype.ext; rw [hf]
      simp only [Function.comp_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      change _ = n₀ * (q * x * q⁻¹ * n₀⁻¹)
      group
    rw [e]
    exact (measurePreserving_mul_left νN _).comp ((hR _).comp hmp)
  obtain ⟨hSF, hL⟩ := GlobalTheory.T.semidirect_quotient_measure_conjugation_invariant N Q hdec hnorm νN hR hC
  have hInv := GlobalTheory.T.conjugation_measure_preserving_semidirect N Q hnorm νN hR hI hC
  have hmass := GlobalTheory.T.semidirect_measure_restriction_normal_part N Q hN hdec νN hR
  have covQ : ∀ h ∈ Q ⊔ N, ∃ r ∈ Q, r * h ∈ N := by
    intro h hh
    obtain ⟨n, hn, q, hq, rfl⟩ := hdec h hh
    refine ⟨q⁻¹, Q.inv_mem hq, ?_⟩
    have e : q⁻¹ * (n * q) = q⁻¹ * n * q⁻¹⁻¹ := by group
    rw [e]; exact hQ _ (Q.inv_mem hq) n hn
  have covQ₂ : ∀ h ∈ Q ⊔ N, ∃ r ∈ Q.map (MulAut.conj m⁻¹).toMonoidHom, r * h ∈ N := by
    intro h hh
    obtain ⟨n, hn, q, hq, rfl⟩ := hdec h hh
    refine ⟨m⁻¹ * q⁻¹ * m, (memQ₂ _).2 ⟨q⁻¹, Q.inv_mem hq, rfl⟩, ?_⟩
    have e : m⁻¹ * q⁻¹ * m * (n * q) = (m⁻¹ * q⁻¹ * m * q⁻¹⁻¹) * (q⁻¹ * n * q⁻¹⁻¹) := by group
    rw [e]; exact N.mul_mem (hmQ _ (Q.inv_mem hq)) (hQ _ (Q.inv_mem hq) n hn)
  haveI : Countable (Q.map (MulAut.conj m⁻¹).toMonoidHom) :=
    Function.Surjective.countable (f := fun q : Q => (⟨(MulAut.conj m⁻¹).toMonoidHom q, Subgroup.mem_map_of_mem _ q.2⟩ :
      Q.map (MulAut.conj m⁻¹).toMonoidHom))
      (fun x => by obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 x.2; exact ⟨⟨q, hq⟩, Subtype.ext e⟩)
  have hE' := GlobalTheory.T.normalizing_element_fundamental_domain_scaling N Q m hN hm νN E hE c hc0 hmod
  refine ⟨supMeas N Q νN, hSF, hInv, fun γ _ => hL γ, fun γ _ => hL γ, _, _,
    GlobalTheory.T.countable_transversal_measure_extension N Q Q hN covQ νN _ hmass hL E hE, GlobalTheory.T.countable_transversal_measure_extension N Q _ hN covQ₂ νN _ hmass hL _ hE', ?_, ?_, ?_⟩
  · rw [hmass, hmass]; exact hmod E
  · rw [hmass]; exact hE0
  · rw [hmass]; exact hEtop
end GlobalTheory.SupMeas
