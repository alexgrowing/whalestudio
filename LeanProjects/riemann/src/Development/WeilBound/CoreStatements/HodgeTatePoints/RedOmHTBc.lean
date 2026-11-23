import Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankWAddConj
import Development.WeilBound.CoreStatements.HodgeTatePoints.GeneratesDiffMap

noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem red_omHT_bc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv _ κ' V _ _ _ _
    Ω' _ _ _ _ P ι hred σ σ' d hφ hd hκ hproj
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have := isFractionRing_of_integers hv
  have hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1
      ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)
  obtain ⟨hd', h1, h2, h3, -⟩ := red_proj A K hAK E c hc p R N Ω D C v O hv κ' V Ω'
    (algebraMap A O) P ι hred σ σ' d hσ hφ hd hκ
  have hδ : algebraMap O C (algebraMap A O d) ≠ 0 :=
    (different_generator_dualInt O C E σ' _ hv.hom_inj
      (exists_diff_generator C v O hv E σ').1 hd').1
  obtain ⟨j₀, hj₀, -, hj₀'⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  have hfg : (D.omHT σ).FG := by
    have : IsNoetherian A D.om := isNoetherian_of_fg_of_noetherian _ D.om_lat.fg
    have h := (IsNoetherian.noetherian (D.om'.comap D.om.subtype)).map D.om.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 (om'_le_om D)] at h
    exact h.map _
  have : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hfg
  let α : D.omHT σ →ₗ[A] D.om := LinearMap.codRestrict D.om (d • (D.omHT σ).subtype) (by
    rintro ⟨_, x, hx, rfl⟩
    exact h1 x (om'_le_om D hx))
  let β : D.om →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ)
    ((eigProj D.ρΩ σ).restrictScalars A ∘ₗ ((p : A) ^ R • D.om.subtype))
    (fun x => ⟨_, pow_smul_mem_om' D x.2, rfl⟩)
  have hβα : β ∘ₗ α = ((p : A) ^ R * d) • LinearMap.id := by
    ext z
    change eigProj D.ρΩ σ ((p : A) ^ R • d • (z : Ω)) = ((p : A) ^ R * d) • (z : Ω)
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LatBasic.eigProj_of_mem (LatBasic.eigQuot_le_eigSp _ _ D.om' z.2), mul_smul]
  have hne : algebraMap A O ((p : A) ^ R * d) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_zero] at h'
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) hδ h'
  have hα : Function.Injective (α.baseChange O) := by
    have h : Function.Injective ((β.baseChange O) ∘ₗ (α.baseChange O)) := by
      rw [← LinearMap.baseChange_comp, hβα, LinearMap.baseChange_smul, LinearMap.baseChange_id]
      intro x y e
      change ((p : A) ^ R * d) • x = ((p : A) ^ R * d) • y at e
      rw [← algebraMap_smul O, ← algebraMap_smul O ((p : A) ^ R * d) y] at e
      exact smul_right_injective _ hne e
    exact Function.Injective.of_comp h
  obtain ⟨j₁, hj₁, hr₁⟩ := exists_lift (ι.comp α)
  have hj₁' : j₁ = j₀ ∘ₗ α.baseChange O := by
    refine LinearMap.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul o z =>
      have : o ⊗ₜ[A] z = o • ((1 : O) ⊗ₜ[A] z) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, hj₁, LinearMap.comp_apply j₀, LinearMap.baseChange_tmul, hj₀']
      rfl
  let s : Ω' →ₗ[O] Ω' :=
    ((algebraMap O C (algebraMap A O d))⁻¹ • (LinearMap.id : Ω' →ₗ[C] Ω')).restrictScalars O
  have hs : ∀ w, algebraMap A O d • s w = w := fun w => by
    change algebraMap A O d • (algebraMap O C (algebraMap A O d))⁻¹ • w = w
    rw [← algebraMap_smul C, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  have hinj : Function.Injective (s ∘ₗ j₁) := by
    have hs' : Function.Injective s := fun x y e => by rw [← hs x, e, hs]
    rw [hj₁']
    exact hs'.comp (hj₀.comp hα)
  have hrange : LinearMap.range (s ∘ₗ j₁) = P.omHT σ' := by
    have e : Set.range (ι.comp α) = ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z} := by
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨α z, ⟨z, z.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, e⟩, rfl⟩
        exact ⟨⟨z, hz⟩, congrArg ι (Subtype.ext e.symm)⟩
    rw [LinearMap.range_comp, hr₁, e, h3, ← Submodule.map_comp]
    have : s ∘ₗ (algebraMap A O d • LinearMap.id) = LinearMap.id := by
      ext w
      change s (algebraMap A O d • w) = w
      rw [map_smul, hs]
    rw [this, Submodule.map_id]
  refine ⟨s ∘ₗ j₁, hinj, hrange, fun z y e => ?_, ?_⟩
  · rw [LinearMap.comp_apply, hs, hj₁]
    exact congrArg ι (Subtype.ext e.symm)
  · have hl := (pt_om_block C v O hv E c hc κ' N V Ω' P σ').2.2.1
    rw [← finrank_baseChange_flat (O := O), ← LinearMap.finrank_range_of_inj hinj, hrange,
      ← finrank_lattice _ hl]
    have e : (latIn (P.omHT σ') (P.Ωsp σ')).map ((P.Ωsp σ').subtype.restrictScalars O) =
        P.omHT σ' := by
      rw [LatBasic.map_latIn]
      exact inf_eq_left.2 (LatBasic.eigQuot_le_eigSp _ _ _)
    conv_lhs => rw [← e]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm

theorem chart_rank : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d d' hp hκ hd hd' hP hP' htest
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero] at h'
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h'
  obtain ⟨𝔮, h𝔮⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {(p : A)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hprime : 𝔮.IsPrime := h𝔮.1.1
  have hmem : (p : A) ∈ 𝔮 := h𝔮.1.2 (Ideal.mem_span_singleton_self _)
  have hht : 𝔮.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔮) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    rintro rfl
    exact hp0 hmem
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, -, hred⟩ :=
    htest 𝔮 hprime hht hmem
  let _ : Algebra A O := φ.toAlgebra
  have hg : Function.Injective ((algebraMap O C).comp φ) := hv.hom_inj.comp hφ
  let ψ : K →+* C := IsFractionRing.lift hg
  have hψ : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h]
    exact (IsFractionRing.lift_algebraMap hg a').symm
  have hκ' : φ κ ∣ (p : O) ^ R := by
    have := map_dvd φ hκ
    rwa [map_pow, map_natCast] at this
  obtain ⟨_, -, -, -, e1⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ
    (ψ.comp σ) d (hψ σ) hd hκ' hP
  obtain ⟨_, -, -, -, e2⟩ := red_omHT_bc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) (ψ.comp (σ.comp c.toRingHom)) d' (hψ _) hd' hκ' hP'
  rw [e1, e2]
  exact finrank_Ω_add_Ω P hv hc (ψ.comp σ)

end PositivityTheory.HtPt.Gb
