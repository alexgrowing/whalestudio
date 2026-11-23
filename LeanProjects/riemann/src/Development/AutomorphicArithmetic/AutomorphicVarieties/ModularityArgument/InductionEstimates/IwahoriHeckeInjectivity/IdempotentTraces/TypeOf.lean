import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section General

private theorem swapC {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [CompactSpace X] [T2Space X] [T2Space Y]
    (κ : Measure X) [IsProbabilityMeasure κ] (ρ : Measure Y) [SFinite ρ] [IsFiniteMeasureOnCompacts ρ]
    (f : X → Y → ℂ) (hf : Continuous fun p : X × Y => f p.1 p.2) {T : Set Y} (hT : IsCompact T)
    (h0 : ∀ x y, f x y ≠ 0 → y ∈ T) : ∫ x, ∫ y, f x y ∂ρ ∂κ = ∫ y, ∫ x, f x y ∂κ ∂ρ := by
  refine integral_integral_swap (Continuous.integrable_of_hasCompactSupport hf
    (HasCompactSupport.intro (isCompact_univ.prod hT) ?_))
  rintro ⟨x, y⟩ hp
  by_contra hne
  exact hp ⟨trivial, h0 x y hne⟩

private theorem haarP (B : Type) [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [MeasurableSpace B]
    [BorelSpace B] : ∃ l : Measure B, IsProbabilityMeasure l ∧ ∀ b, MeasurePreserving (b * ·) l l :=
  ⟨Measure.haarMeasure ⊤, ⟨by simpa using Measure.haarMeasure_self (G := B) (K₀ := ⊤)⟩,
    fun b => measurePreserving_mul_left _ b⟩

variable {A B G : Type} [Group A] [Group B] [Group G] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace G] [BorelSpace A] [BorelSpace B]
  [BorelSpace G] [SecondCountableTopology A] [SecondCountableTopology G] [CompactSpace A] [CompactSpace B] [T2Space G]

private theorem pushT (m : A × B →* G) (hm : Continuous m) (κ : Measure A) [IsProbabilityMeasure κ]
    (hκ : ∀ a, MeasurePreserving (a * ·) κ κ) (l : Measure B) [IsProbabilityMeasure l]
    (hl : ∀ b, MeasurePreserving (b * ·) l l) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ (∀ᵐ k ∂ν, k ∈ m.range) ∧ (∀ k ∈ m.range, MeasurePreserving (k * ·) ν ν) ∧
      ∀ (F : G → ℂ) (f : A → ℂ), Continuous F → (∀ p, F (m p) = f p.1) → ∫ k, F k ∂ν = ∫ a, f a ∂κ := by
  have hmm : Measurable m := hm.measurable
  refine ⟨(κ.prod l).map m, Measure.isProbabilityMeasure_map hmm.aemeasurable, ?_, ?_, fun F f hF h => ?_⟩
  · refine (ae_map_iff hmm.aemeasurable ?_).2 (Eventually.of_forall fun p => ⟨p, rfl⟩)
    exact (isCompact_range hm).isClosed.measurableSet
  · rintro _ ⟨p, rfl⟩
    have h1 := (hκ p.1).prod (hl p.2)
    refine ⟨measurable_const_mul _, ?_⟩
    rw [Measure.map_map (measurable_const_mul _) hmm]
    conv_rhs => rw [← h1.map_eq, Measure.map_map hmm h1.measurable]
    congr 1
    funext q
    exact (m.map_mul p q).symm
  · rw [integral_map hmm.aemeasurable hF.aestronglyMeasurable]
    simp only [h]
    rw [integral_fun_fst]
    simp

end General

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem fin_mem {g : AdelicGLn.AdelicGL K n} (hg : g ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n))) :
    CuspidalSpectrum.finPart K n g ∈ AdelicGLn.integralFiniteGL K n :=
  (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 hg.2

private theorem inf_mem {g : AdelicGLn.AdelicGL K n} (hg : g ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n))) :
    infPart K n g ∈ AutomorphicForm.archCompact K n := by
  have h := mul_mem hg (inv_mem (finEmb_mem_maxCompact (fin_mem hg)))
  rw [← infEmb_infPart_mul_finEmb_finPart g] at h
  simp only [map_mul, finPart_infEmb, finPart_finEmb, one_mul, mul_inv_cancel_right] at h
  exact h

private theorem coe_arc (k : AutomorphicForm.archCompact K n) :
    (arc1 k : AdelicGLn.AdelicGL K n) = infEmb K n (k : archGroup K n) := by
  have h : detModule K n (infEmb K n (k : archGroup K n)) = 1 :=
    mem_normOneGL_iff_detModule.1 (maxCompact_le_normOneGL k.2)
  rw [arc1, ← retract_infEmb, coe_retractOne, h, map_one, inv_one, mul_one]

private theorem coe_fin {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    (fin1 u : AdelicGLn.AdelicGL K n) = finEmb K n u := by
  rw [fin1, MultiplicityOne.coe_finProj, detModule_finEmb hu, map_one, inv_one, mul_one]

private theorem arc_fin_comm (k : AutomorphicForm.archCompact K n) (u : FA K n) : fin1 u * arc1 k = arc1 k * fin1 u :=
  MultiplicityOne.finProj_mul_archProj_comm u _

private noncomputable def prM (U : Subgroup (FA K n)) : AutomorphicForm.archCompact K n × U →* G1 K n where
  toFun p := arc1 p.1 * fin1 (p.2 : FA K n)
  map_one' := by simp [arc1, fin1]
  map_mul' p q := by
    have h := arc_fin_comm q.1 (p.2 : FA K n)
    simp only [arc1, fin1, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul] at h ⊢
    rw [mul_assoc, mul_assoc, ← mul_assoc (MultiplicityOne.finProj K n p.2), h, mul_assoc]

private theorem prM_apply (U : Subgroup (FA K n)) (p : AutomorphicForm.archCompact K n × U) :
    prM U p = arc1 p.1 * fin1 (p.2 : FA K n) := rfl

private theorem cont_prM (U : Subgroup (FA K n)) : Continuous (prM U) :=
  (continuous_archP.comp (continuous_subtype_val.comp continuous_fst)).mul
    (MultiplicityOne.continuous_finProj.comp (continuous_subtype_val.comp continuous_snd))

private theorem inf_prM {U : Subgroup (FA K n)} (hU : U ≤ AdelicGLn.integralFiniteGL K n)
    (p : AutomorphicForm.archCompact K n × U) : infPart K n (prM U p : AdelicGLn.AdelicGL K n) = p.1 := by
  rw [prM_apply, Subgroup.coe_mul, coe_arc, coe_fin (hU p.2.2), map_mul, infPart_infEmb, infPart_finEmb, mul_one]

private theorem fin_prM {U : Subgroup (FA K n)} (hU : U ≤ AdelicGLn.integralFiniteGL K n)
    (p : AutomorphicForm.archCompact K n × U) :
    CuspidalSpectrum.finPart K n (prM U p : AdelicGLn.AdelicGL K n) = p.2 := by
  rw [prM_apply, Subgroup.coe_mul, coe_arc, coe_fin (hU p.2.2), map_mul, finPart_infEmb, finPart_finEmb, one_mul]

private theorem mem_range {U : Subgroup (FA K n)} (hU : U ≤ AdelicGLn.integralFiniteGL K n) (g : G1 K n) :
    g ∈ (prM U).range ↔ CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n) ∈ U ∧
      (g : AdelicGLn.AdelicGL K n) ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨by rw [fin_prM hU]; exact p.2.2, ?_⟩
    rw [prM_apply, Subgroup.coe_mul, coe_arc, coe_fin (hU p.2.2)]
    exact mul_mem p.1.2 (finEmb_mem_maxCompact (hU p.2.2))
  · rintro ⟨h1, h2⟩
    refine ⟨(⟨_, inf_mem h2⟩, ⟨_, h1⟩), Subtype.ext (ext_parts ?_ ?_)⟩
    · rw [inf_prM hU]
    · rw [fin_prM hU]

private theorem kbar_swap (κ : Measure (AutomorphicForm.archCompact K n)) [IsProbabilityMeasure κ]
    (c : AutomorphicForm.archCompact K n → ℂ) (hc : Continuous c) (F : AutomorphicForm.archCompact K n → archGroup K n)
    (hF : Continuous F) (β : TI K n) :
    ∫ k, c k * kbar β (F k) ∂κ = ∫ s, ∫ k, c k * β (F k * zInf K n s) ∂κ ∂posRealMeasure := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs : ∀ a : archGroup K 0, a = 1 := fun a => Subtype.ext (Units.ext (funext fun i => i.elim0))
    have h1 : ∀ a : archGroup K 0, β a = β 1 := fun a => by rw [hs a]
    simp only [kbar, h1]
    rw [integral_mul_const, integral_mul_const, integral_const_mul]
  · simp only [kbar, ← integral_const_mul]
    have hβ : Continuous β := β.continuous
    have hT : IsCompact ((fun p : {r : ℝ // 0 < r} × AutomorphicForm.archCompact K n => p.1 * (detA K n (F p.2))⁻¹) ''
        ((detA K n '' tsupport β) ×ˢ Set.univ)) :=
      ((β.hasCompactSupport.isCompact.image continuous_detA).prod isCompact_univ).image
        (continuous_fst.mul (continuous_detA.comp (hF.comp continuous_snd)).inv)
    refine swapC κ posRealMeasure (fun k s => c k * β (F k * zInf K n s)) ((hc.comp continuous_fst).mul
      (hβ.comp ((hF.comp continuous_fst).mul (continuous_zInf.comp continuous_snd)))) hT fun k s hne => ?_
    refine ⟨(s * detA K n (F k), k), ⟨mem_of_kernel_ne_zero hn (right_ne_zero_of_mul hne), trivial⟩, ?_⟩
    simp only [mul_inv_cancel_right]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.typeOf :
    TypeOf := by
  intro K _ _ n κ e he U hU hUo
  haveI := he.haar.prob
  haveI : CompactSpace U := isCompact_iff_compactSpace.1
    ((AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen hUo) hU)
  obtain ⟨l, hl1, hl⟩ := haarP U
  obtain ⟨ν, hν, hs, hinv, hint⟩ := pushT (prM U) (cont_prM U) κ he.haar.left l hl
  have hcl : IsClosed (AutomorphicForm.archCompact K n : Set (archGroup K n)) :=
    (isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (AutomorphicForm.archCompact K n)))).isClosed
  obtain ⟨E, hE⟩ := ContinuousMap.exists_restrict_eq hcl (⟨e, he.cont⟩ : C(AutomorphicForm.archCompact K n, ℂ))
  have hEe : ∀ k : AutomorphicForm.archCompact K n, E (k : archGroup K n) = e k := fun k => DFunLike.congr_fun hE k
  obtain ⟨ε, hε, hεd⟩ : ∃ ε : G1 K n → ℂ, Continuous ε ∧ ∀ g, ε g = E (infPart K n (g : AdelicGLn.AdelicGL K n)) :=
    ⟨_, E.continuous.comp (continuous_infPart.comp continuous_subtype_val), fun _ => rfl⟩
  have hεm : ∀ p, ε (prM U p) = e p.1 := fun p => by rw [hεd, inf_prM hU, hEe]
  have hfin : ∀ u : U, fin1 (u : FA K n) = prM U (1, u) := fun k => by simp [prM_apply, arc1]
  let D : TypeDat K n :=
    { U := (prM U).range
      isOpen := ⟨_, hUo.preimage CuspidalSpectrum.continuous_finPart, mem_range hU⟩
      ν := ν
      prob := hν
      supp := hs
      inv := hinv
      e := ε
      cont := hε
      star := by
        rintro _ ⟨p, rfl⟩
        rw [← map_inv, hεm, hεm]
        exact he.star p.1
      idem := by
        rintro _ ⟨p, rfl⟩
        rw [hεm, ← he.idem p.1]
        refine hint (fun h => ε h * ε (h⁻¹ * prM U p)) (fun h => e h * e (h⁻¹ * p.1))
          (hε.mul (hε.comp (continuous_inv.mul continuous_const))) fun q => ?_
        have h : (prM U q)⁻¹ * prM U p = prM U (q⁻¹ * p) := by rw [map_mul, map_inv]
        simp only [h, hεm]
        rfl }
  have hfix : ∀ f : G1 K n → ℂ, Continuous f → FixF U f → ∀ g,
      ∫ k, ε k * f (g * k) ∂ν = ∫ k, e k * f (g * arc1 k) ∂κ := fun f hf hF g =>
    hint _ _ (hε.mul (hf.comp (continuous_const.mul continuous_id))) fun q => by
      rw [hεm, prM_apply, ← mul_assoc, hF _ q.2.2]
  have hεl : ∀ (u : U), ∀ k ∈ (prM U).range, ε (prM U (1, u) * k) = ε k := by
    rintro u _ ⟨p, rfl⟩
    rw [← map_mul, hεm, hεm]
    simp
  refine ⟨D, ⟨⟨fun k hk => ?_, fun k hk hk' => ?_, ?_⟩, fun f hf => ⟨fun h => ?_, fun h g => ?_⟩, fun β φ hβ hφ g => ?_⟩,
    fun μ _ θ h1 h2 h3 => ?_⟩
  · refine (mem_range hU k).trans ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have h1 : infPart K n (k : AdelicGLn.AdelicGL K n) = 1 := by rw [infPart_apply, hk, map_one]
    rw [← infEmb_infPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n), h1, map_one, one_mul]
    exact finEmb_mem_maxCompact (hU h)
  · refine (mem_range hU k).2 ⟨?_, hk'⟩
    rw [finPart_apply, hk]
    exact U.one_mem
  · intro k _ hk u _
    have h1 : infPart K n (k : AdelicGLn.AdelicGL K n) = 1 := by rw [infPart_apply, hk, map_one]
    change ε (k * u) = ε u
    rw [hεd, hεd, Subgroup.coe_mul, (infPart K n).map_mul, h1, one_mul]
  · have hF : FixF U f := fun u hu g => by
      have hp := hinv _ ⟨(1, ⟨u, hu⟩), rfl⟩
      rw [← h g, ← h (g * fin1 u)]
      change ∫ k, ε k * f (g * fin1 u * k) ∂ν = ∫ k, ε k * f (g * k) ∂ν
      have hcf : Continuous fun k => ε k * f (g * k) := hε.mul (hf.comp (continuous_const.mul continuous_id))
      conv_rhs => rw [← hp.map_eq]
      rw [integral_map hp.measurable.aemeasurable hcf.aestronglyMeasurable]
      refine integral_congr_ae ?_
      filter_upwards [hs] with k hk
      show ε k * f (g * fin1 u * k) = ε (prM U (1, ⟨u, hu⟩) * k) * f (g * (prM U (1, ⟨u, hu⟩) * k))
      rw [hεl _ k hk, ← hfin ⟨u, hu⟩, mul_assoc]
    exact ⟨fun g => (hfix f hf hF g).symm.trans (h g), hF⟩
  · exact (hfix f hf h.2 g).trans (h.1 g)
  · have hcc : Continuous (tens β φ) := (tens β φ).continuous
    by_cases hc : Continuous (tensFun β φ) ∧ HasCompactSupport (tensFun β φ)
    swap
    · simp [tens, hc]
    have ht : ∀ x, tens β φ x = kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) *
        φ (CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n)) := fun x => by
      rw [tens, dif_pos hc]
      rfl
    have c1 : Continuous fun k : G1 K n => ε k * tens β φ (k⁻¹ * g) := hε.mul (hcc.comp (continuous_inv.mul continuous_const))
    have c2 : Continuous fun k : G1 K n => tens β φ (g * k⁻¹) * ε k := (hcc.comp (continuous_const.mul continuous_inv)).mul hε
    have h3 : ∀ (a : archGroup K n) s, ∫ k, e k * β ((k : archGroup K n)⁻¹ * a * zInf K n s) ∂κ = β (a * zInf K n s) := by
      intro a s
      simpa only [mul_assoc] using (hβ (a * zInf K n s)).1
    have h4 : ∀ (a : archGroup K n) s, ∫ k, e k * β (a * (k : archGroup K n)⁻¹ * zInf K n s) ∂κ = β (a * zInf K n s) := by
      intro a s
      conv_rhs => rw [← (hβ (a * zInf K n s)).2]
      refine integral_congr_ae (Eventually.of_forall fun k => ?_)
      show e k * β (a * (k : archGroup K n)⁻¹ * zInf K n s) = β (a * zInf K n s * (k : archGroup K n)⁻¹) * e k
      rw [mul_comm (e k), mul_assoc a, mul_assoc a, zInf_mul_comm]
    constructor
    · change ∫ k, ε k * tens β φ (k⁻¹ * g) ∂ν = _
      have e1 : ∫ k, ε k * tens β φ (k⁻¹ * g) ∂ν =
          ∫ k, e k * kbar β ((k : archGroup K n)⁻¹ * infPart K n (g : AdelicGLn.AdelicGL K n)) *
            φ (CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n)) ∂κ := by
        refine hint _ _ c1 fun p => ?_
        rw [hεm, ht]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inf_prM hU, fin_prM hU]
        rw [(hφ _ (U.inv_mem p.2.2) _).1]
        ring
      rw [e1, integral_mul_const, kbar_swap κ e he.cont (fun k => (k : archGroup K n)⁻¹ * infPart K n (g : AdelicGLn.AdelicGL K n))
        (continuous_subtype_val.inv.mul continuous_const), ht]
      simp only [h3]
      rfl
    · change ∫ k, tens β φ (g * k⁻¹) * ε k ∂ν = _
      have e1 : ∫ k, tens β φ (g * k⁻¹) * ε k ∂ν =
          ∫ k, e k * kbar β (infPart K n (g : AdelicGLn.AdelicGL K n) * (k : archGroup K n)⁻¹) *
            φ (CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n)) ∂κ := by
        refine hint _ _ c2 fun p => ?_
        rw [hεm, ht]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, inf_prM hU, fin_prM hU]
        rw [(hφ _ (U.inv_mem p.2.2) _).2]
        ring
      rw [e1, integral_mul_const, kbar_swap κ e he.cont (fun k => infPart K n (g : AdelicGLn.AdelicGL K n) * (k : archGroup K n)⁻¹)
        (continuous_const.mul continuous_subtype_val.inv), ht]
      simp only [h4]
      rfl
  · have key : ∀ p, ∃ q, θ.e (prM U p) = prM U q ∧ e q.1 = e p.1 := fun p => by
      obtain ⟨k', hk', hek⟩ := h1 p.1
      obtain ⟨u', hu', hu⟩ := h2 _ p.2.2
      exact ⟨(k', ⟨u', hu'⟩), by rw [prM_apply, map_mul, hk', hu, prM_apply], hek⟩
    have hin : ∀ k ∈ (prM U).range, θ.e k ∈ (prM U).range := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨q, hq, -⟩ := key p
      exact ⟨q, hq.symm⟩
    refine ⟨fun k => ⟨fun h => h3 k ▸ hin _ h, hin k⟩, ?_⟩
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq, hqe⟩ := key p
    change ε (θ.e (prM U p)) = ε (prM U p)
    rw [hq, hεm, hεm, hqe]
