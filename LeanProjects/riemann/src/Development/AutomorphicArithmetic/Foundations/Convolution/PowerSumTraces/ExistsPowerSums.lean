import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

section Abs

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [Module ℂ V]

private theorem mem_orbit_iff (I : Subgroup G) (x g : G) :
    (g : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ I) = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ I) = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

private theorem hk_sum (ρ : Representation ℂ G V) (I : Subgroup G) (x : G)
    (h : (MulAction.orbit I (x : G ⧸ I)).Finite) (v : UpperTheory.V.Hi.fixd ρ I) :
    (UpperTheory.V.AlgebraTools.hk ρ I x v : V) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply ℂ G V ρ I I x h).1 v, UpperTheory.V.Hi.dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem hasTrace_hk (m : Measure G) [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant]
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {I : Subgroup G} (hIo : IsOpen (I : Set G))
    (hIc : IsCompact (I : Set G)) (hm : m I = 1) (x : G) (hx : UpperTheory.V.AlgebraTools.FinOrb I I x)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} 1)
      (LinearMap.trace ℂ _ (UpperTheory.V.AlgebraTools.hk ρ I x)) := by
  classical
  have hx' : (MulAction.orbit I (x : G ⧸ I)).Finite := hx
  set D : Set G := {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} with hD
  let C : G ⧸ I → Set G := fun q => (fun g => q.out⁻¹ * g) ⁻¹' (I : Set G)
  have hC : ∀ q g, g ∈ C q ↔ (g : G ⧸ I) = q := fun q g => by
    show q.out⁻¹ * g ∈ I ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hIo.preimage (continuous_const.mul continuous_id)
  have hCc : ∀ q, IsCompact (C q) := fun q => (Homeomorph.mulLeft q.out⁻¹).isCompact_preimage.2 hIc
  have hCm : ∀ q, m (C q) = 1 := fun q => by rw [← hm]; exact measure_preimage_mul m _ _
  have hU : D = ⋃ q ∈ Set.Finite.toFinset hx', C q := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, hC, exists_prop, exists_eq_right']
    exact (mem_orbit_iff I x g).symm
  have hDc : IsCompact D := by
    rw [hU]
    exact (Set.Finite.toFinset hx').isCompact_biUnion fun q _ => hCc q
  have hDm : MeasurableSet D := by
    rw [hU]
    exact Finset.measurableSet_biUnion _ fun q _ => (hCo q).measurableSet
  have hI : ∀ a ∈ I, ∀ g ∈ D, a * g ∈ D := by
    rintro a ha _ ⟨b, hb, c, hc, rfl⟩
    exact ⟨_, mul_mem ha hb, c, hc, by simp only [mul_assoc]⟩
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp m hρ hDc hDm
  have e : ∀ φ : G → ℂ, (fun g => D.indicator (1 : G → ℂ) g * φ g) = D.indicator φ := fun φ => by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  have hfix : ∀ v, A v ∈ UpperTheory.V.Hi.fixd ρ I := fun v a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, hI a ha g h]
    · have : a * g ∉ D := fun h' => h (by simpa using hI _ (inv_mem ha) _ h')
      simp [h, this]
  have hres : ∀ w : UpperTheory.V.Hi.fixd ρ I, A w = UpperTheory.V.AlgebraTools.hk ρ I x w := fun w => by
    rw [hk_sum ρ I x hx', ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA w l).2, map_sum]
    have hsub : ∀ q ∈ Set.Finite.toFinset hx', C q ⊆ D := fun q hq => by
      rw [hU]
      exact Set.subset_biUnion_of_mem (u := C) hq
    conv_lhs => rw [hU]
    rw [integral_biUnion_finset _ (fun q _ => (hCo q).measurableSet)
      (fun p _ q _ hpq => Set.disjoint_left.2 fun g hp hq => hpq (((hC p g).1 hp).symm.trans ((hC q g).1 hq)))
      (fun q hq => (hA w l).1.mono_set (hsub q hq))]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hconst : ∀ g ∈ C q, l (ρ g w) = l (ρ q.out w) := fun g hg => by
      have h1 : q.out⁻¹ * g ∈ I := hg
      have h2 : g = q.out * (q.out⁻¹ * g) := by group
      rw [h2, map_mul, Module.End.mul_apply, w.2 _ h1]
    rw [setIntegral_congr_fun (hCo q).measurableSet hconst, setIntegral_const, measureReal_def, hCm]
    simp
  have hle : LinearMap.range A ≤ UpperTheory.V.Hi.fixd ρ I := by
    rintro _ ⟨v, rfl⟩
    exact hfix v
  refine ⟨A, fun v l => ?_, Submodule.finiteDimensional_of_le hle, ?_⟩
  · rw [e, integral_indicator hDm, integrable_indicator_iff hDm]
    exact hA v l
  haveI := Submodule.finiteDimensional_of_le hle
  let j := Submodule.inclusion hle
  let s : UpperTheory.V.Hi.fixd ρ I →ₗ[ℂ] LinearMap.range A := A.rangeRestrict ∘ₗ (UpperTheory.V.Hi.fixd ρ I).subtype
  have h1 : UpperTheory.V.AlgebraTools.hk ρ I x = j ∘ₗ s := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact (hres w).symm
  have h2 : A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
      (fun v _ => LinearMap.mem_range_self A v) = s ∘ₗ j := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rfl
  rw [h1, h2]
  exact (LinearMap.trace_comp_comm' s j).symm

end Abs

section Eig

private theorem exists_powerSums {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (hT : IsUnit T) :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ W ∧
      ∀ j : ℕ, LinearMap.trace ℂ W (T ^ j) = (Z.map (· ^ j)).sum := by
  obtain ⟨u, rfl⟩ := hT
  let R : Representation ℂ (Multiplicative ℤ) W := (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨E, -, hE⟩ := GlobalTheory.IwahoriTraceProof.exists_exponents (G := Multiplicative ℤ) _ W R rfl
  have hR : ∀ j : ℕ, R (Multiplicative.ofAdd 1 ^ j) = (u : Module.End ℂ W) ^ j := fun j => by
    rw [map_pow]
    congr 1
  refine ⟨E.map fun χ => ((χ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ), ?_, ?_, fun j => ?_⟩
  · intro h
    obtain ⟨χ, -, h⟩ := Multiset.mem_map.1 h
    exact (χ (Multiplicative.ofAdd 1)).ne_zero h
  · have h1 := hE 1
    rw [map_one, Module.End.one_eq_id, LinearMap.trace_id] at h1
    have h2 : (Module.finrank ℂ W : ℂ) = (E.card : ℂ) := by
      rw [h1]
      simp
    rw [Multiset.card_map]
    exact (Nat.cast_injective h2).symm
  · rw [← hR, hE, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun χ _ => ?_
    simp

end Eig

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem dom_pow (a : Fin n → ℤ) (ha : Antitone a) (h0 : (GLnLocal.uniformizer F : F) ≠ 0) :
    UpperTheory.V.AlgebraTools.Dom fun i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i := by
  intro i j hij
  have hp : 0 < ValuativeRel.valuation F (GLnLocal.uniformizer F : F) := GLnLocal.valuation_uniformizer_pos F
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ hp (GLnLocal.valuation_uniformizer_lt_one F)).2 (ha hij)

private theorem iw_local [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (m : Measure (GL (Fin n) F)) [m.IsHaarMeasure] {I : Subgroup (GL (Fin n) F)}
    (hI : UpperTheory.V.AlgebraTools.iwC F n ⊤ = I) (hm : m I = 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (hIo : IsOpen (I : Set (GL (Fin n) F)))
    (hIc : IsCompact (I : Set (GL (Fin n) F))) (ν : Fin n → ℤ) (hν : Antitone ν)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ (UpperTheory.V.Hi.fixd ρ I) ∧
      ∀ j : ℕ, HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * Cartan.diagPow F n (j • ν) * b} 1)
        (Z.map (· ^ j)).sum := by
  subst hI
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := GLnLocal.uniformizer_ne_zero F
  let t : (Fin n → ℤ) → Fin n → Fˣ := fun a i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i
  have hdiag : ∀ a, Cartan.diagPow F n a = diagT F (Fin n) (t a) := fun a => by
    ext i j
    rw [val_diagT]
    simp [t, Cartan.diagPow]
  have ht : ∀ a b, t (a + b) = t a * t b := fun a b => by
    funext i
    simp [t, _root_.zpow_add]
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul F n ⊤ ℂ V ρ
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard F : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.2 (GlobalTheory.SplitWeil.one_lt_resCard F).ne_bot).isUnit
  let T := UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t ν))
  have hdom : ∀ a, Antitone a → UpperTheory.V.AlgebraTools.Dom (t a) := fun a ha => dom_pow a ha h0
  have hTu : IsUnit T := hunit hq _ (hdom ν hν)
  have hone : UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t 0)) = 1 := by
    have hd0 := hdom 0 (fun _ _ _ => le_rfl)
    have h1 := hmul _ _ hd0 hd0
    rw [← ht, add_zero] at h1
    exact (hunit hq _ hd0).mul_left_cancel (h1.trans (mul_one _).symm)
  have hpow : ∀ j : ℕ, UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t (j • ν))) = T ^ j := by
    intro j
    induction j with
    | zero => simpa using hone
    | succ j ih =>
      have hj : Antitone (j • ν) := fun a b hab => by
        simpa using mul_le_mul_of_nonneg_left (hν hab) (Int.natCast_nonneg j)
      rw [pow_succ, ← ih, hmul _ _ (hdom _ hj) (hdom _ hν), ← ht, succ_nsmul]
  obtain ⟨Z, hZ0, hZc, hZ⟩ := exists_powerSums T hTu
  refine ⟨Z, hZ0, hZc, fun j => ?_⟩
  have h := hasTrace_hk m hρ hIo hIc hm (diagT F (Fin n) (t (j • ν))) ((UpperTheory.V.AlgebraTools.heckePairIwC F n ⊤).1 _)
  rw [hpow, hZ, ← hdiag] at h
  exact h

end Loc

theorem UpperTheory.ConvolutionTheory.C.iwPow :
    UpperTheory.ConvolutionTheory.C.IwPow := by
  intro K _ _ n w _ _ m _ hm σ ν hν hfd
  haveI : FiniteDimensional ℂ (UpperTheory.V.Hi.fixd σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin n))) := hfd
  exact iw_local m (UpperTheory.V.AlgebraTools.memIwC _ n ⊤).2.1 hm σ.ρ σ.smooth (GLnLocal.isOpen_iwahori _ _)
    (GLnLocal.isCompact_iwahori _ _) ν hν
