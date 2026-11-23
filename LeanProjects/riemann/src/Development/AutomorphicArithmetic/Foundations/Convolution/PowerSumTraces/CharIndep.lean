import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportHfun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDiv

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

noncomputable section

namespace UpperTheory.ConvolutionTheory.C.CharIndepProof

open GlobalTheory.OpTrace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem isLocallyConstant_of_right {U : Subgroup G} (hUo : IsOpen (U : Set G)) {f : G → ℂ}
    (hf : ∀ k ∈ U, ∀ x, f (x * k) = f x) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (U : Set G), hUo.preimage (continuous_mul_left _), by simp [U.one_mem],
    fun x hx => ?_⟩
  have := hf _ hx g
  simpa using this

private theorem isIntegralOp_smoothOp (m : Measure G) [IsFiniteMeasureOnCompacts m] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    IsIntegralOp m ρ f (smoothOp ρ m f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := m) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := m) hf hc l v]
    simp only [smul_eq_mul]

private theorem smoothOp_eq_levOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : GlobalTheory.BCT.IsHecke U f) {v : V} (hv : v ∈ fixed ρ U) :
    smoothOp ρ m f v = (m.real (U : Set G) : ℂ) • GlobalTheory.BCT.levOp ρ U U f LinearMap.id v := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  rw [GlobalTheory.TwTrLevel.levOp_apply ρ U U f LinearMap.id v hs, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_smul, LinearMap.id_apply]
  rw [finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (by
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by rw [h0, zero_smul]))]
  refine GlobalTheory.OpTrace.eq_of_forall_dual fun l => ?_
  rw [hρ.map_smoothOp hlc hf.1 l v,
    GlobalTheory.HaarSum.integral_eq_sum_cosets m U hUo hUc.measure_ne_top (fun g => f g • l (ρ g v)) ?_ hs.toFinset ?_,
    map_smul, map_sum]
  · simp
  · intro x s hs'
    rw [(hf.2 s hs' x).2, map_mul, Module.End.mul_apply, (mem_fixed.1 hv) s hs']
  · intro q hq
    have : f q.out = 0 := by simpa using hq
    simp [this]

private theorem finRankTrace_smoothOp (m : Measure G) [m.IsHaarMeasure] {U : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ)
    [FiniteDimensional ℂ (fixed ρ U)] {f : G → ℂ} (hf : GlobalTheory.BCT.IsHecke U f) :
    finRankTrace (smoothOp ρ m f) = (m.real (U : Set G) : ℂ) * GlobalTheory.BCT.twTr ρ U U f LinearMap.id := by
  have hlc := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
  have hW : ∀ x, smoothOp ρ m f x ∈ fixed ρ U :=
    hρ.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
  have hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ U U f LinearMap.id v ∈ fixed ρ U := fun v hv =>
    GlobalTheory.TwTrLevel.levOp_mem_fixed ρ (MonoidHom.id G) (fun _ => rfl) LinearMap.id (fun _ => rfl) U U hUo
      (fun _ h => h) f hf v hv
  rw [finRankTrace_eq _ (fixed ρ U) hW, GlobalTheory.BCT.twTr, dif_pos hmem, ← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun v => Subtype.ext ?_
  simpa using smoothOp_eq_levOp m hUo hUc hρ hf v.2

end UpperTheory.ConvolutionTheory.C.CharIndepProof

open UpperTheory.ConvolutionTheory.C.CharIndepProof GlobalTheory.OpTrace in
theorem UpperTheory.ConvolutionTheory.C.charIndep :
    UpperTheory.ConvolutionTheory.C.CharIndep := by
  classical
  intro G _ _ _ _ _ _ _ _ m _ _ U hU ι _ σ c hfd hc i₀ hi₀
  obtain ⟨hUc, hUo⟩ := hU
  have hfx : ∀ i, fixed (σ i).ρ U = fixedVectors (σ i).ρ U := fun i =>
    Submodule.ext fun v => GlobalTheory.OpTrace.mem_fixed
  haveI hfd' : ∀ i, FiniteDimensional ℂ (fixed (σ i).ρ U) := fun i => by rw [hfx i]; exact hfd i
  let S : Setoid ι := ⟨fun i j => Nonempty ((σ i).ρ.Equiv (σ j).ρ),
    ⟨fun i => ⟨Representation.Equiv.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩
  let mk : ι → Quotient S := Quotient.mk S
  let r : Quotient S → ι := Quotient.out
  haveI : Fintype (Quotient S) := Fintype.ofFinite _
  have hmkr : ∀ q, mk (r q) = q := fun q => Quotient.out_eq q
  have hr : ∀ i, Nonempty ((σ i).ρ.Equiv (σ (r (mk i))).ρ) := fun i =>
    (Quotient.exact (hmkr (mk i))).elim fun e => ⟨e.symm⟩
  let c' : Quotient S → ℂ := fun q => ∑ i with mk i = q, c i
  have hvol : (m.real (U : Set G) : ℂ) ≠ 0 := by
    have h1 : m (U : Set G) ≠ 0 := (hUo.measure_pos m ⟨1, U.one_mem⟩).ne'
    have h2 : m.real (U : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hUc.measure_ne_top⟩
    exact_mod_cast h2
  have key : ∀ f, GlobalTheory.BCT.IsHecke U f →
      ∑ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥},
        c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id = 0 := by
    intro f hf
    have hlc : IsLocallyConstant f := isLocallyConstant_of_right hUo (fun k hk x => (hf.2 k hk x).2)
    have hW : ∀ i x, smoothOp (σ i).ρ m f x ∈ fixed (σ i).ρ U := fun i =>
      (σ i).smooth.smoothOp_mem_fixed hlc hf.1 (fun k hk g => (hf.2 k hk g).1)
    have hfr : ∀ i, FiniteDimensional ℂ (LinearMap.range (smoothOp (σ i).ρ m f)) := fun i =>
      Submodule.finiteDimensional_of_le (S₂ := fixed (σ i).ρ U) (by rintro _ ⟨x, rfl⟩; exact hW i x)
    let s : ι → ℂ := fun i => finRankTrace (smoothOp (σ i).ρ m f)
    have h0 := hc f s ⟨hlc, hf.1⟩ (fun u hu g => hf.2 u hu g) (fun i =>
      ⟨_, isIntegralOp_smoothOp m (σ i).smooth hlc hf.1, hfr i, rfl⟩)
    have hconst : ∀ i, s i = s (r (mk i)) := fun i => by
      obtain ⟨e⟩ := hr i
      haveI := hfr i
      exact ((finRankTrace_eq_of_equiv e.toLinearEquiv (T := smoothOp (σ i).ρ m f)
        (T' := smoothOp (σ (r (mk i))).ρ m f)
        ((σ i).smooth.map_smoothOp_of_intertwining (σ (r (mk i))).smooth hlc hf.1 e.toLinearEquiv.toLinearMap
          (fun g v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v))).2).symm
    have hzero : ∀ q, ¬ fixed (σ (r q)).ρ U ≠ ⊥ → s (r q) = 0 := fun q hq => by
      have hb : fixed (σ (r q)).ρ U = ⊥ := not_not.1 hq
      have hW' : ∀ x, smoothOp (σ (r q)).ρ m f x ∈ (⊥ : Submodule ℂ (σ (r q)).V) := fun x => hb ▸ hW (r q) x
      show finRankTrace _ = 0
      rw [finRankTrace_eq _ ⊥ hW', Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
    have h1 : ∑ q, c' q * s (r q) = 0 := by
      rw [← h0, ← Finset.sum_fiberwise (s := Finset.univ) (g := mk)]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hconst i, (Finset.mem_filter.1 hi).2]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun q => fixed (σ (r q)).ρ U ≠ ⊥),
      Finset.sum_eq_zero (s := Finset.univ) (f := fun q : {q // ¬ fixed (σ (r q)).ρ U ≠ ⊥} => c' q * s (r q))
        (fun q _ => by rw [hzero q q.2, mul_zero]), add_zero] at h1
    have h2 : ∀ q : {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥}, c' q * s (r q) =
        (m.real (U : Set G) : ℂ) * (c' q * GlobalTheory.BCT.twTr (σ (r q)).ρ U U f LinearMap.id) := fun q => by
      show c' q * finRankTrace _ = _
      rw [finRankTrace_smoothOp m hUo hUc (σ (r q)).smooth hf]
      ring
    simp only [h2, ← Finset.mul_sum] at h1
    exact (mul_eq_zero.1 h1).resolve_left hvol
  have hli := GlobalTheory.HeckeTraceIndep.twTr_linearIndependent G U hUo hUc U ⟨hUo, le_rfl, fun _ h => h⟩
    {q : Quotient S // fixed (σ (r q)).ρ U ≠ ⊥} (fun q => σ (r q)) (fun q => ⟨hfd' _, q.2⟩)
    (fun q q' h => Subtype.ext (by rw [← hmkr q, ← hmkr q']; exact Quotient.sound h))
    (fun q => c' q) key
  have hq : fixed (σ (r (mk i₀))).ρ U ≠ ⊥ := by
    obtain ⟨e⟩ := hr i₀
    rw [← hfx i₀] at hi₀
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hi₀
    refine (Submodule.ne_bot_iff _).2 ⟨e.toLinearEquiv v, mem_fixed.2 fun k hk => ?_, ?_⟩
    · have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap k v
      rw [mem_fixed.1 hv k hk] at this
      exact this.symm
    · simpa using hv0
  have hfin := hli ⟨mk i₀, hq⟩
  have hset : {i | Nonempty ((σ i).ρ.Equiv (σ i₀).ρ)} =
      ↑(Finset.univ.filter fun i => mk i = mk i₀) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩
  rw [hset, finsum_mem_coe_finset]
  exact hfin
