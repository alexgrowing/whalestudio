import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSummands
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandsSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

private theorem summand_map {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G ≃* G)
    (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ g v, U (π g v) = π (e g) (U v)) (hW : W.map (U : H →ₗ[ℂ] H) = W)
    {V : Submodule ℂ H} (hV : IsSummandOf π W V) : IsSummandOf π W (V.map (U : H →ₗ[ℂ] H)) where
  le := by
    rintro _ ⟨v, hv, rfl⟩
    rw [← hW]
    exact ⟨v, hV.le hv, rfl⟩
  closed := by
    rw [Submodule.map_coe]
    exact U.toHomeomorph.isClosedMap _ hV.closed
  inv := by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨π (e.symm g) v, hV.inv _ _ hv, ?_⟩
    have := hU (e.symm g) v
    simpa using this
  ne_bot := by
    intro h
    refine hV.ne_bot ((Submodule.eq_bot_iff _).2 fun v hv => ?_)
    have h1 : U v ∈ V.map (U : H →ₗ[ℂ] H) := ⟨v, hv, rfl⟩
    rw [h] at h1
    simpa using h1
  irred := by
    intro V' hle hcl hinv
    have hle' : V'.comap (U : H →ₗ[ℂ] H) ≤ V := by
      intro v hv
      obtain ⟨w, hw, hwv⟩ := hle hv
      have : w = v := U.injective hwv
      exact this ▸ hw
    have hcl' : IsClosed (V'.comap (U : H →ₗ[ℂ] H) : Set H) := hcl.preimage U.continuous
    have hinv' : π.IsInvariant (V'.comap (U : H →ₗ[ℂ] H)) := by
      intro g v hv
      change U (π g v) ∈ V'
      rw [hU]
      exact hinv _ _ hv
    rcases hV.irred _ hle' hcl' hinv' with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
      have h1 : U.symm y ∈ V'.comap (U : H →ₗ[ℂ] H) := by
        change U (U.symm y) ∈ V'
        simpa using hy
      rw [h] at h1
      simpa using h1
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [← h] at hv
      exact hv

private theorem preserves_closure {H ι : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (V : ι → Submodule ℂ H) (W : Submodule ℂ H) (hc : IsClosed (W : Set H))
    (hspan : (⨆ i, V i).topologicalClosure = W) (B : H →L[ℂ] H) (hB : ∀ i, ∀ v ∈ V i, B v ∈ V i)
    (hle : ∀ i, V i ≤ W) : ∀ v ∈ W, B v ∈ W := by
  have hcl : IsClosed ((W.comap (B : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := hc.preimage B.continuous
  have h1 : (⨆ i, V i) ≤ W.comap (B : H →ₗ[ℂ] H) := iSup_le fun i v hv => hle i (hB i v hv)
  have h2 := Submodule.topologicalClosure_minimal _ h1 hcl
  rw [hspan] at h2
  exact fun v hv => h2 hv

private theorem trOn_eig_zero {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G ≃* G)
    (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ g v, U (π g v) = π (e g) (U v)) (hW : W.map (U : H →ₗ[ℂ] H) = W)
    (hmult : ∀ V V', IsSummandOf π W V → IsSummandOf π W V' → V ≠ V' → V ⟂ V')
    (T : H →L[ℂ] H) (hT : ∀ V, IsSummandOf π W V → ∀ v ∈ V, T v ∈ V) (A : H →L[ℂ] H) (x : ℝ)
    {V : Submodule ℂ H} (hV : IsSummandOf π W V) (hne : V.map (U : H →ₗ[ℂ] H) ≠ V) :
    trOn (eigIn V A x) (T ∘L (U : H →L[ℂ] H)) = 0 := by
  have hm := summand_map π W e U hU hW hV
  have ho : V.map (U : H →ₗ[ℂ] H) ⟂ V := hmult _ _ hm hV hne
  have hEV : eigIn V A x ≤ V := inf_le_left
  have hcE : (eigIn V A x).topologicalClosure ≤ V :=
    Submodule.topologicalClosure_minimal _ hEV hV.closed
  have h0 : prj (eigIn V A x) ∘L (T ∘L (U : H →L[ℂ] H)) ∘L prj (eigIn V A x) = 0 := by
    ext y
    have hy : prj (eigIn V A x) y ∈ V := hcE (Submodule.starProjection_apply_mem _ _)
    have hz : T (U (prj (eigIn V A x) y)) ∈ V.map (U : H →ₗ[ℂ] H) := hT _ hm _ ⟨_, hy, rfl⟩
    have hz' : T (U (prj (eigIn V A x) y)) ∈ (eigIn V A x).topologicalClosureᗮ := by
      rw [Submodule.orthogonal_closure]
      exact Submodule.orthogonal_le hEV (ho hz)
    exact (Submodule.starProjection_apply_eq_zero_iff _).2 hz'
  unfold trOn
  rw [h0]
  simp [trace]

private theorem band_core {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (W : Submodule ℂ H) (e : G ≃* G)
    (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ g v, U (π g v) = π (e g) (U v)) (hW : W.map (U : H →ₗ[ℂ] H) = W)
    (hspan : (⨆ V : {V // IsSummandOf π W V}, V.1).topologicalClosure = W)
    (hmult : ∀ V V', IsSummandOf π W V → IsSummandOf π W V' → V ≠ V' → V ⟂ V')
    (A : H →L[ℂ] H) (hA0 : 0 ≤ A) (hAV : ∀ V, IsSummandOf π W V → ∀ v ∈ V, A v ∈ V)
    (hAc : IsCompactOperator (A ∘L prj W)) (η : ℝ) (hη : 0 < η) :
    ∃ S : Finset (ℝ × Submodule ℂ H),
      (∀ p, p ∈ S ↔ η < p.1 ∧ IsSummandOf π W p.2 ∧ p.2.map (U : H →ₗ[ℂ] H) = p.2 ∧
        eigIn p.2 A p.1 ≠ ⊥) ∧
      (∀ p ∈ S, FiniteDimensional ℂ (eigIn p.2 A p.1)) ∧
      ∀ (φ : ℝ → ℝ) (c : ℝ) (T : H →L[ℂ] H), Continuous φ → 0 ≤ c →
        (∀ x ∈ Set.Icc 0 η, |φ x| ≤ c) →
        (∀ V, IsSummandOf π W V → ∀ v ∈ V, T v ∈ V) → IsTraceClass (prj W ∘L T ∘L prj W) →
        ‖trace (prj W ∘L cfc φ A ∘L T ∘L (U : H →L[ℂ] H) ∘L prj W) -
            ∑ p ∈ S, (φ p.1 : ℂ) * trOn (eigIn p.2 A p.1) (T ∘L (U : H →L[ℂ] H))‖ ≤
          c * (traceNorm (prj W ∘L T ∘L prj W)).toReal := by
  classical
  have hc : IsClosed (W : Set H) := by
    rw [← hspan]
    exact Submodule.isClosed_topologicalClosure _
  have hWcl : W.topologicalClosure = W := hc.submodule_topologicalClosure_eq
  have hPmem : ∀ y, prj W y ∈ W := fun y => by
    have : prj W y ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ _
    rwa [hWcl] at this
  have hPself : ∀ y ∈ W, prj W y = y := fun y hy =>
    Submodule.starProjection_eq_self_iff.2 (by rw [hWcl]; exact hy)
  have hUW : ∀ v ∈ W, U v ∈ W := fun w hw => by
    rw [← hW]
    exact ⟨w, hw, rfl⟩
  have hle : ∀ i : {V // IsSummandOf π W V}, i.1 ≤ W := fun i => i.2.le
  have hpres : ∀ B : H →L[ℂ] H, (∀ V, IsSummandOf π W V → ∀ v ∈ V, B v ∈ V) → ∀ v ∈ W, B v ∈ W :=
    fun B hB => preserves_closure (fun i : {V // IsSummandOf π W V} => i.1) W hc hspan B
      (fun i => hB i.1 i.2) hle
  have hAW := hpres A hAV
  obtain ⟨S0, hS1, hS2, hS3⟩ := UpperTheory.ConvolutionTheory.C.eigSplit H W A hc hA0 hAW hAc η hη
  have hsa : IsSelfAdjoint A := hA0.isSelfAdjoint
  have hex : ∀ x ∈ S0, ∃ s : Finset {V // IsSummandOf π W V},
      (∀ i, i ∈ s ↔ eigIn i.1 A x ≠ ⊥) ∧ ∀ B : H →L[ℂ] H,
        trOn (eigIn W A x) B = ∑ i ∈ s, trOn (eigIn i.1 A x) B := by
    intro x hx
    obtain ⟨s, h1, -, h3⟩ := UpperTheory.ConvolutionTheory.C.eigSummands H {V // IsSummandOf π W V} (fun i => i.1) W A x
      (fun i => i.2.closed)
      (fun a b hab => hmult a.1 b.1 a.2 b.2 fun h => hab (Subtype.ext h)) hspan hsa
      (fun i => hAV i.1 i.2) (hS2 x hx)
    exact ⟨s, h1, h3⟩
  choose! s hs1 hs2 using hex
  have hEle : ∀ {V : Submodule ℂ H} (x : ℝ), V ≤ W → eigIn V A x ≤ eigIn W A x :=
    fun {V} x h => inf_le_inf_right _ h
  let f : ℝ → Finset (ℝ × Submodule ℂ H) := fun x =>
    ((s x).filter fun i => i.1.map (U : H →ₗ[ℂ] H) = i.1).image fun i => (x, i.1)
  have hmemS : ∀ p, p ∈ S0.biUnion f ↔ η < p.1 ∧ IsSummandOf π W p.2 ∧
      p.2.map (U : H →ₗ[ℂ] H) = p.2 ∧ eigIn p.2 A p.1 ≠ ⊥ := by
    rintro ⟨x, V⟩
    simp only [Finset.mem_biUnion, f, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, i, ⟨hi, hst⟩, rfl, rfl⟩
      exact ⟨((hS1 y).1 hy).1, i.2, hst, (hs1 y hy i).1 hi⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have hx : x ∈ S0 := (hS1 x).2 ⟨h1, fun hb => h4 (le_bot_iff.1 (hb ▸ hEle x h2.le))⟩
      exact ⟨x, hx, ⟨V, h2⟩, ⟨(hs1 x hx ⟨V, h2⟩).2 h4, h3⟩, rfl, rfl⟩
  refine ⟨S0.biUnion f, hmemS, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2, -, h4⟩ := (hmemS p).1 hp
    have hx : p.1 ∈ S0 := (hS1 _).2 ⟨h1, fun hb => h4 (le_bot_iff.1 (hb ▸ hEle _ h2.le))⟩
    haveI := hS2 _ hx
    exact Submodule.finiteDimensional_of_le (hEle p.1 h2.le)
  · intro φ c T hφ hc0 hb hT htr
    have hTW := hpres T hT
    have hcomp : prj W ∘L (T ∘L (U : H →L[ℂ] H)) ∘L prj W =
        (prj W ∘L T ∘L prj W) ∘L ((U : H →L[ℂ] H) ∘L prj W) := by
      ext y
      change prj W (T (U (prj W y))) = prj W (T (prj W (U (prj W y))))
      rw [hPself _ (hUW _ (hPmem y))]
    have hUP : ‖(U : H →L[ℂ] H) ∘L prj W‖ₑ ≤ 1 := by
      refine enorm_le_one_of_norm_le_one (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_)
      change ‖U (prj W y)‖ ≤ 1 * ‖y‖
      rw [U.norm_map, one_mul]
      exact Submodule.norm_starProjection_apply_le _ _
    have hnorm : traceNorm (prj W ∘L (T ∘L (U : H →L[ℂ] H)) ∘L prj W) ≤
        traceNorm (prj W ∘L T ∘L prj W) := by
      rw [hcomp]
      refine (traceNorm_comp_right_le _ _).trans ?_
      calc _ ≤ 1 * traceNorm (prj W ∘L T ∘L prj W) := by gcongr
        _ = _ := one_mul _
    have htc : IsTraceClass (prj W ∘L (T ∘L (U : H →L[ℂ] H)) ∘L prj W) := hnorm.trans_lt htr
    have hmain := hS3 φ c (T ∘L (U : H →L[ℂ] H)) hφ hc0 hb htc
    have hfirst : trOn W (cfc φ A ∘L prj W ∘L (T ∘L (U : H →L[ℂ] H))) =
        trace (prj W ∘L cfc φ A ∘L T ∘L (U : H →L[ℂ] H) ∘L prj W) := by
      unfold trOn
      congr 1
      ext y
      change prj W (cfc φ A (prj W (T (U (prj W y))))) = prj W (cfc φ A (T (U (prj W y))))
      rw [hPself _ (hTW _ (hUW _ (hPmem y)))]
    have hsum : ∑ p ∈ S0.biUnion f, (φ p.1 : ℂ) * trOn (eigIn p.2 A p.1) (T ∘L (U : H →L[ℂ] H)) =
        ∑ x ∈ S0, (φ x : ℂ) * trOn (eigIn W A x) (T ∘L (U : H →L[ℂ] H)) := by
      rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.sum_image, hs2 x hx, Finset.mul_sum, Finset.sum_filter]
        · refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs with hst
          · rfl
          · rw [trOn_eig_zero π W e U hU hW hmult T hT A x i.2 hst, mul_zero]
        · intro a _ b _ hab
          exact Subtype.ext (congrArg Prod.snd hab)
      · intro x _ y _ hxy
        refine Finset.disjoint_left.2 fun p hp hq => hxy ?_
        simp only [f, Finset.mem_image] at hp hq
        obtain ⟨i, -, rfl⟩ := hp
        obtain ⟨j, -, hj⟩ := hq
        exact (congrArg Prod.fst hj).symm
    rw [hsum, ← hfirst]
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono htr.ne hnorm) hc0

private theorem prj_eq_star {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (W : Submodule ℂ H) [W.HasOrthogonalProjection] (hc : IsClosed (W : Set H)) :
    prj W = W.starProjection := by
  have key : ∀ (K K' : Submodule ℂ H) [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection],
      K = K' → K.starProjection = K'.starProjection := by
    intro K K' _ _ h
    subst h
    rfl
  exact key _ _ hc.submodule_topologicalClosure_eq

theorem UpperTheory.ConvolutionTheory.C.cuspTrBand :
    UpperTheory.ConvolutionTheory.C.CuspTrBand := by
  intro K _ _ n μ _ θ hm A hA0 hAV hAc η hη
  obtain ⟨U, hU1, hU2, hU3⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary K n μ θ
  have hspan := UpperTheory.ConvolutionTheory.C.summandsSpan K n μ
  have hc : IsClosed (cuspidalL2 μ : Set (L2 μ)) := by
    rw [← hspan]
    exact Submodule.isClosed_topologicalClosure _
  have hP : Pc μ = prj (cuspidalL2 μ) := (prj_eq_star _ hc).symm
  rw [hP] at hAc ⊢
  have := band_core (rightRegularRep (Gam K n) μ) (cuspidalL2 μ) θ.e.toMulEquiv U
    (fun g v => hU2 g v) hU3 hspan (fun V V' h h' hne => hm V V' h h' hne) A hA0 hAV hAc η hη
  rw [← hU1]
  exact this
