import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CosAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem fix_of_avg {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (ν : Measure G)
    (e : G → ℂ) (u : G) (hu : MeasurePreserving (u * ·) ν ν) (he : ∀ᵐ k ∂ν, e (u * k) = e k) (w : H)
    (hw : ∫ k, e k • π k w ∂ν = w) : π u w = w := by
  by_cases hi : Integrable (fun k => e k • π k w) ν
  · have h1 := (π u).integral_comp_comm hi
    have h2 := hu.integral_comp (Homeomorph.mulLeft u).measurableEmbedding (fun k => e k • π k w)
    rw [hw] at h1 h2
    rw [← h1]
    refine Eq.trans (integral_congr_ae ?_) h2
    filter_upwards [he] with k hk
    rw [map_smul, hk, π.map_mul_apply]
  · rw [integral_undef hi] at hw
    rw [← hw, map_zero]

private theorem coset_bij {G L : Type*} [Group G] [Group L] (loc : L →* G) (p : G →* L) (h1 : ∀ x, p (loc x) = x)
    (hc : ∀ h, p h = 1 → ∀ x, loc x * h = h * loc x) (J : Subgroup L) (x : L) (U : Subgroup G)
    (hJU : ∀ j ∈ J, loc j ∈ U) (hUJ : ∀ u ∈ U, p u ∈ J) :
    Set.BijOn (fun c : L ⧸ J => (QuotientGroup.mk (loc c.out) : G ⧸ U)) {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
      {c | ∃ k ∈ U, c = QuotientGroup.mk (k * loc x)} := by
  have key : ∀ y : L, (QuotientGroup.mk (loc (QuotientGroup.mk y : L ⧸ J).out) : G ⧸ U) = QuotientGroup.mk (loc y) := by
    intro y
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J y
    rw [hj, map_mul, QuotientGroup.mk_mul_of_mem _ (hJU _ j.2)]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨loc k, hJU k hk, by simp only [key, map_mul]⟩
  · intro a _ b _ hab
    have h := hUJ _ (QuotientGroup.eq.1 hab)
    rw [map_mul, map_inv, h1, h1] at h
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 h
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨QuotientGroup.mk (p k * x), ⟨p k, hUJ k hk, rfl⟩, ?_⟩
    have hp : p (k * (loc (p k))⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have e1 : k * loc x = loc (p k * x) * (k * (loc (p k))⁻¹) := by
      rw [hc _ hp, map_mul]
      group
    simp only [key]
    rw [e1, QuotientGroup.mk_mul_of_mem _ (U.mul_mem hk (U.inv_mem (hJU _ (hUJ k hk))))]

private theorem hop_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : Gw n w) (U : Subgroup (FA K n)) (hJ : CO J)
    (hJU : ∀ j ∈ J, AdelicGLn.localEmbedding w j ∈ U) (hUJ : ∀ u ∈ U, finAt w (finEmb K n u) ∈ J) :
    (∑ᶠ c ∈ {c : FA K n ⧸ U | ∃ k ∈ U, c = QuotientGroup.mk (k * AdelicGLn.localEmbedding w x)}, rhoF μ c.out) ∘L
      prj (fixF μ U) = Hop μ w J x ∘L prj (fixF μ U) := by
  obtain ⟨hfin, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJ.2 hJ.1
  obtain ⟨-, hmemU, hPU, -, habs, hmul, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemJ, -, hPJ, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  obtain ⟨-, hl1, -, -, hl5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have hb := coset_bij (AdelicGLn.localEmbedding w)
    (MonoidHom.mk' (fun g : FA K n => finAt w (finEmb K n g)) fun a b => by rw [map_mul, finAt_mul]) hl1 hl5 J x U hJU hUJ
  have hfin' := hb.image_eq ▸ hfin.image _
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : prj (fixL μ w J) (prj (fixF μ U) v) = prj (fixF μ U) v := by
    refine hPJ _ ((hmemJ _).2 ?_)
    rintro _ ⟨j, hj, rfl⟩
    exact (hmemU _).1 (hPU v) _ (hJU j hj)
  rw [Hop, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv]
  let ev : (LL μ →L[ℂ] LL μ) →+ LL μ := AddMonoidHom.mk' (fun T => T (prj (fixF μ U) v)) fun _ _ => rfl
  refine (ev.map_finsum_mem _ hfin').trans (Eq.trans ?_ (ev.map_finsum_mem _ hfin).symm)
  refine (finsum_mem_eq_of_bijOn _ hb fun c _ => ?_).symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (AdelicGLn.localEmbedding w c.out)
  change rhoF μ _ (prj (fixF μ U) v) = rhoF μ _ (prj (fixF μ U) v)
  rw [hu, hmul, ContinuousLinearMap.comp_apply, (hmemU _).1 (hPU v) u u.2]

private theorem level_facts {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (D : TypeDat K n) (U : Subgroup (FA K n)) (hD : D.Level U) (hle : U ≤ AdelicGLn.integralFiniteGL K n) :
    IsOpen (U : Set (FA K n)) ∧ IsCompact (U : Set (FA K n)) ∧ ∀ v, D.FixedByTypeProjector μ v → v ∈ fixF μ U := by
  have hpe : ∀ u ∈ AdelicGLn.integralFiniteGL K n, ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u := by
    intro u hu
    exact congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))
  have hiff : ∀ u ∈ AdelicGLn.integralFiniteGL K n, fin1 u ∈ D.U ↔ u ∈ U := by
    intro u hu
    have h := hD.1 (fin1 u) (by rw [hpe u hu, prodEquiv_finEmb])
    rwa [hpe u hu, prodEquiv_finEmb] at h
  have ho : IsOpen (U : Set (FA K n)) := by
    obtain ⟨O, hO, hUO⟩ := D.isOpen
    have : (U : Set (FA K n)) = (AdelicGLn.integralFiniteGL K n : Set (FA K n)) ∩ finEmb K n ⁻¹' O := by
      ext u
      constructor
      · intro hu
        have h := ((hUO _).1 ((hiff u (hle hu)).2 hu)).1
        rw [hpe u (hle hu)] at h
        exact ⟨hle hu, h⟩
      · rintro ⟨hu, h⟩
        refine (hiff u hu).1 ((hUO _).2 ?_)
        rw [hpe u hu]
        exact ⟨h, finEmb_mem_maxCompact hu⟩
    rw [this]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter (hO.preimage continuous_finEmb)
  refine ⟨ho, (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (U.isClosed_of_isOpen ho) hle, fun v hv => ?_⟩
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U).2.1 v).2 fun u hu => ?_
  have hu' := (hiff u (hle hu)).2 hu
  refine fix_of_avg _ D.ν D.e (fin1 u) (D.inv _ hu') ?_ v hv
  filter_upwards [D.supp] with k hk
  exact hD.2.2 _ hu' (by rw [hpe u (hle hu), prodEquiv_finEmb]) k hk

private theorem comm_proj {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P T : H →L[ℂ] H) (F : Submodule ℂ H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (hJ : ∀ u, J u ∈ F) (hJ' : ∀ u, J' u ∈ F) (hT : Commute T (prj F))
    (hY : (T ∘L prj F) ∘L P = P ∘L (T ∘L prj F)) : T ∘L P = P ∘L T := by
  have h0 : ∀ a ∈ F, ∀ h, inner ℂ a (h - prj F h) = 0 := fun a ha h =>
    inner_eq_zero_symm.1 (Submodule.starProjection_inner_eq_zero h a (F.le_topologicalClosure ha))
  have h1 : P * prj F = P := by
    refine ContinuousLinearMap.ext fun h => ?_
    have := (hP.2.2 (h - prj F h)).2 ⟨fun u => h0 _ (hJ u) h, fun u => h0 _ (hJ' u) h⟩
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  have hQ : IsSelfAdjoint (prj F) := isSelfAdjoint_starProjection _
  have h2 : prj F * P = P := by
    have := congrArg star h1
    rwa [star_mul, hQ.star_eq, hP.1.star_eq] at this
  change (T * prj F) * P = P * (T * prj F) at hY
  change T * P = P * T
  rw [mul_assoc, h2, hT.eq, ← mul_assoc, h1] at hY
  exact hY

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.uiwAct :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), D.Level (levOn S U) →
          ∀ (d d' : ℕ) (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d'), ∀ w ∈ S, U w = GLnLocal.iwahori (w.adicCompletion K) (2 + 2) → ∀ ν : Fin (2 + 2) → ℤ,
          (∃ s, Act A.J (Uiw μ w ν) s ∧
            HeckeAt A (levOn S U) (AdelicGLn.localEmbedding w (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν)) (s 0 : Eu d →ₗ[ℂ] Eu d)) ∧
          ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P → Uiw μ w ν ∘L P = P ∘L Uiw μ w ν := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp S U hU D hD d d' A A' w hw hI ν
  have hmem : ∀ u, u ∈ levOn S U ↔ ∀ v, finAt v (finEmb K (2 + 2) u) ∈
      (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion K) (2 + 2)) := fun u => Iff.rfl
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL K (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall K (2 + 2)).2 fun v => ?_
    have h := (hmem u).1 hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  obtain ⟨-, hl1, hl2, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K (2 + 2) w
  have hJU : ∀ j ∈ U w, AdelicGLn.localEmbedding w j ∈ levOn S U := by
    intro j hj
    refine (hmem _).2 fun v => ?_
    by_cases hv : v = w
    · subst hv
      rw [hl1, if_pos hw]
      exact hj
    · rw [hl2 v hv]
      exact one_mem _
  have hUJ : ∀ u ∈ levOn S U, finAt w (finEmb K (2 + 2) u) ∈ U w := by
    intro u hu
    have h := (hmem u).1 hu w
    rwa [if_pos hw] at h
  obtain ⟨ho, hc, hfix⟩ := level_facts μ D _ hD hle
  have hT : Uiw μ w ν = Hop μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) := by rw [hI]; rfl
  obtain ⟨⟨s, ⟨u, κ, hκ, hact, hs⟩, hsec⟩, hcomm⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' _ hD hle _ _
    (hop_prj μ w (U w) (Cartan.diagPow (w.adicCompletion K) (2 + 2) ν) _ (hU w).1 hJU hUJ).symm
  have hA : ∀ x, A.J x ∈ fixF μ (levOn S U) := fun x => hfix _ (ctZero K μ μ₂ τ₁ τ₂ hp D d d' A A' x).2.1
  have hA' : ∀ x, A'.J x ∈ fixF μ (levOn S U) := fun x =>
    hfix _ (ctZero K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A x).2.1
  rw [hT]
  refine ⟨⟨s, ⟨u, κ, hκ, fun x => ?_, hs⟩, fun v => funext fun x => hsec 0 v x⟩, fun P hP => ?_⟩
  · rw [← hact x, ContinuousLinearMap.comp_apply, (UpperTheory.ConvolutionTheory.Tf.commPrj K (2 + 2) μ _).2.2.2.1 _ (hA x)]
  · refine comm_proj A.J A'.J P _ _ hP hA hA' ?_ (hcomm P hP)
    refine (UpperTheory.ConvolutionTheory.Tf.hopLevel K (2 + 2) μ Measure.haar w (U w) _ _ (hU w).1.2 (hU w).1.1 ho hc ?_ hUJ).1
    rintro _ ⟨j, hj, rfl⟩
    exact hJU j hj
