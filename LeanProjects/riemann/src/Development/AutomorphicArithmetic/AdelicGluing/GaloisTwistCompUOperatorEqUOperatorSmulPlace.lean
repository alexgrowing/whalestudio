import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AdelicGluing.ExistsGaloisTransportLocalGLPreservingIwahori
import Development.AutomorphicArithmetic.AdelicGluing.GalTwistFinProjEqOfGalAdFinEmbEq
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem prj_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H) (W W' : Submodule ℂ H) (hW : IsClosed (W : Set H)) (hW' : IsClosed (W' : Set H))
    (hU : ∀ v, U v ∈ W' ↔ v ∈ W) (v : H) : U (prj W v) = prj W' (U v) := by
  have hc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hc' : W'.topologicalClosure = W' := hW'.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ W.topologicalClosure ↔ v ∈ W := fun v => by rw [hc]
  have hm' : ∀ v, v ∈ W'.topologicalClosure ↔ v ∈ W' := fun v => by rw [hc']
  have a1 : prj W v ∈ W := (hm _).1 (Submodule.starProjection_apply_mem _ v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm' _).2 ((hU _).2 a1)) fun u hu => ?_
  have hu' : U.symm u ∈ W := (hU _).1 (by simpa using (hm' _).1 hu)
  have e : u = U (U.symm u) := by simp
  rw [e, ← map_sub, LinearIsometryEquiv.inner_map_map]
  exact Submodule.starProjection_inner_eq_zero v _ ((hm _).2 hu')

private theorem mk_iff {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (a b : G) :
    (QuotientGroup.mk (s a) : G' ⧸ J') = QuotientGroup.mk (s b) ↔
      (QuotientGroup.mk a : G ⧸ J) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, hJ, map_mul, map_inv]

private theorem cosets {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (x : G)
    (hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → G),
      Function.Injective (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) ∧
      Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} ∧
      Function.Injective (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) ∧
      Set.range (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) =
        {c | ∃ k ∈ J', c = QuotientGroup.mk (k * s x)} := by
  classical
  let S := {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
  haveI : Fintype S := hS.fintype
  have hout : ∀ c : S, (QuotientGroup.mk (c.1.out) : G ⧸ J) = c.1 := fun c => QuotientGroup.out_eq' c.1
  refine ⟨S, inferInstance, fun c => c.1.out, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    have h' : (QuotientGroup.mk (a.1.out) : G ⧸ J) = QuotientGroup.mk (b.1.out) := h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      have : (QuotientGroup.mk (i.1.out) : G ⧸ J) ∈ S := by rw [hout]; exact i.2
      exact this
    · intro hc
      exact ⟨⟨c, hc⟩, hout ⟨c, hc⟩⟩
  · intro a b h
    apply Subtype.ext
    have h' := (mk_iff s J J' hJ _ _).1 h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk, e⟩ := i.2
      refine ⟨s k, (hJ k).1 hk, ?_⟩
      have h1 : (QuotientGroup.mk (i.1.out) : G ⧸ J) = QuotientGroup.mk (k * x) := (hout i).trans e
      have h2 := (mk_iff s J J' hJ _ _).2 h1
      rw [map_mul] at h2
      exact h2
    · rintro ⟨k, hk, rfl⟩
      have hk0 : s.symm k ∈ J := (hJ _).2 (by simpa using hk)
      have hc : (QuotientGroup.mk (s.symm k * x) : G ⧸ J) ∈ S := ⟨_, hk0, rfl⟩
      refine ⟨⟨_, hc⟩, ?_⟩
      have h2 := (mk_iff s J J' hJ _ _).2 (hout ⟨_, hc⟩)
      rw [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2

private theorem cosets_eq {G : Type} [Group G] (J : Subgroup G) (a b x : G) (ha : a ∈ J) (hb : b ∈ J) :
    {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * (a * x * b))} =
      {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} := by
  have key : ∀ k : G, (QuotientGroup.mk (k * (a * x * b)) : G ⧸ J) = QuotientGroup.mk (k * a * x) := fun k => by
    rw [QuotientGroup.eq]
    have e : (k * (a * x * b))⁻¹ * (k * a * x) = b⁻¹ := by group
    rw [e]
    exact J.inv_mem hb
  ext c
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * a, J.mul_mem hk ha, key k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, J.mul_mem hk (J.inv_mem ha), ?_⟩
    rw [key]
    simp

private theorem fixL_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v := by
  unfold fixL
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.1]
  constructor
  · exact fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
          ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (w : Pl E) (ν : Fin n → ℤ),
            θ.U ∘L Uiw μ w ν = Uiw μ (σ • w) ν ∘L θ.U := by
  intro F E _ _ _ _ _ _ σ n hn μ _ θ hθ w ν
  obtain ⟨s, hs1, hs2, hs3⟩ := UpperTheory.exists_galois_transport_localGL_preserving_iwahori F E σ n hn w
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ
  have hO := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hC := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  have hO' := GLnLocal.isOpen_iwahori ((σ • w).adicCompletion E) n
  have hC' := GLnLocal.isCompact_iwahori ((σ • w).adicCompletion E) n
  have hrho : ∀ g v, U (rhoL μ w g v) = rhoL μ (σ • w) (s g) (U v) := fun g v => by
    have e := UpperTheory.galTwist_finProj_eq_of_galAd_finEmb_eq F E σ n hn μ θ hθ _ _ (hs1 g)
    show U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding w g)) v) =
      rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding (σ • w) (s g))) (U v)
    rw [hint, e]
  have hfx : ∀ v, U v ∈ fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) ↔
      v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) := fun v => by
    rw [fixL_iff, fixL_iff]
    constructor
    · intro h k hk
      apply U.injective
      rw [hrho]
      exact h _ ((hs2 k).1 hk)
    · intro h k' hk'
      have e : k' = s (s.symm k') := by simp
      rw [e, ← hrho, h _ ((hs2 _).2 (by simpa using hk'))]
  have hP : ∀ v, U (prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v) =
      prj (fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n)) (U v) :=
    prj_map U _ _ (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 hfx
  obtain ⟨hf, -, hHP, hsum, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w _
    (Cartan.diagPow (w.adicCompletion E) n ν) hO hC
  obtain ⟨-, -, hHP', hsum', -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ (σ • w) _
    (s (Cartan.diagPow (w.adicCompletion E) n ν)) hO' hC'
  obtain ⟨ι, _, y, i1, r1, i2, r2⟩ := cosets s _ _ hs2 _ hf
  have hmain : ∀ v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n),
      U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
        Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v) := fun v hv => by
    rw [hsum ι y i1 r1 v hv, hsum' ι (fun i => s (y i)) i2 r2 (U v) ((hfx v).2 hv), map_sum]
    exact Finset.sum_congr rfl fun i _ => hrho _ _
  obtain ⟨a, ha, b, hb, hab⟩ := hs3 ν
  have hH : Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) =
      Uiw μ (σ • w) ν := by
    unfold Uiw Hop
    rw [hab, cosets_eq _ a b _ ha hb]
  rw [← hU, ← hH]
  refine ContinuousLinearMap.ext fun v => ?_
  have e1 := DFunLike.congr_fun hHP v
  have e2 := DFunLike.congr_fun hHP' (U v)
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  have hm : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.2.1 v
  show U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
    Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v)
  rw [← e1, hmain _ hm, hP, e2]
