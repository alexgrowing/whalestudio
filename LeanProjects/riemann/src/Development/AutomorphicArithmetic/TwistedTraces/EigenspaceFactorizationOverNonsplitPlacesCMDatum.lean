import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Abs

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rho_typed (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (f : LL μ)
    (hf : ∀ w, f ∈ eigL μ w (J w) (χ w)) (P : Finset (Pl K))
    (hP : ∀ w ∉ P, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) (R : Finset (Pl K)) :
    ∀ g : AdelicGLn.FiniteAdelicGL K n, (∀ w ∈ R, finAt w (finEmb K n g) ∈ J w) →
      (∀ w ∈ P, w ∉ R → finAt w (finEmb K n g) = 1) →
      (∀ w ∉ P, finAt w (finEmb K n g) ∈ GLnLocal.integralGL (w.adicCompletion K) n) →
      rhoF μ g f = (∏ w ∈ R, χ w (finAt w (finEmb K n g))) • f := by
  obtain ⟨-, -, -, -, -, hmul, hone, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have heig : ∀ w, ∀ x ∈ J w, rhoF μ (AdelicGLn.localEmbedding w x) f = χ w x • f := fun w x hx => by
    have := hf w
    simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] at this
    simpa [rhoL] using this x hx
  induction R using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have hfix : f ∈ fixF μ (levOn P fun _ => ⊥) := by
      rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ P]
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨e1, e2⟩ := hP v hv
        have := heig v x (by rw [e1]; exact hx)
        rw [this, e2]
        simp
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot.1 hx, map_one, hone]
        rfl
    have hg : g ∈ levOn P (fun _ => ⊥) := by
      intro v
      by_cases hv : v ∈ P
      · simp only [hv, if_true]
        exact Subgroup.mem_bot.2 (h1 v hv (Finset.notMem_empty v))
      · simp only [hv, if_false]
        exact h2 v hv
    simpa using ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).1 hfix g hg
  | insert a R ha ih =>
    intro g h0 h1 h2
    obtain ⟨-, e1, e2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n a
    set x := finAt a (finEmb K n g) with hx
    set g' := (AdelicGLn.localEmbedding a x)⁻¹ * g with hg'
    have hc : ∀ w, w ≠ a → finAt w (finEmb K n g') = finAt w (finEmb K n g) := fun w hw => by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e2 w hw]
      simp
    have hca : finAt a (finEmb K n g') = 1 := by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e1]
      simp [hx]
    have key := ih g' (fun w hw => by
        have hwa : w ≠ a := fun h => ha (h ▸ hw)
        rw [hc w hwa]
        exact h0 w (Finset.mem_insert_of_mem hw))
      (fun w hw hwR => by
        by_cases hwa : w = a
        · subst hwa; exact hca
        · rw [hc w hwa]
          exact h1 w hw (by simp [hwa, hwR]))
      (fun w hw => by
        by_cases hwa : w = a
        · subst hwa; rw [hca]; exact one_mem _
        · rw [hc w hwa]; exact h2 w hw)
    have hgg : g = AdelicGLn.localEmbedding a x * g' := by simp [hg']
    have hprod : ∏ w ∈ R, χ w (finAt w (finEmb K n g')) = ∏ w ∈ R, χ w (finAt w (finEmb K n g)) :=
      Finset.prod_congr rfl fun w hw => by
        rw [hc w fun h => ha (h ▸ hw)]
    have hstep : rhoF μ g f = rhoF μ (AdelicGLn.localEmbedding a x) (rhoF μ g' f) := by
      conv_lhs => rw [hgg, hmul]
      rfl
    rw [hstep, key, hprod, map_smul, heig a x (h0 a (Finset.mem_insert_self a R)), smul_smul,
      Finset.prod_insert ha, mul_comm]

end Abs

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over' {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_atFin' {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

private theorem fin_above' (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem cmp_homeo {v : Pl F} (u : PlacesOver E v) (hu : ∀ u' : PlacesOver E v, u' = u) :
    IsOpenMap (GM.cmp (n := n) u) ∧ Function.Surjective (GM.cmp (n := n) u) := by
  letI : Unique (PlacesOver E v) := ⟨⟨u⟩, hu⟩
  let s : (u.1.adicCompletion E) ≃+* CompletionsOver E v :=
    (RingEquiv.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)).symm
  have hs : Continuous s.toRingHom :=
    (Homeomorph.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)).symm.continuous
  have h1 : ∀ a : GL (Fin n) (u.1.adicCompletion E), GM.cmp u (mapGL n s.toRingHom a) = a := fun a => by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact s.symm_apply_apply _
  have h2 : ∀ x : GL (Fin n) (CompletionsOver E v), mapGL n s.toRingHom (GM.cmp u x) = x := fun x => by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact s.apply_symm_apply _
  let e : GL (Fin n) (CompletionsOver E v) ≃ₜ GL (Fin n) (u.1.adicCompletion E) :=
    { toFun := GM.cmp u
      invFun := mapGL n s.toRingHom
      left_inv := h2
      right_inv := h1
      continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (continuous_apply u))
      continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map hs) }
  exact ⟨e.isOpenMap, e.surjective⟩

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem lvN_co (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) {v : Pl F} (hv : v ∈ L.S)
    (hu : ∀ u : PlacesOver E v, u = T.mk' v) : CO (lvN T L v) := by
  have ho : IsOpen (lvN T L v : Set (Gw n (T.mk' v).1)) := by
    have := (cmp_homeo (n := n) (T.mk' v) hu).1 _ (L.lev v hv).1
    simpa [lvN] using this
  refine ⟨(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) ?_, ho⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (L.lev v hv).2.1 hx (T.mk' v)

private theorem eig_of_fix (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
    {v : Pl F} (u : PlacesOver E v) (hu : u = T.mk' v) (f : LL μ) (h : f ∈ fixL μ (T.mk' v).1 (lvN T L v)) :
    f ∈ eigL μ u.1 ((L.UE v).map (GM.cmp u)) 1 := by
  subst hu
  have h' : ∀ g ∈ lvN T L v, rhoF μ (AdelicGLn.localEmbedding (T.mk' v).1 g) f = f := fun g hg => by
    have h2 : ∀ y ∈ (lvN T L v).map (AdelicGLn.localEmbedding (T.mk' v).1), rhoF μ y f = f := by
      simpa [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus] using h
    exact h2 _ ⟨g, hg, rfl⟩
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  intro x hx
  simpa [rhoL] using h' x hx

private theorem at_place (hq : GM.Split E q) (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
    {ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ} (hF : FitsV T L ψ) (v : Pl F) (hv : v ∉ nsS T)
    (x : GL (Fin n) (CompletionsOver E v)) (hx : x ∈ L.UE v) :
    (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := by
  have easy : (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) → (∀ u : PlacesOver E v, T.χ u.1 = 1) →
      (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := fun h1 h2 => by
    refine ⟨h1, ?_⟩
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_eq_one fun u _ => ?_
    rw [Set.indicator_of_mem (by exact h1 u), h2 u]
    rfl
  by_cases hvq : v = q
  · subst hvq
    refine easy (fun u => ?_) (T.triv v hq)
    rw [T.at_q u]
    exact (L.at_q.2.2.1 x).1 hx u
  by_cases hvS : v ∈ T.S
  · have hs : GM.Split E v := by
      by_contra hs
      exact hv (Finset.mem_filter.2 ⟨hvS, hs⟩)
    have hsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hvS, hs⟩
    exact easy (((hF.split v hsp).2 x).1 hx) (T.triv v hs)
  · have hvL : v ∉ L.S := fun h => hvS (hF.S_eq ▸ h)
    have hu : x ∈ unitSet E n v := by
      rw [← (L.off v hvL hvq).2.2.1]
      exact hx
    have hoff : ∀ u : PlacesOver E v, T.J u.1 = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ T.χ u.1 = 1 := fun u =>
      T.off u.1 (by rwa [under_over']) (by rwa [under_over'])
    refine easy (fun u => ?_) fun u => (hoff u).2
    rw [(hoff u).1]
    exact hu u

end SlopeTestRemainingChoices

theorem UpperTheory.eigenspace_factorization_over_nonsplit_places_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q →
        ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀)
          (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), FitsV T L ψ → (∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v) →
        ∀ (r : ℕ) (p : Fin r → Pl F), (∀ v, v ∈ nsS T ↔ v ∈ Set.range p) →
          (∀ i, CO (lvN T L (p i))) ∧ (∀ i, ∀ u ∈ lvN T L (p i), ∀ g, ψ (p i) (u * g) = ψ (p i) g) ∧
          offN μ T ⊓ (⨅ i, fixL μ (T.mk' (p i)).1 (lvN T L (p i))) ≤ fixF μ (GM.levE L.UE) := by
  intro F E _ _ _ _ _ σ n q w₀ hq μ _ T L ψ hF hun r p hp
  have hpS : ∀ i, p i ∈ nsS T := fun i => (hp _).2 ⟨i, rfl⟩
  have hS : ∀ i, p i ∈ T.S ∧ ¬ GM.Split E (p i) := fun i => Finset.mem_filter.1 (hpS i)
  have hLS : ∀ i, p i ∈ L.S := fun i => hF.S_eq ▸ (hS i).1
  refine ⟨fun i => lvN_co T L (hLS i) (hun _ (hpS i)), ?_, ?_⟩
  · rintro i _ ⟨x, hx, rfl⟩ g
    obtain ⟨y, rfl⟩ := (cmp_homeo (n := n) (T.mk' (p i)) (hun _ (hpS i))).2 g
    rw [← map_mul, ← hF.nonsplit _ (hS i).1 (hS i).2, ← hF.nonsplit _ (hS i).1 (hS i).2]
    exact (L.inv _ (hLS i)).1 x hx y
  intro f hf
  obtain ⟨hoff, hfix⟩ := Submodule.mem_inf.1 hf
  have hfix' : ∀ i, f ∈ fixL μ (T.mk' (p i)).1 (lvN T L (p i)) := (Submodule.mem_iInf _).1 hfix
  let J' : ∀ w : Pl E, Subgroup (Gw n w) := fun w =>
    if w.under (𝓞 F) ∈ nsS T then
      (L.UE (w.under (𝓞 F))).map (GM.cmp (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F)))) else T.J w
  let χ' : ∀ w : Pl E, Gw n w → ℂ := fun w => if w.under (𝓞 F) ∈ nsS T then 1 else T.χ w
  have hJpos : ∀ w : Pl E, w.under (𝓞 F) ∈ nsS T →
      J' w = (L.UE (w.under (𝓞 F))).map (GM.cmp (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F)))) ∧ χ' w = 1 :=
    fun w hw => ⟨if_pos hw, if_pos hw⟩
  have hJneg : ∀ w : Pl E, w.under (𝓞 F) ∉ nsS T → J' w = T.J w ∧ χ' w = T.χ w :=
    fun w hw => ⟨if_neg hw, if_neg hw⟩
  have hfw : ∀ w, f ∈ eigL μ w (J' w) (χ' w) := fun w => by
    by_cases hw : w.under (𝓞 F) ∈ nsS T
    · rw [(hJpos w hw).1, (hJpos w hw).2]
      obtain ⟨i, hi⟩ := (hp _).1 hw
      have h1 := hfix' i
      rw [hi] at h1
      exact eig_of_fix μ T L (v := w.under (𝓞 F)) (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F))) (hun _ hw _) f h1
    · rw [(hJneg w hw).1, (hJneg w hw).2]
      exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hoff w) hw
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.1 f).2 fun g hg => ?_
  have hX : ∀ v : Pl F, mapGL n (atFin v) (finEmb E n g) ∈ L.UE v := fun v => Subgroup.mem_iInf.1 hg v
  have hJ : ∀ w : Pl E, finAt w (finEmb E n g) ∈ J' w := fun w => by
    by_cases hw : w.under (𝓞 F) ∈ nsS T
    · rw [(hJpos w hw).1]
      exact ⟨_, hX _, cmp_atFin' (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F))) _⟩
    · rw [(hJneg w hw).1]
      have := (at_place hq T L hF _ hw _ (hX _)).1 (⟨w, ⟨rfl⟩⟩ : PlacesOver E (w.under (𝓞 F)))
      rwa [cmp_atFin'] at this
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
    refine ((insert q T.S).finite_toSet.biUnion fun v _ => fin_above' (E := E) v).subset ?_
    intro w hw
    exact Set.mem_biUnion (x := w.under (𝓞 F)) hw rfl
  set P : Finset (Pl E) := hfin.toFinset with hPdef
  have hP : ∀ w ∉ P, J' w = GLnLocal.integralGL (w.adicCompletion E) n ∧ χ' w = 1 := fun w hw => by
    have h0 : w.under (𝓞 F) ∉ insert q T.S := fun h => hw (hfin.mem_toFinset.2 h)
    rw [Finset.mem_insert, not_or] at h0
    have hns : w.under (𝓞 F) ∉ nsS T := fun h => h0.2 (Finset.mem_filter.1 h).1
    rw [(hJneg w hns).1, (hJneg w hns).2]
    exact T.off w h0.2 h0.1
  have hr := rho_typed μ J' χ' f hfw P hP P g (fun w _ => hJ w) (fun w h1 h2 => absurd h1 h2)
    (fun w hw => by rw [← (hP w hw).1]; exact hJ w)
  have hone : ∏ w ∈ P, χ' w (finAt w (finEmb E n g)) = 1 := by
    have ht := UpperTheory.ConvolutionTheory.Tf.tensEProd F E n (fun w => (J' w : Set (Gw n w)).indicator (χ' w))
      (by
        refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
        by_contra hc
        apply hw
        have hwP : w ∉ P := fun h => hc (hfin.mem_toFinset.1 h)
        obtain ⟨e1, e2⟩ := hP w hwP
        simp only [e1, e2]) (finEmb E n g)
    have hl : ∀ v : Pl F, GM.prodFn (v := v) (fun w => (J' w.1 : Set (Gw n w.1)).indicator (χ' w.1))
        (mapGL n (atFin v) (finEmb E n g)) = 1 := fun v => by
      unfold GM.prodFn
      by_cases hv : v ∈ nsS T
      · rw [finprod_eq_prod_of_fintype]
        refine Finset.prod_eq_one fun u _ => ?_
        have hu : u.1.under (𝓞 F) ∈ nsS T := by rwa [under_over']
        rw [cmp_atFin']
        beta_reduce
        rw [Set.indicator_of_mem (show finAt u.1 (finEmb E n g) ∈ (J' u.1 : Set (Gw n u.1)) from hJ u.1), (hJpos u.1 hu).2]
        rfl
      · have hu : ∀ u : PlacesOver E v, u.1.under (𝓞 F) ∉ nsS T := fun u => by rwa [under_over']
        rw [← (at_place hq T L hF v hv _ (hX v)).2]
        exact finprod_congr fun u => by
          beta_reduce
          rw [(hJneg u.1 (hu u)).1, (hJneg u.1 (hu u)).2]
    simp only [hl, finprod_one] at ht
    rw [finprod_eq_prod_of_mulSupport_subset (s := P)] at ht
    · rw [ht]
      exact Finset.prod_congr rfl fun w _ => (Set.indicator_of_mem (by exact hJ w) _).symm
    · intro w hw
      by_contra hc
      apply hw
      obtain ⟨e1, e2⟩ := hP w (by simpa using hc)
      simp only [Set.indicator_of_mem (show finAt w (finEmb E n g) ∈ (J' w : Set (Gw n w)) from hJ w), e2]
      rfl
  rw [hr, hone, one_smul]
