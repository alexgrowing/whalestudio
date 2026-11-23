import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.FiniteProductSplitting

private noncomputable def glue {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {n : ℕ} (g : ∀ i, GL (Fin n) (R i)) :
    GL (Fin n) (∀ i, R i) where
  val := Matrix.of fun a b i => (g i : Matrix (Fin n) (Fin n) (R i)) a b
  inv := Matrix.of fun a b i => ((g i)⁻¹ : GL (Fin n) (R i)) a b
  val_inv := by
    ext a b i
    have := congrFun (congrFun (g i).mul_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl
  inv_val := by
    ext a b i
    have := congrFun (congrFun (g i).inv_mul a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl

private theorem glue_cont {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] {n : ℕ} :
    Continuous (glue : (∀ i, GL (Fin n) (R i)) → GL (Fin n) (∀ i, R i)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_coe_inv.comp (continuous_apply i)).matrix_elem a b

private theorem exists_ext {ι A : Type*} {X : A → Type*} (wi : ι → A) (hw : Function.Injective wi)
    (ψ : ∀ i, X (wi i)) (d : ∀ a, X a) :
    ∃ h : ∀ a, X a, (∀ i, h (wi i) = ψ i) ∧ ∀ a, a ∉ Set.range wi → h a = d a := by
  refine ⟨fun a => if ha : ∃ i, wi i = a then ha.choose_spec ▸ ψ ha.choose else d a, fun i => ?_,
    fun a ha => dif_neg ha⟩
  have key : ∀ j (hj : wi j = wi i), (hj ▸ ψ j : X (wi i)) = ψ i := by
    intro j hj
    obtain rfl := hw hj
    rfl
  have ha : ∃ j, wi j = wi i := ⟨i, rfl⟩
  simp only [dif_pos ha]
  exact key _ _

private theorem finprod_split {A M : Type*} [CommMonoid M] {r : ℕ} (wi : Fin r → A) (hw : Function.Injective wi)
    (X : A → M) (hX : (Function.mulSupport X).Finite) :
    ∏ᶠ u, X u = (∏ i, X (wi i)) * ∏ᶠ (u) (_ : u ∉ Set.range wi), X u := by
  have h := finprod_mem_inter_mul_diff' (f := X) (s := Set.univ) (Set.range wi)
    (hX.subset Set.inter_subset_right)
  rw [Set.univ_inter, finprod_mem_univ, finprod_mem_range hw, finprod_eq_prod_of_fintype] at h
  rw [← h]
  congr 1
  refine finprod_congr fun u => ?_
  simp only [Set.mem_diff, Set.mem_univ, true_and]

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem cmp_cont {v : Pl F} (w : PlacesOver E v) : Continuous (GM.cmp (n := n) w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem a b)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_coe_inv.matrix_elem a b)

private theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

private theorem iwCoset_zero (w : Pl E) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w)) := by
  have hd : Cartan.diagPow (w.adicCompletion E) n (0 : Fin n → ℤ) = 1 := by
    apply Units.ext
    rw [Cartan.coe_diagPow]
    simp
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [hd, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [hd, mul_one, mul_one]⟩

private theorem iw_test (w : Pl E) :
    IsLocallyConstant (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) ∧
      HasCompactSupport (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) := by
  have ho := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hc := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))
  · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem prodFn_eq {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    [Fintype (PlacesOver E v)] : GM.prodFn h = fun g => ∏ w, h w (GM.cmp w g) :=
  funext fun _ => finprod_eq_prod_of_fintype _

private theorem prodFn_test {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    (hc : ∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) :
    IsLocallyConstant (GM.prodFn h) ∧ HasCompactSupport (GM.prodFn h) := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  rw [prodFn_eq]
  constructor
  · have key : ∀ T : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ T, h w (GM.cmp w g) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hc a).1.comp_continuous (cmp_cont a)).mul ih
    exact key _
  · haveI : T2Space (CompletionsOver E v) := Pi.t2Space
    haveI : T2Space (GL (Fin n) (CompletionsOver E v)) := Units.instT2Space
    haveI : R1Space (GL (Fin n) (CompletionsOver E v)) := T2Space.r1Space
    refine HasCompactSupport.intro ((isCompact_univ_pi fun w => (hc w).2.isCompact).image glue_cont) fun g hg => ?_
    by_contra hne
    refine hg ⟨fun w => GM.cmp w g, fun w _ => subset_tsupport _ ?_, ?_⟩
    · exact fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    · exact Units.ext (Matrix.ext fun a b => rfl)

private theorem unit_prod (v : Pl F) :
    (GM.prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  funext g
  rw [GM.prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hg w) _
  · rw [Set.indicator_of_notMem hg]
    obtain ⟨w, hw⟩ := not_forall.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

private theorem iwFn_test {q : Pl F} (w₀ : PlacesOver E q) :
    IsLocallyConstant (GM.iwFn w₀ (0 : Fin n → ℤ)) ∧ HasCompactSupport (GM.iwFn w₀ (0 : Fin n → ℤ)) := by
  refine prodFn_test _ fun w => ?_
  rw [ite_self, iwCoset_zero]
  exact iw_test w.1

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private noncomputable def dflt (T : Ty σ n q w₀) (w : Pl E) : Gw n w → ℂ :=
  (T.J w : Set (Gw n w)).indicator fun x => conj (T.χ w x)

private theorem dflt_of_triv (T : Ty σ n q w₀) (w : Pl E) (h : T.χ w = 1) :
    dflt T w = (T.J w : Set (Gw n w)).indicator 1 := by
  unfold dflt
  rw [h]
  funext x
  by_cases hx : x ∈ (T.J w : Set (Gw n w))
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem sp_split (T : Ty σ n q w₀) {v : Pl F} (hv : v ∈ T.sp) : v ∈ T.S ∧ GM.Split E v :=
  Finset.mem_filter.1 hv

private theorem phi_eq (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ)
    (hF : T.Fits L ψ) (hq : GM.Split E q) (h : ∀ w : Pl E, Gw n w → ℂ)
    (h1 : ∀ v ∈ T.sp, h (T.mk' v).1 = ψ v)
    (h2 : ∀ w : Pl E, (∀ v ∈ T.sp, w ≠ (T.mk' v).1) → h w = dflt T w) (v : Pl F) :
    L.φ v = GM.prodFn fun u : PlacesOver E v => h u.1 := by
  have hother : ∀ (u : PlacesOver E v), v ∉ T.sp → h u.1 = dflt T u.1 := fun u hv => by
    refine h2 u.1 fun v' hv' e => hv ?_
    have : v' = v := by rw [← under_eq (T.mk' v'), ← e, under_eq u]
    rwa [← this]
  by_cases hsp : v ∈ T.sp
  · rw [(hF.split v hsp).1]
    congr 1
    funext u
    by_cases hu : u = T.mk' v
    · subst hu
      rw [Function.update_self, h1 v hsp]
    · rw [Function.update_of_ne hu, h2 u.1 fun v' hv' e => hu ?_,
        dflt_of_triv T u.1 (T.triv v (sp_split T hsp).2 u)]
      have : v' = v := by rw [← under_eq (T.mk' v'), ← e, under_eq u]
      subst this
      exact Subtype.ext e
  by_cases hS : v ∈ T.S
  · have hns : ¬ GM.Split E v := fun hs => hsp (Finset.mem_filter.2 ⟨hS, hs⟩)
    rw [hF.nonsplit v hS hns]
    congr 1
    funext u
    rw [hother u hsp]
    rfl
  by_cases hvq : v = q
  · subst hvq
    rw [L.at_q.1]
    unfold GM.iwFn
    congr 1
    funext u
    rw [hother u hsp, dflt_of_triv T u.1 (T.triv v hq u), ite_self, iwCoset_zero, T.at_q u]
  · have hvS : v ∉ L.S := by rw [hF.S_eq]; exact hS
    rw [(L.off v hvS hvq).1, ← unit_prod v]
    congr 1
    funext u
    have hu := T.off u.1 (by rw [under_eq]; exact hS) (by rw [under_eq]; exact hvq)
    rw [hother u hsp, dflt_of_triv T u.1 hu.2, hu.1]

end Main

end UpperTheory.FiniteProductSplitting

open UpperTheory.FiniteProductSplitting in
theorem UpperTheory.exists_pos_const_typed_test_function_bound :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
        ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n)
          (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ T : Ty σ n q w₀,
        ∃ κ : ℝ, 0 < κ ∧ ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
          ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ T.sp ↔ v ∈ Set.range p) →
          ∀ [∀ i, MeasurableSpace (Gw n (T.mk' (p i)).1)] [∀ i, BorelSpace (Gw n (T.mk' (p i)).1)]
            (mm : ∀ i, Measure (Gw n (T.mk' (p i)).1)), (∀ i, (mm i).IsHaarMeasure ∧ mm i (T.J (T.mk' (p i)).1) = 1) →
          ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm i) (ψ (p i)) (B i)) →
          ∀ g : TG E n, (∀ x, g x = avg (tensE (GM.onInf aE) L.φ) x) →
            Rop μ g = (κ : ℂ) • (Oinf μ νE aE ∘L (List.ofFn B).prod ∘L prj (T.typed μ)) := by
  intro F E _ _ _ _ _ σ n hn μ _ νE _ aE q w₀ hq T
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ ((insert q T.S : Finset (Pl F)) : Set (Pl F))}.Finite :=
    finite_under _ (Finset.finite_toSet _)
  have hcof : ∀ᶠ w : Pl E in Filter.cofinite,
      w.under (𝓞 F) ∉ T.S ∧ w.under (𝓞 F) ≠ q := by
    refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hw
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    tauto
  obtain ⟨κ, hκ, H⟩ := tensFactor E n hn μ νE T.J T.χ (fun w => ⟨T.co w, T.chr w⟩)
    (hcof.mono fun w hw => T.off w hw.1 hw.2)
  refine ⟨κ, hκ, ?_⟩
  intro L ψ hF r p hp hsp _ _ mm hmm B hB g hg
  have hpS : ∀ i, p i ∈ T.sp := fun i => (hsp _).2 ⟨i, rfl⟩
  have hwi : Function.Injective fun i => (T.mk' (p i)).1 := fun i j e => hp (by
    have e' : (T.mk' (p i)).1 = (T.mk' (p j)).1 := e
    rw [← under_eq (T.mk' (p i)), e', under_eq])
  obtain ⟨h, hh1, hh2⟩ := exists_ext (X := fun w : Pl E => Gw n w → ℂ) (fun i => (T.mk' (p i)).1) hwi
    (fun i => ψ (p i)) (dflt T)
  have h1 : ∀ v ∈ T.sp, h (T.mk' v).1 = ψ v := fun v hv => by
    obtain ⟨i, rfl⟩ := (hsp v).1 hv
    exact hh1 i
  have h2 : ∀ w : Pl E, (∀ v ∈ T.sp, w ≠ (T.mk' v).1) → h w = dflt T w := fun w hw =>
    hh2 w fun ⟨i, e⟩ => hw _ (hpS i) e.symm
  have hφ := phi_eq T L ψ hF hq h h1 h2
  have hint : ∀ᶠ w : Pl E in Filter.cofinite,
      h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1 := by
    refine hcof.mono fun w hw => ?_
    have hu := T.off w hw.1 hw.2
    have hne : ∀ v ∈ T.sp, w ≠ (T.mk' v).1 := fun v hv e => hw.1 (by
      rw [e, under_eq]; exact (sp_split T hv).1)
    rw [h2 w hne, dflt_of_triv T w hu.2, hu.1]
  obtain ⟨e, -, he, ht⟩ := GM.avgE F E n hn (insert q L.S) aE L.φ (fun v hv => by
      rcases Finset.mem_insert.1 hv with hvq | hv
      · rw [hvq, L.at_q.1]; exact iwFn_test w₀
      · exact ⟨(L.test v hv).1, (L.test v hv).2.1⟩)
    (fun v hv => (L.off v (fun h => hv (Finset.mem_insert_of_mem h))
      (fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _))).1)
  have hgt : g = tens aE e := by
    ext x
    rw [hg, ht]
  have heform : ∀ x, e x = (∏ i, ψ (p i) (finAt (T.mk' (p i)).1 (finEmb E n x))) *
      ∏ᶠ u ∉ Set.range (fun i => (T.mk' (p i)).1), (T.J u : Set (Gw n u)).indicator (fun g => conj (T.χ u g)) (finAt u (finEmb E n x)) := by
    intro x
    have e1 : e x = ∏ᶠ w, h w (finAt w (finEmb E n x)) := by
      rw [he x, ← UpperTheory.ConvolutionTheory.Tf.tensEProd F E n h hint (finEmb E n x)]
      exact finprod_congr fun v => by rw [hφ v]
    have hsupp : (Function.mulSupport fun w : Pl E => h w (finAt w (finEmb E n x))).Finite := by
      have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w (finEmb E n x)) = 1 := by
        filter_upwards [hint, AdelicGLn.eventually_mem_integralGL E n (finEmb E n x)] with w a1 a2
        rw [a1, Set.indicator_of_mem (by exact a2)]
        rfl
      exact Filter.eventually_cofinite.1 hev
    rw [e1, finprod_split _ hwi _ hsupp]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [hh1 i]
    · refine finprod_congr fun u => finprod_congr fun hu => ?_
      rw [hh2 u hu]
      rfl
  have main := H aE r (fun i => (T.mk' (p i)).1) hwi mm hmm (fun i => ψ (p i)) B (fun i => ⟨(hF.test _ (hpS i)).1,
    fun u hu g' => by
      have hχ := T.triv (p i) (sp_split T (hpS i)).2 (T.mk' (p i))
      rw [((hF.test _ (hpS i)).2 u hu g').2, hχ]
      simp, hB i⟩) e heform
  rw [hgt]
  exact main
