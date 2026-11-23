import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ClopenTest
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.InfAtFinEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocAll
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.BcPoly
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.WordHt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchOfScale
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.G1St

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private def glue {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {n : ℕ} (g : ∀ i, GL (Fin n) (R i)) :
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

private theorem cmp_cont {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) : Continuous (cmp (n := n) w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem a b)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_coe_inv.matrix_elem a b)

private theorem prodFn_test {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ) (hc : ∀ w, Continuous (h w) ∧ HasCompactSupport (h w)) :
    Continuous (prodFn h) ∧ HasCompactSupport (prodFn h) := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  have e : prodFn h = fun g => ∏ w, h w (cmp w g) := funext fun g => finprod_eq_prod_of_fintype _
  rw [e]
  refine ⟨continuous_finset_prod _ fun w _ => (hc w).1.comp (cmp_cont w), ?_⟩
  haveI : T2Space (CompletionsOver E v) := Pi.t2Space
  haveI : T2Space (GL (Fin n) (CompletionsOver E v)) := Units.instT2Space
  haveI : R1Space (GL (Fin n) (CompletionsOver E v)) := T2Space.r1Space
  refine HasCompactSupport.intro ((isCompact_univ_pi fun w => (hc w).2.isCompact).image glue_cont) fun g hg => ?_
  by_contra hne
  refine hg ⟨fun w => cmp w g, fun w _ => subset_tsupport _ ?_, ?_⟩
  · exact fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
  · exact Units.ext (Matrix.ext fun a b => rfl)

private theorem prodFn_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F} :
    (prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _).indicator 1) =
      (unitSet E n v).indicator 1 := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  funext g
  rw [prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hg w) _
  · rw [Set.indicator_of_notMem hg]
    obtain ⟨w, hw⟩ := not_forall.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

open scoped Pointwise in
private theorem iwCoset_test {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    Continuous ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) ∧ HasCompactSupport ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have e : iwCoset w ν = (GLnLocal.iwahori (w.adicCompletion K) n : Set _) * {Cartan.diagPow (w.adicCompletion K) n ν} *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
    · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hc : IsCompact (iwCoset w ν) := by
    rw [e]; exact ((GLnLocal.isCompact_iwahori _ _).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ _)
  have ho : IsOpen (iwCoset w ν) := by
    rw [e]; exact (GLnLocal.isOpen_iwahori _ _).mul_left
  exact ⟨IsClopen.continuous_indicator ⟨hc.isClosed, ho⟩ continuous_const,
    HasCompactSupport.intro hc fun g hg => Set.indicator_of_notMem hg _⟩

open Classical in
private theorem mono_split {E : Type} [Field E] [NumberField E] {n : ℕ} (κ : Finset (Pl E)) (β : Pl E × Fin n →₀ ℕ)
    (hβ : ∀ x ∈ β.support, x.1 ∈ κ) : ∃ p : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, (p w).totalDegree ≤ β.degree) ∧
      ∏ w ∈ κ, atPl w (p w) = monomial β 1 := by
  refine ⟨fun w => ∏ i, X i ^ β (w, i), fun w _ => ?_, ?_⟩
  · refine (totalDegree_finset_prod _ _).trans ?_
    simp only [totalDegree_X_pow]
    have h1 : ∑ i, β (w, i) = ∑ x ∈ Finset.univ.image (fun i : Fin n => (w, i)), β x := by
      rw [Finset.sum_image]; intro a _ b _ h; exact (Prod.ext_iff.1 h).2
    rw [h1, Finsupp.degree_apply]
    exact Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx
  · simp only [atPl, map_prod, map_pow, rename_X]
    rw [← Finset.prod_product' κ Finset.univ (fun w i => (X (w, i) : MvPolynomial (Pl E × Fin n) ℂ) ^ β (w, i)), monomial_eq, C_1, one_mul,
      Finsupp.prod_of_support_subset β (s := κ ×ˢ Finset.univ) (fun x hx => Finset.mem_product.2 ⟨hβ x hx, Finset.mem_univ _⟩) _
        (fun _ _ => pow_zero _)]

private theorem sup_mono {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {n : ℕ} {q : Pl F}
    {w₀ : PlacesOver K q} {ν : Fin n → ℤ} {j : ℕ} {Y Y' : ℝ} {f : normOneGL K n → ℂ} (h : Sup w₀ ν j Y f) (hY : Y ≤ Y') :
    Sup w₀ ν j Y' f := fun g hg => ⟨(h g hg).1.trans hY, (h g hg).2⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem onInf_test {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) :
    Continuous (onInf β) ∧ HasCompactSupport (onInf β) :=
  ⟨β.continuous.comp (archEquiv K n).continuous, β.hasCompactSupport.comp_homeomorph (archEquiv K n).toHomeomorph⟩

set_option maxHeartbeats 1000000 in
theorem UpperTheory.ConvolutionTheory.GM.termEx :
    LocUnit → TermEx := by
  intro hU F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE iμE μF iμF θ q w₀ q₀ hq νE _ νF _ aE aF ci hci hA
  classical
  letI : MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E)) := borel _
  haveI : BorelSpace (GL (Fin n) (InfiniteAdeleRing E)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin n) (InfiniteAdeleRing F)) := ⟨rfl⟩
  choose s1 b1 s2 b2 mE mF hm using fun v => (matchOne F E σ n v).1
  obtain ⟨k, hk, H4⟩ := UpperTheory.ConvolutionTheory.G.g4 F E σ hσ n hn hp μE μF (νE.map (archEquiv E n).symm) (νF.map (archEquiv F n).symm) mE mF
    iμE iμF ((archEquiv E n).symm.isHaarMeasure_map νE) ((archEquiv F n).symm.isHaarMeasure_map νF)
    (fun v => ⟨(hm v).1, (hm v).2.2.1⟩) (fun v => ⟨(hm v).2.1, (hm v).2.2.2⟩)
  obtain ⟨cq, hcq, HQ⟩ := UpperTheory.ConvolutionTheory.L1.locQ F E σ hσ hp n hn q hq
  refine ⟨k * ci * cq, by positivity, fun L ν hν 𝔢 𝔣 he hf => ?_⟩
  obtain ⟨YE, hYE, TE⟩ := termE F E σ hσ hp n hn μE θ q w₀ νE aE L ν hν 𝔢 he
  obtain ⟨YF, hYF, TF⟩ := termF F E σ hσ hp n hn μF q w₀ q₀ νF aF L ν hν 𝔣 hf
  refine ⟨max YE YF, le_max_of_le_left hYE, fun κ hκ t₀ ht D => ?_⟩
  have hκ' : ∀ w ∈ κ, w.under (𝓞 F) ∉ L.S ∧ w.under (𝓞 F) ≠ q := fun w hw => not_or.1 (mt (he.2.2.1 w).2 (hκ w hw))
  obtain ⟨γ, hγ, LA⟩ := locAll hU F E σ hσ hp n hn κ (fun w hw => L.unr _ (hκ' w hw).1) t₀ ht D
  refine ⟨∏ w ∈ κ, atPl w (γ w), fun x hx => ?_, ?_, fun β hβ hD => ?_⟩
  · obtain ⟨w, hw, hx⟩ := Finset.mem_biUnion.1 (vars_prod _ hx)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (vars_rename _ _ hx)
    exact hw
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun w hw => ?_
    rw [atPl, eval_rename]
    exact hγ w hw
  obtain ⟨p, hp1, hp2⟩ := mono_split κ β hβ
  have hhE : ∀ w : Pl E, ∃ h : GL (Fin n) (w.adicCompletion E) → ℂ, (w ∈ κ → IsSph w (γ w * p w) h) ∧
      (w ∉ κ → h = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) ∧ Continuous h ∧ HasCompactSupport h := by
    intro w
    obtain ⟨a, b, c⟩ := sphEx E n hn w
    by_cases hw : w ∈ κ
    · obtain ⟨h, hh⟩ := a (γ w * p w)
      exact ⟨h, fun _ => hh, fun h' => absurd hw h', (c _ _ hh).1.continuous, (c _ _ hh).2.1⟩
    · exact ⟨_, fun h' => absurd h' hw, fun _ => rfl, (c _ _ b).1.continuous, (c _ _ b).2.1⟩
  choose h h1 h2 h3 using hhE
  obtain ⟨κF, hκF⟩ : ∃ κF : Finset (Pl F), ∀ v, v ∈ κF ↔ ∃ w ∈ κ, w.under (𝓞 F) = v :=
    ⟨κ.image fun w => w.under (𝓞 F), fun v => Finset.mem_image⟩
  have hhF : ∀ v : Pl F, ∃ f : GL (Fin n) (v.adicCompletion F) → ℂ,
      IsSph v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w)) f ∧
      (v ∉ κF → f = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1) ∧ Continuous f ∧ HasCompactSupport f := by
    intro v
    obtain ⟨a, b, c⟩ := sphEx F n hn v
    by_cases hv : v ∈ κF
    · obtain ⟨f, hh⟩ := a (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w))
      exact ⟨f, hh, fun h' => absurd hv h', (c _ _ hh).1.continuous, (c _ _ hh).2.1⟩
    · refine ⟨_, ?_, fun _ => rfl, (c _ _ b).1.continuous, (c _ _ b).2.1⟩
      rw [Finset.filter_eq_empty_iff.2 fun w hw e => hv ((hκF v).2 ⟨w, hw, e⟩), Finset.prod_empty]
      exact b
  choose f f1 f2 f3 using hhF
  have hκF' : ∀ v ∈ κF, v ∉ L.S ∧ v ≠ q := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := (hκF v).1 hv
    exact hκ' w hw
  obtain ⟨Y1, hY1, TE⟩ := TE κ hκ (fun w => γ w * p w) h h1 h2
  obtain ⟨Y2, hY2, TF⟩ := TF κF (fun v hv => mt (hf.2.2.1 v).1 (not_or.2 (hκF' v hv))) _ f (fun v _ => f1 v) f2
  refine ⟨max Y1 Y2, le_max_of_le_left hY1, fun evE evF hE hF j wd => ?_⟩
  obtain ⟨φ, φS, φq, φo⟩ : ∃ φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ, (∀ v ∈ L.S, φ v = L.φ v) ∧
      φ q = iwFn w₀ (fun i => (j : ℤ) * ν i) ∧ ∀ v ∉ L.S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1 :=
    ⟨Function.update (fun v => if v ∈ L.S then L.φ v else prodFn fun w : PlacesOver E v => h w.1) q (iwFn w₀ fun i => (j : ℤ) * ν i),
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨ψ, ψS, ψq, ψo⟩ : ∃ ψ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ, (∀ v ∈ L.S, ψ v = L.f v) ∧
      ψ q = (iwCoset q fun i => (j : ℤ) * ν i).indicator 1 ∧ ∀ v ∉ L.S, v ≠ q → ψ v = f v :=
    ⟨Function.update (fun v => if v ∈ L.S then L.f v else f v) q ((iwCoset q fun i => (j : ℤ) * ν i).indicator 1),
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨c, cS, cq', co⟩ : ∃ c : Pl F → ℂ, (∀ v ∈ L.S, c v = L.c v) ∧ c q = cq ∧ ∀ v ∉ L.S, v ≠ q → c v = 1 :=
    ⟨Function.update (fun v => if v ∈ L.S then L.c v else 1) q cq,
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨fE, e1, e2, e3⟩ := TE evE hE j wd φ φS φq φo
  obtain ⟨fF, g1, g2, g3⟩ := TF evF hF j (wd.map (resIx F)) ψ ψS ψq ψo
  have hpoly : (map C (∏ w ∈ κ, atPl w (γ w)) * monomial β (mono wd) : PR E n) =
      C (mono wd) * map C (∏ w ∈ κ, atPl w (γ w * p w)) := by
    have : ∏ w ∈ κ, atPl w (γ w * p w) = (∏ w ∈ κ, atPl w (γ w)) * monomial β 1 := by
      rw [← hp2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => map_mul (rename _) _ _
    rw [this, map_mul, map_monomial, C_1, mul_left_comm, C_mul_monomial, mul_one]
  rw [List.length_map] at g3
  have h0 : (0 : ℝ) ≤ max Y1 Y2 := le_max_of_le_left (zero_le_one.trans hY1)
  refine ⟨fE, fF, by rw [hpoly]; exact e2, ?_, sup_mono e3 ?_, sup_mono g3 ?_, ?_⟩
  · rw [hpoly, bcPoly F E n κ κF (fun w hw => (hκF _).2 ⟨w, hw, rfl⟩)]
    exact g2
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (zero_le_one.trans hYE) (le_max_left _ _) _) (by positivity) h0
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (zero_le_one.trans hYF) (le_max_right _ _) _) (by positivity) h0
  have key := H4 (insert q (L.S ∪ κF)) (onInf (word νE aE (none :: wd))) (onInf (word νF aF (none :: wd.map (resIx F)))) φ ψ ci c
    (onInf_test _).1 (onInf_test _).2 (onInf_test _).1 (onInf_test _).2 (fun v => ?_) (fun v hv => ?_) (hA (none :: wd)) (fun v => ?_)
  · have hc : (k : ℂ) * ci * ∏ v ∈ insert q (L.S ∪ κF), c v = ((k * ci * cq : ℝ) : ℂ) * ∏ v ∈ L.S, L.c v := by
      rw [Finset.prod_insert (by
          rw [Finset.mem_union, not_or]; exact ⟨L.q_not, fun h => (hκF' q h).2 rfl⟩),
        Finset.prod_union (Finset.disjoint_right.2 fun v hv => (hκF' v hv).1),
        Finset.prod_eq_one fun v hv => co v (hκF' v hv).1 (hκF' v hv).2, Finset.prod_congr rfl cS, cq']
      push_cast
      ring
    rw [hc, ← funext e1, ← funext g1] at key
    exact key
  · by_cases hv : v ∈ L.S
    · rw [φS v hv, ψS v hv]
      obtain ⟨a1, a2, a3, a4⟩ := L.test v hv
      exact ⟨a1.continuous, a2, a3.continuous, a4⟩
    by_cases hvq : v = q
    · subst hvq
      rw [φq, ψq]
      have := prodFn_test (fun w : PlacesOver E v => (iwCoset w.1 (if w = w₀ then (fun i => (j : ℤ) * ν i) else 0)).indicator 1)
        fun w => iwCoset_test _ _
      exact ⟨this.1, this.2, iwCoset_test _ _⟩
    · rw [φo v hv hvq, ψo v hv hvq]
      have := prodFn_test (fun w : PlacesOver E v => h w.1) fun w => h3 w.1
      exact ⟨this.1, this.2, f3 v⟩
  · rw [Finset.mem_insert, Finset.mem_union, not_or, not_or] at hv
    rw [φo v hv.2.1 hv.1, ψo v hv.2.1 hv.1]
    refine ⟨?_, f2 v hv.2.2, co v hv.2.1 hv.1⟩
    rw [← prodFn_unit]
    congr 1
    funext w
    exact h2 w.1 fun hw => hv.2.2 ((hκF v).2 ⟨w.1, hw, under_eq w⟩)
  · refine (?_ : MatchAt σ v (c v) (φ v) (ψ v)) (mE v) (mF v) (hm v).1 (hm v).2.1 (hm v).2.2.1 (hm v).2.2.2
    by_cases hv : v ∈ L.S
    · rw [φS v hv, ψS v hv, cS v hv]
      exact L.mat v hv
    by_cases hvq : v = q
    · subst hvq
      rw [φq, ψq, cq']
      exact HQ w₀ _
    · rw [φo v hv hvq, ψo v hv hvq, co v hv hvq]
      exact LA p (fun w hw => (hp1 w hw).trans hD) v (L.unr v hv) h (f v) h1 h2 (f1 v)
