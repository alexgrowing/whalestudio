import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LineDerivListEqIteratedFDeriv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Filter Topology

namespace GlobalTheory

section Formal

variable {σ R : Type*} [CommRing R] [IsAddTorsionFree R]

theorem mvPowerSeries_eq_zero_of_pderiv_mem_span (S : Set (MvPowerSeries σ R))
    (h0 : ∀ F ∈ S, MvPowerSeries.constantCoeff F = 0)
    (hd : ∀ F ∈ S, ∀ i, MvPowerSeries.pderiv R i F ∈ Ideal.span S) : ∀ F ∈ S, F = 0 := by
  classical
  have key : ∀ n : ℕ, ∀ F ∈ Ideal.span S, ∀ m : σ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m F = 0 := by
    intro n
    induction n with
    | zero => intro F _ m hm; omega
    | succ n ih =>
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        intro m hm
        by_cases h : m = 0
        · rw [h, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0 F hF]
        obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
        have hle : Finsupp.single i 1 ≤ m := by
          rw [Finsupp.single_le_iff]; omega
        obtain ⟨m', rfl⟩ := exists_add_of_le hle
        have h1 := ih _ (hd F hF i) m' (by
          rw [map_add, Finsupp.degree_single] at hm; omega)
        rw [MvPowerSeries.coeff_pderiv, add_comm m', mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul,
          smul_eq_zero_iff_right (Nat.succ_ne_zero _)] at h1
        exact h1
      | zero => intro m _; simp
      | add F G _ _ hF hG => intro m hm; rw [map_add, hF m hm, hG m hm, add_zero]
      | smul G F _ hF =>
        intro m hm
        rw [smul_eq_mul, MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [hF p.2 (by rw [← hp, map_add] at hm; omega), mul_zero]
  intro F hF
  ext m
  rw [key _ F (Ideal.subset_span hF) m (Nat.lt_succ_self _), map_zero]

end Formal

section Operator

variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem dirPolyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x =
      iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
        (fun k => u ((Finsupp.toMultiset m).toList.get
          (k.cast (Multiset.length_toList _).symm))) := by
  classical
  simp [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_monomial]

theorem dirPolyDeriv_eq_sum (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support,
      P.coeff m * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x := by
  simp only [dirPolyDeriv_monomial_one]
  rfl

theorem dirPolyDeriv_monomial_eq_lineDerivList {m : σ →₀ ℕ} {l : List σ}
    (hl : (l : Multiset σ) = Finsupp.toMultiset m) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x =
      lineDerivList ℂ (l.map u) F x := by
  rw [dirPolyDeriv_monomial_one, ← lineDerivList_ofFn hF]
  have h1 : (List.ofFn fun k : Fin (Multiset.card (Finsupp.toMultiset m)) =>
      u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))
      = (Finsupp.toMultiset m).toList.map u := by
    apply List.ext_getElem <;> simp
  rw [h1]
  refine lineDerivList_perm hF (List.Perm.map _ ?_)
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hl]

end Operator

section Dir

variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable def taylorDir (u : σ → W) (f : W → ℂ) : MvPowerSeries σ ℂ :=
  fun m => ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0

variable (u : σ → W) {f g : W → ℂ}

theorem coeff_taylorDir (f : W → ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (taylorDir u f) = ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0 := rfl

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in

theorem cast_prod_factorial_ne_zero (m : σ →₀ ℕ) : ((∏ i, (m i).factorial : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (m i).factorial_ne_zero)

theorem dirPolyDeriv_monomial_eq_coeff (f : W → ℂ) (m : σ →₀ ℕ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0 =
      ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorDir u f) := by
  rw [coeff_taylorDir, mul_inv_cancel_left₀ (cast_prod_factorial_ne_zero m)]

theorem dirPolyDeriv_eq_sum_coeff_taylorDir (P : MvPolynomial σ ℂ) (f : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorDir u f) := by
  rw [dirPolyDeriv_eq_sum]
  simp only [dirPolyDeriv_monomial_eq_coeff, mul_assoc]

theorem coeff_taylorDir_eq_lineDerivList (hf : AnalyticAt ℂ f 0) {m : σ →₀ ℕ} {l : List σ}
    (hl : (l : Multiset σ) = Finsupp.toMultiset m) :
    MvPowerSeries.coeff m (taylorDir u f) =
      ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ * lineDerivList ℂ (l.map u) f 0 := by
  rw [coeff_taylorDir, dirPolyDeriv_monomial_eq_lineDerivList hl u hf]

theorem taylorDir_congr (h : f =ᶠ[𝓝 0] g) : taylorDir u f = taylorDir u g := by
  ext m
  rw [coeff_taylorDir, coeff_taylorDir, dirPolyDeriv_monomial_one, dirPolyDeriv_monomial_one,
    (h.iteratedFDeriv ℂ _).eq_of_nhds]

@[simp] theorem constantCoeff_taylorDir (f : W → ℂ) :
    MvPowerSeries.constantCoeff (taylorDir u f) = f 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorDir,
    dirPolyDeriv_monomial_one]
  have : ∀ (n : ℕ) (_ : n = 0) (v : Fin n → W), iteratedFDeriv ℂ n f 0 v = f 0 := by
    rintro n rfl v; simp
  rw [this _ (by simp)]
  simp

theorem taylorDir_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f + g) = taylorDir u f + taylorDir u g := by
  ext m
  rw [map_add, coeff_taylorDir_eq_lineDerivList u (hf.add hg) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hg (Multiset.coe_toList _), ← mul_add,
    ← lineDerivList_add hf hg]
  rfl

theorem taylorDir_smul (c : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylorDir u (c • f) = c • taylorDir u f := by
  ext m
  have h := congrFun (lineDerivList_const_smul ((Finsupp.toMultiset m).toList.map u) c f) 0
  rw [map_smul, coeff_taylorDir_eq_lineDerivList u hf.const_smul (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (Multiset.coe_toList _)]
  change _ * lineDerivList ℂ _ (fun z => c • f z) 0 = _
  rw [h, smul_eq_mul, smul_eq_mul]
  ring

theorem analyticAt_fderiv_apply {x : W} (hf : AnalyticAt ℂ f x) (v : W) :
    AnalyticAt ℂ (fun z => fderiv ℂ f z v) x :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv

theorem taylorDir_fderiv (hf : AnalyticAt ℂ f 0) (i : σ) :
    taylorDir u (fun z => fderiv ℂ f z (u i)) = MvPowerSeries.pderiv ℂ i (taylorDir u f) := by
  classical
  have h1 : (fun z => fderiv ℂ f z (u i)) =ᶠ[𝓝 0] lineDerivList ℂ [u i] f := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    exact hz.differentiableAt.lineDeriv_eq_fderiv.symm
  ext m
  rw [taylorDir_congr u h1, MvPowerSeries.coeff_pderiv,
    coeff_taylorDir_eq_lineDerivList u (analyticAt_lineDerivList hf _) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (l := (Finsupp.toMultiset m).toList ++ [i])
      (by rw [← Multiset.coe_add]; simp), List.map_append, lineDerivList_append]
  have h2 : (∏ j, ((m + Finsupp.single i 1 : σ →₀ ℕ) j).factorial : ℕ) = (m i + 1) * ∏ j, (m j).factorial := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => (m j).factorial) (Finset.mem_univ i), ← mul_assoc]
    congr 1
    · simp [Nat.factorial_succ]
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
  have h3 := cast_prod_factorial_ne_zero m
  have h4 : ((m i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
  rw [h2, Nat.cast_mul, Nat.cast_succ, List.map_singleton]
  field_simp

@[simp] theorem taylorDir_const (c : ℂ) : taylorDir u (fun _ => c) = MvPowerSeries.C c := by
  have h0 : taylorDir u (fun _ => (0 : ℂ)) = 0 := by
    have := taylorDir_smul u 0 (analyticAt_const (v := (0 : ℂ)) (x := (0 : W)))
    rw [zero_smul, zero_smul] at this
    exact this
  refine MvPowerSeries.pderiv.ext (fun i => ?_) (by simp)
  rw [← taylorDir_fderiv u analyticAt_const]
  simp [h0]

@[simp] theorem taylorDir_zero : taylorDir u (0 : W → ℂ) = 0 :=
  (taylorDir_const u 0).trans (map_zero _)

@[simp] theorem taylorDir_one : taylorDir u (1 : W → ℂ) = 1 :=
  (taylorDir_const u 1).trans (map_one _)

theorem taylorDir_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f * g) = taylorDir u f * taylorDir u g := by
  rw [← sub_eq_zero]
  refine mvPowerSeries_eq_zero_of_pderiv_mem_span
    {F | ∃ f g : W → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      F = taylorDir u (f * g) - taylorDir u f * taylorDir u g} ?_ ?_ _ ⟨f, g, hf, hg, rfl⟩
  · rintro _ ⟨f, g, -, -, rfl⟩
    simp
  · rintro _ ⟨f, g, hf, hg, rfl⟩ i
    have hf' := analyticAt_fderiv_apply hf (u i)
    have hg' := analyticAt_fderiv_apply hg (u i)
    have h1 : (fun z => fderiv ℂ (f * g) z (u i)) =ᶠ[𝓝 0]
        f * (fun z => fderiv ℂ g z (u i)) + (fun z => fderiv ℂ f z (u i)) * g := by
      filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hz hz'
      rw [fderiv_mul hz.differentiableAt hz'.differentiableAt]
      simp [mul_comm]
    rw [map_sub, ← taylorDir_fderiv u (hf.mul hg), taylorDir_congr u h1,
      taylorDir_add u (hf.mul hg') (hf'.mul hg), Derivation.leibniz, ← taylorDir_fderiv u hf,
      ← taylorDir_fderiv u hg, smul_eq_mul, smul_eq_mul, add_sub_add_comm,
      mul_comm (taylorDir u g)]
    exact Ideal.add_mem _ (Ideal.subset_span ⟨_, _, hf, hg', rfl⟩)
      (Ideal.subset_span ⟨_, _, hf', hg, rfl⟩)

theorem taylorDir_clm (ℓ : W →L[ℂ] ℂ) :
    taylorDir u ℓ = ∑ i, ℓ (u i) • (MvPowerSeries.X i : MvPowerSeries σ ℂ) := by
  classical
  refine MvPowerSeries.pderiv.ext (fun i => ?_) (by simp)
  rw [← taylorDir_fderiv u (ℓ.analyticAt 0)]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

theorem taylorDir_comp_clm {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (L : W' →L[ℂ] W) (v : σ → W') (hf : AnalyticAt ℂ f 0) :
    taylorDir v (fun z => f (L z)) = taylorDir (fun i => L (v i)) f := by
  ext m
  have hc : AnalyticAt ℂ (fun z => f (L z)) 0 := hf.comp_of_eq (L.analyticAt 0) (map_zero L)
  have h := congrFun (lineDerivList_comp_linearMap (L : W' →ₗ[ℂ] W)
    ((Finsupp.toMultiset m).toList.map v) f) 0
  rw [map_zero, List.map_map] at h
  rw [coeff_taylorDir_eq_lineDerivList v hc (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ hf (Multiset.coe_toList _)]
  exact congrArg _ h

theorem coeff_taylorDir_eq_zero_iff (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    (∀ m : σ →₀ ℕ, m.degree = n → MvPowerSeries.coeff m (taylorDir u f) = 0) ↔
      iteratedFDeriv ℂ n f 0 = 0 := by
  classical
  have hdeg : ∀ m : σ →₀ ℕ, Multiset.card (Finsupp.toMultiset m) = m.degree := fun m => by
    rw [Finsupp.card_toMultiset]; rfl
  constructor
  · intro h
    refine ContinuousMultilinearMap.toMultilinearMap_injective
      (MultilinearMap.ext_of_span_eq_top (g := fun _ => u) (fun _ => hu) fun j => ?_)
    have hl : ((List.ofFn j : List σ) : Multiset σ) =
        Finsupp.toMultiset (Multiset.toFinsupp (List.ofFn j : List σ)) := by simp
    have h1 := h (Multiset.toFinsupp (List.ofFn j : List σ)) (by rw [← hdeg, ← hl]; simp)
    rw [coeff_taylorDir_eq_lineDerivList u hf hl, List.map_ofFn, lineDerivList_ofFn hf,
      mul_eq_zero_iff_left (inv_ne_zero (cast_prod_factorial_ne_zero _))] at h1
    exact h1
  · rintro h m rfl
    rw [← hdeg] at h
    rw [coeff_taylorDir, dirPolyDeriv_monomial_one, h]
    simp

theorem taylorDir_eq_zero_iff (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) : taylorDir u f = 0 ↔ f =ᶠ[𝓝 0] 0 := by
  refine ⟨fun h => ?_, fun h => by rw [taylorDir_congr u h, taylorDir_zero]⟩
  have h1 : ∀ n, iteratedFDeriv ℂ n f 0 = 0 := fun n =>
    (coeff_taylorDir_eq_zero_iff u hu hf n).1 fun m _ => by rw [h, map_zero]
  obtain ⟨p, r, hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds (0 : W) hp.r_pos] with y hy
  have h2 := hp.hasSum_iteratedFDeriv hy
  simp only [h1, ContinuousMultilinearMap.zero_apply, smul_zero, zero_add] at h2
  exact h2.unique hasSum_zero

variable (W) in

def analyticAtZero : Subalgebra ℂ (W → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' _ := analyticAt_const

omit [Fintype σ] in

@[simp] theorem mem_analyticAtZero : f ∈ analyticAtZero W ↔ AnalyticAt ℂ f 0 := Iff.rfl

noncomputable def taylorDirAlgHom : analyticAtZero W →ₐ[ℂ] MvPowerSeries σ ℂ where
  toFun f := taylorDir u f
  map_one' := taylorDir_one u
  map_mul' f g := taylorDir_mul u f.2 g.2
  map_zero' := taylorDir_zero u
  map_add' f g := taylorDir_add u f.2 g.2
  commutes' c := taylorDir_const u c

@[simp] theorem taylorDirAlgHom_apply (f : analyticAtZero W) :
    taylorDirAlgHom u f = taylorDir u f := rfl

theorem taylorDir_neg (hf : AnalyticAt ℂ f 0) : taylorDir u (-f) = -taylorDir u f := by
  rw [← neg_one_smul ℂ f, taylorDir_smul u _ hf, neg_one_smul]

theorem taylorDir_sub (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f - g) = taylorDir u f - taylorDir u g := by
  rw [sub_eq_add_neg, taylorDir_add u hf hg.neg, taylorDir_neg u hg, sub_eq_add_neg]

theorem taylorDir_sum {κ : Type*} (s : Finset κ) {F : κ → W → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylorDir u (fun z => ∑ k ∈ s, F k z) = ∑ k ∈ s, taylorDir u (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt ℂ (F k) 0 := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [← ih hs]
    exact taylorDir_add u (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ hs)

theorem taylorDir_prod {κ : Type*} (s : Finset κ) {F : κ → W → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylorDir u (fun z => ∏ k ∈ s, F k z) = ∏ k ∈ s, taylorDir u (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt ℂ (F k) 0 := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.prod_insert hj]
    rw [← ih hs]
    exact taylorDir_mul u (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_prod _ hs)

theorem taylorDir_eval {κ : Type*} {φ : κ → W → ℂ} (hφ : ∀ k, AnalyticAt ℂ (φ k) 0)
    (P : MvPolynomial κ ℂ) :
    taylorDir u (fun z => MvPolynomial.eval (fun k => φ k z) P) =
      MvPolynomial.aeval (fun k => taylorDir u (φ k)) P := by
  have h := MvPolynomial.comp_aeval_apply (f := fun k => (⟨φ k, hφ k⟩ : analyticAtZero W))
    (taylorDirAlgHom u) P
  simp only [taylorDirAlgHom_apply] at h
  rw [← h]
  congr 1
  funext z
  exact (MvPolynomial.comp_aeval_apply (f := fun k => (⟨φ k, hφ k⟩ : analyticAtZero W))
    ((Pi.evalAlgHom ℂ (fun _ : W => ℂ) z).comp (analyticAtZero W).val) P).symm

theorem taylorDir_eq_iff (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u f = taylorDir u g ↔ f =ᶠ[𝓝 0] g := by
  rw [← sub_eq_zero, ← taylorDir_sub u hf hg, taylorDir_eq_zero_iff u hu (hf.sub hg),
    ← Filter.eventuallyEq_iff_sub]

theorem taylorDir_fderiv_sum (hf : AnalyticAt ℂ f 0) (a : σ → ℂ) :
    taylorDir u (fun z => fderiv ℂ f z (∑ i, a i • u i)) =
      ∑ i, a i • MvPowerSeries.pderiv ℂ i (taylorDir u f) := by
  simp only [map_sum, map_smul]
  rw [taylorDir_sum u _ (F := fun i z => a i • fderiv ℂ f z (u i))
    fun i _ => (analyticAt_fderiv_apply hf (u i)).const_smul (c := a i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← taylorDir_fderiv u hf, ← taylorDir_smul u _ (analyticAt_fderiv_apply hf (u i))]
  rfl

end Dir

section Coord

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def taylor (f : (σ → ℂ) → ℂ) : MvPowerSeries σ ℂ :=
  taylorDir (fun i => (Pi.single i 1 : σ → ℂ)) f

variable {f g : (σ → ℂ) → ℂ}

theorem taylor_eq_taylorDir (f : (σ → ℂ) → ℂ) :
    taylor f = taylorDir (fun i => (Pi.single i 1 : σ → ℂ)) f := rfl

theorem coeff_taylor (f : (σ → ℂ) → ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (taylor f) = ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1)
        (fun i => (Pi.single i 1 : σ → ℂ)) f 0 := rfl

theorem dirPolyDeriv_eq_sum_coeff_taylor (P : MvPolynomial σ ℂ) (f : (σ → ℂ) → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => (Pi.single i 1 : σ → ℂ)) f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylor f) :=
  dirPolyDeriv_eq_sum_coeff_taylorDir _ P f

@[simp] theorem constantCoeff_taylor (f : (σ → ℂ) → ℂ) :
    MvPowerSeries.constantCoeff (taylor f) = f 0 := constantCoeff_taylorDir _ f

theorem taylor_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (f + g) = taylor f + taylor g := taylorDir_add _ hf hg

@[simp] theorem taylor_const (c : ℂ) :
    taylor (fun _ : σ → ℂ => c) = MvPowerSeries.C c := taylorDir_const _ c

@[simp] theorem taylor_zero : taylor (0 : (σ → ℂ) → ℂ) = 0 := taylorDir_zero _

@[simp] theorem taylor_one : taylor (1 : (σ → ℂ) → ℂ) = 1 := taylorDir_one _

theorem taylor_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor (f * g) = taylor f * taylor g := taylorDir_mul _ hf hg

theorem taylor_sum {κ : Type*} (s : Finset κ) {F : κ → (σ → ℂ) → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylor (fun z => ∑ k ∈ s, F k z) = ∑ k ∈ s, taylor (F k) := taylorDir_sum _ s hF

theorem taylor_fderiv (hf : AnalyticAt ℂ f 0) (i : σ) :
    taylor (fun z => fderiv ℂ f z (Pi.single i 1)) = MvPowerSeries.pderiv ℂ i (taylor f) :=
  taylorDir_fderiv (fun i => (Pi.single i 1 : σ → ℂ)) hf i

theorem taylor_clm (ℓ : (σ → ℂ) →L[ℂ] ℂ) :
    taylor ℓ = ∑ i, ℓ (Pi.single i 1) • (MvPowerSeries.X i : MvPowerSeries σ ℂ) :=
  taylorDir_clm _ ℓ

@[simp] theorem taylor_coord (i : σ) : taylor (fun z : σ → ℂ => z i) = MvPowerSeries.X i := by
  have h := taylor_clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i)
  simp only [ContinuousLinearMap.proj_apply, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h

theorem span_range_single_one :
    Submodule.span ℂ (Set.range fun i : σ => (Pi.single i 1 : σ → ℂ)) = ⊤ := by
  have h := (Pi.basisFun ℂ σ).span_eq
  rwa [show ⇑(Pi.basisFun ℂ σ) = fun i : σ => (Pi.single i 1 : σ → ℂ) from
    funext fun i => Pi.basisFun_apply ℂ σ i] at h

theorem taylor_eq_iff (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor f = taylor g ↔ f =ᶠ[𝓝 0] g :=
  taylorDir_eq_iff _ span_range_single_one hf hg

noncomputable def taylorAlgHom : analyticAtZero (σ → ℂ) →ₐ[ℂ] MvPowerSeries σ ℂ :=
  taylorDirAlgHom fun i => (Pi.single i 1 : σ → ℂ)

@[simp] theorem taylorAlgHom_apply (f : analyticAtZero (σ → ℂ)) : taylorAlgHom f = taylor f := rfl

theorem taylor_eval_comp {κ : Type*} {φ : κ → (σ → ℂ) → ℂ} (hφ : ∀ k, AnalyticAt ℂ (φ k) 0)
    (P : MvPolynomial κ ℂ) :
    taylor (fun z => MvPolynomial.eval (fun k => φ k z) P) =
      MvPolynomial.aeval (fun k => taylor (φ k)) P := taylorDir_eval _ hφ P

theorem taylor_eval (P : MvPolynomial σ ℂ) :
    taylor (fun z : σ → ℂ => MvPolynomial.eval z P) = (P : MvPowerSeries σ ℂ) := by
  have h := taylor_eval_comp (φ := fun (k : σ) (z : σ → ℂ) => z k)
    (fun k => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) k).analyticAt 0) P
  simp only [taylor_coord] at h
  refine h.trans ?_
  have : MvPolynomial.aeval (fun k : σ => (MvPowerSeries.X k : MvPowerSeries σ ℂ))
      = MvPolynomial.coeToMvPowerSeries.algHom (R := ℂ) ℂ := by
    ext1 k; simp
  rw [this]
  simp

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem taylor_comp_clm (L : (σ → ℂ) →L[ℂ] W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylor (fun z => F (L z)) = taylorDir (fun i => L (Pi.single i 1)) F :=
  taylorDir_comp_clm L _ hF

theorem taylorDir_eq_taylor (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylorDir u F = taylor fun z : σ → ℂ => F (∑ i, z i • u i) := by
  have h := taylor_comp_clm (LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ u)) hF
  simp only [LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply_single,
    one_smul] at h
  rw [← h]
  rfl

end Coord

section Examples

example : taylor (fun z : Fin 2 → ℂ => z 0 * z 1 + 3) =
    MvPowerSeries.X 0 * MvPowerSeries.X 1 + MvPowerSeries.C 3 := by
  have h := taylor_eval (MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.C 3 :
    MvPolynomial (Fin 2) ℂ)
  simpa using h

example : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial (Finsupp.single 0 2) 1)
    (fun i : Fin 1 => (Pi.single i 1 : Fin 1 → ℂ)) (fun z => z 0 ^ 2) 0 = 2 := by
  have h := taylor_eval (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℂ)
  simp only [map_pow, MvPolynomial.eval_X] at h
  rw [dirPolyDeriv_monomial_eq_coeff, ← taylor_eq_taylorDir, h, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_X_pow]
  simp

example : MvPowerSeries.pderiv ℂ 0 (taylor fun z : Fin 1 → ℂ => Complex.exp (z 0)) =
    taylor fun z : Fin 1 → ℂ => Complex.exp (z 0) := by
  have hd : ∀ z : Fin 1 → ℂ, HasFDerivAt (fun z : Fin 1 → ℂ => Complex.exp (z 0))
      (Complex.exp (z 0) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) z :=
    fun z => (hasFDerivAt_apply 0 z).cexp
  rw [← taylor_fderiv (SCV.analyticAt_iff_eventually_differentiableAt.2
    (Eventually.of_forall fun z => (hd z).differentiableAt))]
  simp [fun z => (hd z).fderiv]

end Examples

end GlobalTheory
