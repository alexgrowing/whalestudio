import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.TaylorComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology

section Chain

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem iter_comp_clm {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : W →L[ℂ] V) (i : ℕ) :
    iteratedFDeriv ℂ i (f ∘ A) 0 = (iteratedFDeriv ℂ i f 0).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := ω) le_rfl (fun _ => rfl)
  obtain ⟨U, hUu, hUo, h0U⟩ := mem_nhds_iff.mp hu
  have hfU : ContDiffOn ℂ ω f U := hfu.mono hUu
  have hAo : IsOpen (A ⁻¹' U) := hUo.preimage A.continuous
  have h0A : (0 : W) ∈ A ⁻¹' U := by simpa using h0U
  have key := A.iteratedFDerivWithin_comp_right hfU hUo.uniqueDiffOn hAo.uniqueDiffOn
    (x := 0) (by simpa using h0U) (i := i) le_top
  rw [map_zero] at key
  rw [iteratedFDerivWithin_of_isOpen i hAo h0A, iteratedFDerivWithin_of_isOpen i hUo h0U] at key
  exact key

theorem mD_comp {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : W →L[ℂ] V) (S : Multiset W) :
    mD (f ∘ A) 0 S = mD f 0 (S.map A) := by
  have gen : ∀ (n m : ℕ) (h : n = m) (v : Fin n → V) (v' : Fin m → V), (∀ j, v j = v' (Fin.cast h j)) →
      iteratedFDeriv ℂ n f 0 v = iteratedFDeriv ℂ m f 0 v' := by
    intro n m h v v' hv
    subst h
    congr 1
    funext j
    exact hv j
  have hl : ∀ l : List W, lD (f ∘ A) 0 l = lD f 0 (l.map A) := by
    intro l
    unfold lD
    rw [iter_comp_clm hf A]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    refine gen _ _ (by simp) _ _ (fun j => ?_)
    simp [List.get_eq_getElem]
  have hS : S.map A = ((S.toList.map A : List V) : Multiset V) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  show lD (f ∘ A) 0 S.toList = _
  rw [hl, hS, mD_coe hf]

end Chain

section Uniq

variable {σ : Type}

theorem coeff_foldr (l : List σ) (m : σ →₀ ℕ) : ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPowerSeries σ ℂ,
    coeff m (l.foldr (fun q G => pderiv ℂ q G) F) = c * coeff (m + (l.map fun q => Finsupp.single q 1).sum) F := by
  induction l generalizing m with
  | nil => exact ⟨1, one_ne_zero, fun F => by simp⟩
  | cons q l ih =>
    obtain ⟨c, hc, hF⟩ := ih (m + Finsupp.single q 1)
    refine ⟨c * ((m q : ℂ) + 1), mul_ne_zero hc (Nat.cast_add_one_ne_zero _), fun F => ?_⟩
    simp only [List.foldr_cons]
    rw [MvPowerSeries.coeff_pderiv, hF, List.map_cons, List.sum_cons, add_assoc]
    ring

theorem sum_single_toList (k : σ →₀ ℕ) :
    ((Finsupp.toMultiset k).toList.map fun q => Finsupp.single q 1).sum = k := by
  classical
  have h : ∀ t : Multiset σ, (t.map fun q => Finsupp.single q 1).sum = Multiset.toFinsupp t := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
  first
    | (rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList, h, Finsupp.toMultiset_toFinsupp])
    | (have h2 := h (Finsupp.toMultiset k)
       rw [Finsupp.toMultiset_toFinsupp] at h2
       rw [← h2, ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList])

theorem eq_of_cc (F G : MvPowerSeries σ ℂ)
    (h : ∀ l : List σ, constantCoeff (l.foldr (fun q H => pderiv ℂ q H) F) =
      constantCoeff (l.foldr (fun q H => pderiv ℂ q H) G)) : F = G := by
  ext m
  obtain ⟨c, hc, hcF⟩ := coeff_foldr (Finsupp.toMultiset m).toList m
  have h1 := h (Finsupp.toMultiset m).toList
  obtain ⟨c0, hc0, h0⟩ := coeff_foldr (Finsupp.toMultiset m).toList 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    h0, h0, zero_add, sum_single_toList] at h1
  exact mul_left_cancel₀ hc0 h1

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def IsTayF (Θ : W → ℂ) (w : σ → W) (F : MvPowerSeries σ ℂ) : Prop :=
  ∀ l : List σ, constantCoeff (l.foldr (fun q H => pderiv ℂ q H) F) = mD Θ 0 ((l.map w : List W) : Multiset W)

theorem IsTayF.eq {Θ : W → ℂ} {w : σ → W} {F G : MvPowerSeries σ ℂ} (hF : IsTayF Θ w F)
    (hG : IsTayF Θ w G) : F = G := eq_of_cc F G fun l => (hF l).trans (hG l).symm

theorem isTayF_family (Θ : W → ℂ) (w : σ → W) (Φ : Multiset W → MvPowerSeries σ ℂ)
    (hd : ∀ q s, pderiv ℂ q (Φ s) = Φ (w q ::ₘ s)) (hc : ∀ s, constantCoeff (Φ s) = mD Θ 0 s) :
    IsTayF Θ w (Φ 0) := by
  have key : ∀ l : List σ, l.foldr (fun q H => pderiv ℂ q H) (Φ 0) = Φ ((l.map w : List W) : Multiset W) := by
    intro l
    induction l with
    | nil => rfl
    | cons q l ih => simp only [List.foldr_cons, ih, hd, List.map_cons, Multiset.cons_coe]
  intro l
  rw [key, hc]

theorem isTayF_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ} (hf : ContDiffAt ℂ ω f 0)
    (A : W →L[ℂ] V) {w : σ → W} {v : σ → V} (hv : ∀ q, A (w q) = v q) {F : MvPowerSeries σ ℂ}
    (hF : IsTayF f v F) : IsTayF (f ∘ A) w F := by
  intro l
  have hAw : (⇑A ∘ w) = v := funext hv
  rw [hF l, mD_comp hf A, Multiset.map_coe, List.map_map, hAw]

end Uniq

section Fam

variable {g : ℕ}

theorem isTayF_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    IsTayF θ (fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ)) (tay θ 0) := by
  have hc : ∀ (s : Multiset (Fin g → ℂ)) (k : Fin 1 × Fin g →₀ ℕ),
      coeff k (tay θ s) = mD θ 0 (dirs k + s) / fct k := fun _ _ => rfl
  have hd : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      dirs (k + Finsupp.single q 1) = (Pi.single q.2 1 : Fin g → ℂ) ::ₘ dirs k := by
    intro k q
    unfold dirs
    first
      | (rw [map_add, Finsupp.toMultiset_single, Multiset.map_add, one_nsmul, Multiset.map_singleton, add_comm,
          Multiset.singleton_add])
      | (simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_comm, Multiset.singleton_add])
      | (simp [map_add, Finsupp.toMultiset_single]; rw [add_comm, Multiset.singleton_add])
  have hf : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      fct (k + Finsupp.single q 1) = fct k * ((k q : ℂ) + 1) := by
    intro k q
    have h : ∀ p, (((k + Finsupp.single q 1 : Fin 1 × Fin g →₀ ℕ) p).factorial : ℂ) =
        ((k p).factorial : ℂ) * (if p = q then ((k q : ℂ) + 1) else 1) := by
      intro p
      by_cases hp : p = q
      · subst hp
        rw [if_pos rfl, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hp, Finsupp.add_apply, mul_one]
        simp [Finsupp.single_apply, Ne.symm hp]
    unfold fct
    rw [Finset.prod_congr rfl (fun p _ => h p), Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hf0 : ∀ k : Fin 1 × Fin g →₀ ℕ, fct k ≠ 0 := by
    intro k
    unfold fct
    exact Finset.prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast Nat.factorial_ne_zero _
  refine isTayF_family θ _ (tay θ) (fun q s => ?_) (fun s => ?_)
  · ext k
    have h1 : ((k q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    have h2 := hf0 k
    beta_reduce
    rw [MvPowerSeries.coeff_pderiv, hc, hc, hd, hf, Multiset.cons_add, ← Multiset.add_cons]
    field_simp
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
    simp [dirs, fct]

variable {n : ℕ}

def tayNs (Θ : (Fin n × Fin g → ℂ) → ℂ) (s : Multiset (Fin n × Fin g → ℂ)) : MvPowerSeries (Fin n × Fin g) ℂ :=
  fun k => mD Θ 0 (dirsN k + s) / fctN k

theorem cc_subst {σ τ : Type} [Fintype σ] {L : σ → MvPowerSeries τ ℂ} (hL0 : ∀ p, constantCoeff (L p) = 0)
    (F : MvPowerSeries σ ℂ) : constantCoeff (subst L F) = constantCoeff F := by
  classical
  have hL : MvPowerSeries.HasSubst L := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hL, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro e he
    obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact he (Finsupp.ext hn)
    have hz : constantCoeff (e.prod fun s n => L s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hp)
      rw [map_pow, hL0, zero_pow hp]
    rw [hz, smul_zero]

private theorem pderiv_tay_eq_tay_cons_single (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) (q : Fin 1 × Fin g) :
    pderiv ℂ q (tay θ s) = tay θ ((Pi.single q.2 1 : Fin g → ℂ) ::ₘ s) := by
  have hc : ∀ (s : Multiset (Fin g → ℂ)) (k : Fin 1 × Fin g →₀ ℕ),
      coeff k (tay θ s) = mD θ 0 (dirs k + s) / fct k := fun _ _ => rfl
  have hd : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      dirs (k + Finsupp.single q 1) = (Pi.single q.2 1 : Fin g → ℂ) ::ₘ dirs k := by
    intro k q
    unfold dirs
    first
      | (rw [map_add, Finsupp.toMultiset_single, Multiset.map_add, one_nsmul, Multiset.map_singleton, add_comm,
          Multiset.singleton_add])
      | (simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_comm, Multiset.singleton_add])
      | (simp [map_add, Finsupp.toMultiset_single]; rw [add_comm, Multiset.singleton_add])
  have hf : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      fct (k + Finsupp.single q 1) = fct k * ((k q : ℂ) + 1) := by
    intro k q
    have h : ∀ p, (((k + Finsupp.single q 1 : Fin 1 × Fin g →₀ ℕ) p).factorial : ℂ) =
        ((k p).factorial : ℂ) * (if p = q then ((k q : ℂ) + 1) else 1) := by
      intro p
      by_cases hp : p = q
      · subst hp
        rw [if_pos rfl, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hp, Finsupp.add_apply, mul_one]
        simp [Finsupp.single_apply, Ne.symm hp]
    unfold fct
    rw [Finset.prod_congr rfl (fun p _ => h p), Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hf0 : ∀ k : Fin 1 × Fin g →₀ ℕ, fct k ≠ 0 := by
    intro k
    unfold fct
    exact Finset.prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast Nat.factorial_ne_zero _
  ext k
  have h1 : ((k q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  have h2 := hf0 k
  rw [MvPowerSeries.coeff_pderiv, hc, hc, hd, hf, Multiset.cons_add, ← Multiset.add_cons]
  field_simp

theorem isTayF_subst {τ : Type} [Fintype τ] (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0)
    (L : Fin 1 × Fin g → MvPowerSeries τ ℂ) (a : Fin 1 × Fin g → τ → ℂ) (hL0 : ∀ p, constantCoeff (L p) = 0)
    (hLd : ∀ p q, pderiv ℂ q (L p) = C (a p q)) :
    IsTayF f (fun q => ∑ p, a p q • (Pi.single p.2 1 : Fin g → ℂ)) (subst L (tay f 0)) := by
  have hL : MvPowerSeries.HasSubst L := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
  have hcf : ∀ (s : Multiset (Fin g → ℂ)) (k : Fin 1 × Fin g →₀ ℕ),
      coeff k (tay f s) = mD f 0 (dirs k + s) / fct k := fun _ _ => rfl
  have lin : ∀ (c : Fin 1 × Fin g → ℂ) (T : Multiset (Fin g → ℂ)),
      mD f 0 ((∑ p, c p • (Pi.single p.2 1 : Fin g → ℂ)) ::ₘ T) =
        ∑ p, c p * mD f 0 ((Pi.single p.2 1 : Fin g → ℂ) ::ₘ T) := by
    intro c T
    simp only [mD_cons hf, map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine isTayF_family f _ (fun s => subst L (tay f s)) (fun q s => ?_) (fun s => ?_)
  · beta_reduce
    have htay : tay f ((∑ p, a p q • (Pi.single p.2 1 : Fin g → ℂ)) ::ₘ s) =
        ∑ p, a p q • tay f ((Pi.single p.2 1 : Fin g → ℂ) ::ₘ s) := by
      ext k
      simp only [map_sum, map_smul, hcf, smul_eq_mul, Multiset.add_cons, lin, Finset.sum_div, mul_div_assoc]
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hL0]
    simp only [hLd]
    rw [htay, ← MvPowerSeries.coe_substAlgHom hL, map_sum]
    simp only [map_smul]
    rw [MvPowerSeries.coe_substAlgHom hL]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [pderiv_tay_eq_tay_cons_single, MvPowerSeries.smul_eq_C_mul, mul_comm]
  · beta_reduce
    rw [cc_subst hL0, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcf]
    simp [dirs, fct]

end Fam

section Main

variable {g : ℕ}

def diagCLM (c : Fin g → ℂ) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun i => c i • ContinuousLinearMap.proj i

theorem diagCLM_apply (c z : Fin g → ℂ) : diagCLM c z = fun i => c i * z i := by
  first
    | rfl
    | (funext i; simp [diagCLM])

def addCLM (g : ℕ) : (Fin 2 × Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 × Fin g => ℂ) ((0 : Fin 2), i) +
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 × Fin g => ℂ) ((1 : Fin 2), i)

theorem partA (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0) (c : Fin g → ℂ) :
    tay (fun z => f fun i => c i * z i) 0 = subst (fun p : Fin 1 × Fin g => C (c p.2) * X p) (tay f 0) := by
  have e : (fun z : Fin g → ℂ => f fun i => c i * z i) = f ∘ diagCLM c := by
    funext z
    simp only [Function.comp, diagCLM_apply]
  have hA : ContDiffAt ℂ ω (f ∘ diagCLM c) 0 :=
    ContDiffAt.comp (0 : Fin g → ℂ) (by rw [map_zero]; exact hf) (diagCLM c).contDiff.contDiffAt
  have h1 := isTayF_tay hA
  rw [← e] at h1
  apply IsTayF.eq h1
  have h2 := isTayF_subst f hf (fun p : Fin 1 × Fin g => C (c p.2) * X p)
    (fun p q => if p = q then c p.2 else 0) (fun p => by simp) (fun p q => by
      rw [← MvPowerSeries.smul_eq_C_mul]
      first
        | rw [Derivation.map_smul, MvPowerSeries.pderiv_X]
        | rw [LinearMap.map_smul_of_tower, MvPowerSeries.pderiv_X]
      by_cases h : p = q
      · subst h
        simp [MvPowerSeries.smul_eq_C_mul]
      · simp [h, Pi.single_apply, Ne.symm h])
  have hv : ∀ q : Fin 1 × Fin g, diagCLM c (Pi.single q.2 1) =
      ∑ p : Fin 1 × Fin g, (if p = q then c p.2 else 0) • (Pi.single p.2 1 : Fin g → ℂ) := by
    intro q
    rw [diagCLM_apply]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    funext i
    by_cases h : i = q.2 <;> simp [Pi.single_apply, h]
  have h3 := isTayF_comp hf (diagCLM c) (w := fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ)) hv h2
  rw [← e] at h3
  exact h3

end Main

end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
