import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CardToMultisetEqDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.EqZeroOfVecMulTmat

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptx (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  Matrix.vecMul (G.lc p ga n - ∑ s : Fin n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)) (tmat γ)⁻¹
termination_by n
decreasing_by exact s.isLt

def ptw (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  G.lc p ga n - ∑ s ∈ Finset.range n, ∑ b,
    (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s)

theorem ptx_eq (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C)
    (ga : Fin d → PowerSeries C) (n : ℕ) :
    ptx G p γ ga n = Matrix.vecMul (ptw G p γ ga n) (tmat γ)⁻¹ := by
  rw [ptx, ptw, Finset.sum_range]

private theorem lgCurve_zero' (G : LogFGL v d) (a : Fin d) :
    G.lgCurve (fun _ => (0 : PowerSeries C)) a = 0 := by
  have h0 : HasSubst (fun _ : Fin d => (0 : PowerSeries C)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun _ => by simp)
  ext j
  rw [map_zero]
  change MvPowerSeries.coeff (Finsupp.single () j) (subst _ (G.lg a)) = 0
  rw [MvPowerSeries.coeff_subst h0]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · subst he
    rw [coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact he (Finsupp.ext hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs]),
      map_zero, smul_zero]

private theorem lc_at_zero_eq_tangent (G : LogFGL v d) (p : ℕ) (ga : Fin d → PowerSeries C)
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : G.lc p ga 0 = tangent ga := by
  funext a
  have hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - (fun _ => (0 : PowerSeries C)) b := by
    intro b
    show (PowerSeries.X : PowerSeries C) ^ 1 ∣ ga b - 0
    rw [pow_one, sub_zero]
    exact PowerSeries.X_dvd_iff.mpr (h0 b)
  have h1 := lgCurve_sub_dvd (β := fun _ => (0 : PowerSeries C)) G h0 (fun _ => by simp) 1 hk a
  simp only [lgCurve_zero', sub_zero] at h1
  have h2 := PowerSeries.X_pow_dvd_iff.mp h1 1 (by norm_num)
  rw [map_sub, sub_eq_zero] at h2
  show PowerSeries.coeff (p ^ 0) (G.lgCurve ga a) = PowerSeries.coeff 1 (ga a)
  rw [pow_zero, h2]

theorem ptx_rel (G : LogFGL v d) (p : ℕ) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (hdet : v (tmat γ).det = 0) (ga : Fin d → PowerSeries C)
    (n : ℕ) :
    G.lc p ga n = ∑ s ∈ Finset.range (n + 1), ∑ b,
      (ptx G p γ ga s b) ^ (p ^ (n - s)) • G.lc p (γ b) (n - s) := by
  have hlast : ∑ b, (ptx G p γ ga n b) ^ (p ^ (n - n)) • G.lc p (γ b) (n - n) =
      ptw G p γ ga n := by
    simp only [Nat.sub_self, pow_zero, pow_one]
    rw [Finset.sum_congr rfl (fun b _ => by rw [lc_at_zero_eq_tangent G p (γ b) (fun c => (hγ b c).1)]),
      sum_smul_tangent, ptx_eq, vecMul_inv_tmat hdet]
  rw [Finset.sum_range_succ, hlast, ptw]
  abel

def pcurve (G : LogFGL v d) (p : ℕ) (γ : Fin d → Fin d → PowerSeries C) (x : ℕ → Fin d → C) :
    ℕ → Fin d → PowerSeries C
  | 0 => 0
  | s + 1 => G.add (pcurve G p γ x s) (G.sumF fun b => expC (p ^ s) (rescaleCurve (x s b) (γ b)))

private theorem hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha

private theorem constantCoeff_subst_eq_zero_of_constantCoeff_eq_zero {σ : Type} [Finite σ] (a : σ → PowerSeries C)
    (ha : ∀ s, PowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C)
    (hf : constantCoeff f = 0) : PowerSeries.constantCoeff (subst a f) = 0 := by
  have hA : HasSubst a := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds a (fun s => ha s)
  have key : PowerSeries.coeff 0 (subst a f) = 0 := by
    change MvPowerSeries.coeff (Finsupp.single () 0) (subst a f) = 0
    rw [MvPowerSeries.coeff_subst hA]
    apply finsum_eq_zero_of_forall_eq_zero
    intro e
    by_cases he : e = 0
    · subst he
      rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact he (Finsupp.ext hcon)
      have hdvd : (PowerSeries.X : PowerSeries C) ∣ e.prod (fun s n => a s ^ n) := by
        rw [Finsupp.prod]
        exact (dvd_pow (PowerSeries.X_dvd_iff.mpr (ha s)) hs).trans
          (Finset.dvd_prod_of_mem (fun s => a s ^ e s) (Finsupp.mem_support_iff.mpr hs))
      have h0 : PowerSeries.coeff 0 (e.prod (fun s n => a s ^ n)) = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact PowerSeries.X_dvd_iff.mp hdvd
      have h0' : MvPowerSeries.coeff (Finsupp.single () 0) (e.prod (fun s n => a s ^ n)) = 0 := h0
      rw [h0', smul_zero]
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at key

private theorem lgCurve_add' (G : LogFGL v d) (ga gb : Fin d → PowerSeries C)
    (hga : ∀ c, PowerSeries.constantCoeff (ga c) = 0)
    (hgb : ∀ c, PowerSeries.constantCoeff (gb c) = 0) (a : Fin d) :
    G.lgCurve (G.add ga gb) a = G.lgCurve ga a + G.lgCurve gb a := by
  have hE : HasSubst (Sum.elim ga gb) := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun s => by
    cases s with
    | inl c => exact hga c
    | inr c => exact hgb c)
  have hF : HasSubst G.F := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun c => G.F_const c)
  have hL : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun b => by simp)
  have hR : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun b => by simp)
  show subst (fun c => subst (Sum.elim ga gb) (G.F c)) (G.lg a) =
    subst ga (G.lg a) + subst gb (G.lg a)
  rw [← MvPowerSeries.subst_comp_subst_apply hF hE, G.lg_F, MvPowerSeries.subst_add hE,
    MvPowerSeries.subst_comp_subst_apply hL hE, MvPowerSeries.subst_comp_subst_apply hR hE]
  simp only [MvPowerSeries.subst_X hE, Sum.elim_inl, Sum.elim_inr]

private theorem constantCoeff_sumList_and_lgCurve_sumList (G : LogFGL v d) : ∀ l : List (Fin d → PowerSeries C),
    (∀ g ∈ l, ∀ c, PowerSeries.constantCoeff (g c) = 0) →
      (∀ c, PowerSeries.constantCoeff (G.sumList l c) = 0) ∧
        ∀ a, G.lgCurve (G.sumList l) a = (l.map fun g => G.lgCurve g a).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨fun c => by simp [LogFGL.sumList], fun a => ?_⟩
    simp only [LogFGL.sumList, List.map_nil, List.sum_nil]
    exact lgCurve_zero' G a
  | cons g l ih =>
    intro h
    have hg : ∀ c, PowerSeries.constantCoeff (g c) = 0 := h g (by simp)
    obtain ⟨h1, h2⟩ := ih (fun g' hg' => h g' (by simp [hg']))
    refine ⟨fun c => ?_, fun a => ?_⟩
    · simp only [LogFGL.sumList]
      exact constantCoeff_subst_eq_zero_of_constantCoeff_eq_zero _ (fun s => by
        cases s with
        | inl c' => exact hg c'
        | inr c' => exact h1 c') _ (G.F_const c)
    · simp only [LogFGL.sumList]
      rw [lgCurve_add' G _ _ hg h1, h2 a, List.map_cons, List.sum_cons]

private theorem lgCurve_rescaleCurve (G : LogFGL v d) (x : C) (ga : Fin d → PowerSeries C)
    (h0 : ∀ c, PowerSeries.constantCoeff (ga c) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve x ga) a = PowerSeries.rescale x (G.lgCurve ga a) := by
  have hA : HasSubst ga := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun c => h0 c)
  have hB : HasSubst (rescaleCurve x ga) := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds _ (fun c => by
    show PowerSeries.constantCoeff (PowerSeries.rescale x (ga c)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
      one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0 c])
  ext n
  rw [PowerSeries.coeff_rescale]
  change MvPowerSeries.coeff (Finsupp.single () n) (subst (rescaleCurve x ga) (G.lg a)) =
    x ^ n * MvPowerSeries.coeff (Finsupp.single () n) (subst ga (G.lg a))
  rw [MvPowerSeries.coeff_subst hA, MvPowerSeries.coeff_subst hB,
    mul_finsum _ _]
  apply finsum_congr
  intro e
  have hp : e.prod (fun s m => rescaleCurve x ga s ^ m) =
      PowerSeries.rescale x (e.prod (fun s m => ga s ^ m)) := by
    first
    | rw [map_finsuppProd]
    | rw [Finsupp.prod, Finsupp.prod, map_prod]
    simp only [map_pow]
    try rfl
  have hc : PowerSeries.coeff n (PowerSeries.rescale x (e.prod (fun s m => ga s ^ m))) =
      x ^ n * PowerSeries.coeff n (e.prod (fun s m => ga s ^ m)) := by
    rw [PowerSeries.coeff_rescale]
  have hc' : MvPowerSeries.coeff (Finsupp.single () n)
      (PowerSeries.rescale x (e.prod (fun s m => ga s ^ m))) =
      x ^ n * MvPowerSeries.coeff (Finsupp.single () n) (e.prod (fun s m => ga s ^ m)) := hc
  rw [hp, hc', smul_eq_mul, smul_eq_mul]
  ring

private theorem exists_subring_iff_isIntV : ∃ S : Subring C, ∀ x, x ∈ S ↔ IsIntV v x :=
  ⟨{ carrier := {x | 0 ≤ v x}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
       exact add_nonneg ha hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }, fun _ => Iff.rfl⟩

private theorem exists_subring_powerSeries_mem_iff_psIsInt : ∃ T : Subring (PowerSeries C), ∀ f, f ∈ T ↔ PsIsInt v f := by
  obtain ⟨S, hS⟩ := exists_subring_iff_isIntV (v := v)
  refine ⟨{ carrier := {f | PsIsInt v f}
            mul_mem' := fun {f g} hf hg => by
              have hf' : PsIsInt v f := hf
              have hg' : PsIsInt v g := hg
              show PsIsInt v (f * g)
              intro n
              rw [← hS, PowerSeries.coeff_mul]
              exact S.sum_mem fun ij _ => S.mul_mem ((hS _).2 (hf' _)) ((hS _).2 (hg' _))
            one_mem' := by
              show PsIsInt v 1
              intro n
              rw [← hS, PowerSeries.coeff_one]
              split_ifs
              exacts [S.one_mem, S.zero_mem]
            add_mem' := fun {f g} hf hg => by
              have hf' : PsIsInt v f := hf
              have hg' : PsIsInt v g := hg
              show PsIsInt v (f + g)
              intro n
              rw [← hS, map_add]
              exact S.add_mem ((hS _).2 (hf' n)) ((hS _).2 (hg' n))
            zero_mem' := by
              show PsIsInt v 0
              intro n
              rw [← hS, map_zero]
              exact S.zero_mem
            neg_mem' := fun {f} hf => by
              have hf' : PsIsInt v f := hf
              show PsIsInt v (-f)
              intro n
              rw [← hS, map_neg]
              exact S.neg_mem ((hS _).2 (hf' n)) }, fun _ => Iff.rfl⟩

private theorem psIsInt_subst_of_mvIsInt {σ : Type} [Finite σ] (a : σ → PowerSeries C)
    (ha : ∀ s, PowerSeries.constantCoeff (a s) = 0) (hai : ∀ s, PsIsInt v (a s))
    (f : MvPowerSeries σ C) (hf : MvIsInt v f) : PsIsInt v (subst a f) := by
  obtain ⟨S, hS⟩ := exists_subring_iff_isIntV (v := v)
  obtain ⟨T, hT⟩ := exists_subring_powerSeries_mem_iff_psIsInt (v := v)
  have hA : HasSubst a := hasSubst_of_constantCoeff_eq_zero_weighted_sum_bounds a (fun s => ha s)
  intro n
  rw [← hS]
  change MvPowerSeries.coeff (Finsupp.single () n) (subst a f) ∈ S
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_induction (p := fun z => z ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy)
    (fun e => ?_)
  have hprod : e.prod (fun s m => a s ^ m) ∈ T := by
    rw [Finsupp.prod]
    exact T.prod_mem fun s _ => T.pow_mem ((hT _).2 (hai s)) _
  rw [smul_eq_mul]
  exact S.mul_mem ((hS _).2 (hf e)) ((hS _).2 (((hT _).1 hprod) n))

theorem isCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → IsCurve v (pcurve G p γ x n)
  | 0, _ => isCurve_zero
  | n + 1, hx => isCurve_add G (isCurve_pcurve G hp hγ x n fun s hs b => hx s (by omega) b)
      (isCurve_sumF G _ fun b => isCurve_expC (pow_ne_zero _ hp)
        (isCurve_rescale (hx n (by omega) b) (hγ b)))

theorem lgCurve_pcurve (G : LogFGL v d) {p : ℕ} (hp : p ≠ 0) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (x : ℕ → Fin d → C) :
    ∀ n, (∀ s < n, ∀ b, IsIntV v (x s b)) → ∀ a, G.lgCurve (pcurve G p γ x n) a =
      ∑ s ∈ Finset.range n, ∑ b, PowerSeries.expand (p ^ s) (pow_ne_zero _ hp)
        (PowerSeries.rescale (x s b) (G.lgCurve (γ b) a))
  | 0, _, a => by simp [pcurve, lgCurve_zero]
  | n + 1, hx, a => by
      have hx' : ∀ s < n, ∀ b, IsIntV v (x s b) := fun s hs b => hx s (by omega) b
      have hc : ∀ b, IsCurve v (expC (p ^ n) (rescaleCurve (x n b) (γ b))) := fun b =>
        isCurve_expC (pow_ne_zero _ hp) (isCurve_rescale (hx n (by omega) b) (hγ b))
      rw [pcurve, lgCurve_add G (fun b => (isCurve_pcurve G hp hγ x n hx' b).1)
        (fun b => (isCurve_sumF G _ hc b).1), lgCurve_pcurve G hp hγ x n hx' a,
        lgCurve_sumF G _ hc, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lgCurve_expC G (pow_ne_zero _ hp) (fun c => (isCurve_rescale (hx n (by omega) b) (hγ b) c).1),
        lgCurve_rescale G _ (fun c => (hγ b c).1)]

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
