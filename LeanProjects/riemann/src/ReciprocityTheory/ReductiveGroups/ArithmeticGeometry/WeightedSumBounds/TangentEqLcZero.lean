import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def intRing (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {x y} hx hy := by
    show 0 ≤ v (x * y); rw [v.map_mul]; exact add_nonneg hx hy
  one_mem' := by show 0 ≤ v 1; rw [v.map_one]
  add_mem' {x y} hx hy := le_trans (le_min hx hy) (v.map_add x y)
  zero_mem' := by show 0 ≤ v 0; rw [v.map_zero]; exact le_top
  neg_mem' {x} hx := by show 0 ≤ v (-x); rw [v.map_neg]; exact hx

theorem mem_intRing {v : AddValuation C (WithTop ℝ)} {x : C} :
    x ∈ intRing v ↔ IsIntV v x := Iff.rfl

private theorem hs_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact hasSubst_of_constantCoeff_zero ha0
  | exact HasSubst.of_constantCoeff_zero' ha0
  | exact hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)

theorem mvIsInt_subst {σ τ : Type} [Finite σ] (v : AddValuation C (WithTop ℝ))
    {f : MvPowerSeries σ C} (hf : MvIsInt v f) {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvIsInt v (a s)) (ha0 : ∀ s, constantCoeff (a s) = 0) :
    MvIsInt v (subst a f) := by
  classical
  have hS : HasSubst a := hs_lemma_2 ha0
  have hmul : ∀ p q : MvPowerSeries τ C, MvIsInt v p → MvIsInt v q → MvIsInt v (p * q) := by
    intro p q hp hq e
    rw [coeff_mul]
    exact mem_intRing.mp (Subring.sum_mem _ fun x _ =>
      Subring.mul_mem _ (mem_intRing.mpr (hp _)) (mem_intRing.mpr (hq _)))
  have hone : MvIsInt v (1 : MvPowerSeries τ C) := by
    intro e
    rw [coeff_one]
    split_ifs
    · exact mem_intRing.mp (Subring.one_mem _)
    · exact mem_intRing.mp (Subring.zero_mem _)
  have hpow : ∀ (p : MvPowerSeries τ C) (n : ℕ), MvIsInt v p → MvIsInt v (p ^ n) := by
    intro p n hp
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hp
  have hprod : ∀ d : σ →₀ ℕ, MvIsInt v (d.prod fun s e => a s ^ e) := by
    intro d
    show MvIsInt v (∏ s ∈ d.support, a s ^ d s)
    exact Finset.prod_induction _ (MvIsInt v) hmul hone (fun s _ => hpow _ _ (ha s))
  intro e
  rw [coeff_subst hS]
  apply mem_intRing.mp
  refine finsum_induction (fun x => x ∈ intRing v) (Subring.zero_mem _)
    (fun x y hx hy => Subring.add_mem _ hx hy) (fun d => ?_)
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (mem_intRing.mpr (hf d)) (mem_intRing.mpr (hprod d e))

theorem unit_finsupp (e : Unit →₀ ℕ) : e = Finsupp.single () (e ()) := by
  exact Finsupp.ext fun u => by cases u; simp

theorem psIsInt_iff {v : AddValuation C (WithTop ℝ)} {f : PowerSeries C} :
    PsIsInt v f ↔ MvIsInt v (σ := Unit) f := by
  constructor
  · intro h α
    rw [unit_finsupp α]
    exact h (α ())
  · intro h n
    exact h (Finsupp.single () n)

variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem hasSubst_F (G : LogFGL v d) : HasSubst G.F := hs_lemma_2 G.F_const

theorem isCurve_zero : IsCurve v (0 : Fin d → PowerSeries C) := by
  intro a
  refine ⟨by simp, fun n => ?_⟩
  simp [IsIntV]

private theorem cc_lemma_3 {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C}
    (hf : constantCoeff f = 0) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : constantCoeff (subst a f) = 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst (hs_lemma_2 ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun s => by simpa using h s)
    have hp : constantCoeff (e.prod fun s n => a s ^ n) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, ha0 s, zero_pow hs])
    rw [coeff_zero_eq_constantCoeff_apply, hp, smul_zero]

theorem isCurve_add (G : LogFGL v d) {ga gb : Fin d → PowerSeries C}
    (ha : IsCurve v ga) (hb : IsCurve v gb) : IsCurve v (G.add ga gb) := by
  intro a
  have hs0 : ∀ s, constantCoeff (Sum.elim ga gb s) = 0 := by
    rintro (s | s)
    · exact (ha s).1
    · exact (hb s).1
  have hsI : ∀ s, MvIsInt v (Sum.elim ga gb s) := by
    rintro (s | s)
    · exact psIsInt_iff.mp (ha s).2
    · exact psIsInt_iff.mp (hb s).2
  exact ⟨cc_lemma_3 (G.F_const a) hs0, psIsInt_iff.mpr (mvIsInt_subst v (G.F_int a) hsI hs0)⟩

theorem lgCurve_add (G : LogFGL v d) {ga gb : Fin d → PowerSeries C}
    (ha : ∀ b, PowerSeries.constantCoeff (ga b) = 0)
    (hb : ∀ b, PowerSeries.constantCoeff (gb b) = 0) (a : Fin d) :
    G.lgCurve (G.add ga gb) a = G.lgCurve ga a + G.lgCurve gb a := by
  have hE0 : ∀ s, constantCoeff (Sum.elim ga gb s) = 0 := by
    rintro (s | s)
    · exact ha s
    · exact hb s
  have hE : HasSubst (Sum.elim ga gb) := hs_lemma_2 hE0
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma_2 (fun b => constantCoeff_X _)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma_2 (fun b => constantCoeff_X _)
  show subst (fun b => subst (Sum.elim ga gb) (G.F b)) (G.lg a) =
    subst ga (G.lg a) + subst gb (G.lg a)
  rw [← subst_comp_subst_apply (hasSubst_F G) hE, G.lg_F a, subst_add hE,
    subst_comp_subst_apply hl hE, subst_comp_subst_apply hr hE]
  simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]

theorem lgCurve_zero (G : LogFGL v d) (a : Fin d) : G.lgCurve 0 a = 0 := by
  classical
  have h0 : HasSubst (0 : Fin d → PowerSeries C) := hs_lemma_2 (fun _ => by simp)
  show subst (0 : Fin d → PowerSeries C) (G.lg a) = 0
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_subst h0, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · rw [hn, coeff_zero_eq_constantCoeff_apply, G.lg_const a, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext fun s => by simpa using h s)
    have hp : (n.prod fun s k => (0 : Fin d → PowerSeries C) s ^ k) = 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [Pi.zero_apply, zero_pow hs])
    rw [hp, map_zero, smul_zero]

theorem isCurve_sumList (G : LogFGL v d) :
    ∀ l : List (Fin d → PowerSeries C), (∀ g ∈ l, IsCurve v g) → IsCurve v (G.sumList l)
  | [], _ => isCurve_zero
  | g :: l, h => isCurve_add G (h g (by simp))
      (isCurve_sumList G l fun g' hg' => h g' (by simp [hg']))

theorem lgCurve_sumList (G : LogFGL v d) :
    ∀ l : List (Fin d → PowerSeries C), (∀ g ∈ l, IsCurve v g) → ∀ a,
      G.lgCurve (G.sumList l) a = (l.map fun g => G.lgCurve g a).sum
  | [], _, a => by simp [LogFGL.sumList, lgCurve_zero]
  | g :: l, h, a => by
      have hl : ∀ g' ∈ l, IsCurve v g' := fun g' hg' => h g' (by simp [hg'])
      rw [LogFGL.sumList, lgCurve_add G (fun b => (h g (by simp) b).1)
        (fun b => (isCurve_sumList G l hl b).1), lgCurve_sumList G l hl a]
      simp

theorem isCurve_sumF (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ u, IsCurve v (g u)) : IsCurve v (G.sumF g) :=
  isCurve_sumList G (List.ofFn g) (fun g' hg' => by
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hg'
    exact h u)

theorem lgCurve_sumF (G : LogFGL v d) {m : ℕ} (g : Fin m → Fin d → PowerSeries C)
    (h : ∀ u, IsCurve v (g u)) (a : Fin d) :
    G.lgCurve (G.sumF g) a = ∑ u, G.lgCurve (g u) a := by
  rw [show G.sumF g = G.sumList (List.ofFn g) from rfl,
    lgCurve_sumList G _ (fun g' hg' => by
      obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hg'
      exact h u) a]
  simp [List.map_ofFn, List.sum_ofFn]

theorem isCurve_rescale {x : C} (hx : IsIntV v x) {ga : Fin d → PowerSeries C}
    (h : IsCurve v ga) : IsCurve v (rescaleCurve x ga) := by
  intro a
  refine ⟨?_, fun n => ?_⟩
  · show PowerSeries.constantCoeff (PowerSeries.rescale x (ga a)) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, (h a).1]
  · show IsIntV v (PowerSeries.coeff n (PowerSeries.rescale x (ga a)))
    rw [PowerSeries.coeff_rescale]
    exact mem_intRing.mp (Subring.mul_mem _ (Subring.pow_mem _ (mem_intRing.mpr hx) n)
      (mem_intRing.mpr ((h a).2 n)))

theorem lgCurve_rescale (G : LogFGL v d) (x : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve x ga) a = PowerSeries.rescale x (G.lgCurve ga a) := by
  have hX : HasSubst (fun _ : Unit => (x • PowerSeries.X : PowerSeries C)) :=
    (PowerSeries.HasSubst.smul_X' x).const
  show subst (fun b => PowerSeries.rescale x (ga b)) (G.lg a) = PowerSeries.rescale x (subst ga (G.lg a))
  simp only [PowerSeries.rescale_eq_subst, PowerSeries.subst_def]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hX]

theorem degree_eq_one {σ : Type} {e : σ →₀ ℕ} (he : e.degree = 1) :
    ∃ b, e = Finsupp.single b 1 := by
  classical
  have hd : ∑ i ∈ e.support, e i = 1 := by
    first
    | exact he
    | simpa [Finsupp.degree] using he
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hd
    exact zero_ne_one hd
  obtain ⟨b, hb⟩ := hne
  refine ⟨b, ?_⟩
  rw [← Finset.add_sum_erase _ _ hb] at hd
  have hb1 : 1 ≤ e b := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hb)
  have hrest : ∑ i ∈ e.support.erase b, e i = 0 := by omega
  have heb : e b = 1 := by omega
  ext i
  by_cases hi : i = b
  · rw [hi, heb, Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_cases his : i ∈ e.support
    · exact (Finset.sum_eq_zero_iff.mp hrest) i (Finset.mem_erase.mpr ⟨hi, his⟩)
    · by_contra hc
      exact his (Finsupp.mem_support_iff.mpr hc)

theorem order_lg_sub_X (G : LogFGL v d) (a : Fin d) : ((2 : ℕ) : ℕ∞) ≤ (G.lg a - X a).order := by
  classical
  apply MvPowerSeries.le_order
  intro e he
  have he' : e.degree < 2 := by exact_mod_cast he
  rw [map_sub]
  rcases (show e.degree = 0 ∨ e.degree = 1 by omega) with h0 | h1
  · have hz : e = 0 := by
      first
      | exact Finsupp.degree_eq_zero_iff.mp h0
      | exact (Finsupp.degree_eq_zero_iff e).mp h0
    rw [hz, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, G.lg_const,
      constantCoeff_X, sub_zero]
  · obtain ⟨b, rfl⟩ := degree_eq_one h1
    rw [G.lg_lin, coeff_X]
    by_cases hab : a = b
    · rw [hab, if_pos rfl, if_pos rfl, sub_self]
    · rw [if_neg hab, if_neg (fun h => hab ((Finsupp.single_left_injective one_ne_zero h).symm)),
        sub_zero]

theorem coeff_lgCurve_low (G : LogFGL v d) {ga : Fin d → PowerSeries C} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ b, ∀ i < k, PowerSeries.coeff i (ga b) = 0) (a : Fin d) {j : ℕ} (hj : j < 2 * k) :
    PowerSeries.coeff j (G.lgCurve ga a) = PowerSeries.coeff j (ga a) := by
  have h0 : ∀ b, constantCoeff (ga b) = 0 := fun b => by
    have := hk b 0 hk1
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  have hs : HasSubst ga := hasSubst_of_constantCoeff_zero h0
  have hsplit : G.lgCurve ga a = ga a + subst ga (G.lg a - X a) := by
    rw [LogFGL.lgCurve, subst_sub hs, subst_X hs]; ring
  have hord : ((k : ℕ∞)) ≤ ⨅ b, MvPowerSeries.order (ga b) := le_iInf fun b => nat_le_order fun e he => by
    rw [unit_finsupp e] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hk b _ he
  have hR := le_order_subst hs (G.lg a - X a)
  have hlt : ((Finsupp.single () j).degree : ℕ∞) < (subst ga (G.lg a - X a)).order := by
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_trans (mul_le_mul' hord (order_lg_sub_X G a)) hR)
    exact_mod_cast (show j < k * 2 by omega)
  rw [hsplit, map_add]
  have := coeff_of_lt_order hlt
  change _ + coeff (Finsupp.single () j) _ = _
  rw [this, add_zero]

theorem tangent_eq_lc_zero (G : LogFGL v d) (p : ℕ) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0) : tangent ga = G.lc p ga 0 := by
  funext a
  show PowerSeries.coeff 1 (ga a) = PowerSeries.coeff (p ^ 0) (G.lgCurve ga a)
  rw [pow_zero]
  exact (coeff_lgCurve_low G le_rfl (fun b i hi => by
    rw [Nat.lt_one_iff.mp hi, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0 b]) a
    (by norm_num)).symm

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
