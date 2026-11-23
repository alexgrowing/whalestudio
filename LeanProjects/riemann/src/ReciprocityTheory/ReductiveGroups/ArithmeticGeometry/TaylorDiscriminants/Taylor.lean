import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff

section Sym

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem cml_perm {l l' : List V} (p : l.Perm l') :
    ∀ (n : ℕ) (M : ContinuousMultilinearMap ℂ (fun _ : Fin n => V) ℂ),
      (∀ (v : Fin n → V) (σ : Equiv.Perm (Fin n)), M (v ∘ σ) = M v) →
      ∀ (h : l.length = n) (h' : l'.length = n),
        M (fun i => l.get (i.cast h.symm)) = M (fun i => l'.get (i.cast h'.symm)) := by
  intro n M hM
  let F : List V → ℂ := fun k => if hk : k.length = n then M (fun i => k.get (i.cast hk.symm)) else 0
  have key : ∀ l₀ : List V, F (l₀ ++ l) = F (l₀ ++ l') := by
    induction p with
    | nil => intro l₀; rfl
    | @cons x l₁ l₂ _ ih =>
      intro l₀
      have e₁ : l₀ ++ x :: l₁ = (l₀ ++ [x]) ++ l₁ := by simp
      have e₂ : l₀ ++ x :: l₂ = (l₀ ++ [x]) ++ l₂ := by simp
      rw [e₁, e₂]
      exact ih _
    | swap x y k =>
      intro l₀
      simp only [F]
      by_cases hk : (l₀ ++ y :: x :: k).length = n
      · have hk' : (l₀ ++ x :: y :: k).length = n := by simpa using hk
        rw [dif_pos hk, dif_pos hk']
        have hlt : l₀.length + 1 < n := by simp at hk; omega
        rw [← hM _ (Equiv.swap (⟨l₀.length, by omega⟩ : Fin n) ⟨l₀.length + 1, hlt⟩)]
        congr 1
        funext i
        obtain ⟨i, hi⟩ := i
        simp only [Function.comp_apply, Equiv.swap_apply_def, Fin.mk.injEq]
        split_ifs with h1 h2
        · subst h1
          simp [List.getElem_append]
        · subst h2
          simp [List.getElem_append]
        · rcases lt_or_ge i l₀.length with h3 | h3
          · simp [List.getElem_append, h3]
          · obtain ⟨j, rfl⟩ : ∃ j, i = l₀.length + (j + 2) := ⟨i - (l₀.length + 2), by omega⟩
            simp [List.getElem_append]
      · have hk' : ¬ (l₀ ++ x :: y :: k).length = n := by simpa using hk
        rw [dif_neg hk, dif_neg hk']
    | trans _ _ ih₁ ih₂ => intro l₀; exact (ih₁ l₀).trans (ih₂ l₀)
  intro h h'
  have e := key []
  simp only [F, List.nil_append, dif_pos h, dif_pos h'] at e
  exact e

def lD (φ : V → ℂ) (x : V) (l : List V) : ℂ := iteratedFDeriv ℂ l.length φ x (fun i => l.get i)

theorem lD_eq (φ : V → ℂ) (x : V) (l : List V) {n : ℕ} (h : l.length = n) :
    lD φ x l = iteratedFDeriv ℂ n φ x (fun i => l.get (i.cast h.symm)) := by
  subst h
  rfl

theorem lD_perm {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {l l' : List V} (p : l.Perm l') :
    lD φ x l = lD φ x l' := by
  have hl : l'.length = l.length := p.length_eq.symm
  rw [lD_eq φ x l rfl, lD_eq φ x l' hl]
  exact cml_perm p l.length _ (fun v σ => (hφ.of_le le_top).iteratedFDeriv_comp_perm v σ) rfl hl

def mD (φ : V → ℂ) (x : V) (s : Multiset V) : ℂ := lD φ x s.toList

theorem mD_coe {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) (l : List V) :
    mD φ x (l : Multiset V) = lD φ x l := lD_perm hφ (Multiset.coe_eq_coe.mp (Multiset.coe_toList _))

theorem lD_cons (φ : V → ℂ) (x v : V) (l : List V) :
    lD φ x (v :: l) = (iteratedFDeriv ℂ (l.length + 1) φ x).curryLeft v (fun i => l.get i) := by
  show iteratedFDeriv ℂ (l.length + 1) φ x (fun i => (v :: l).get i) = _
  rw [ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · first | rfl | simp
  · first | rfl | simp

theorem mD_cons {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) (v : V) (s : Multiset V) :
    mD φ x (v ::ₘ s) =
      (iteratedFDeriv ℂ (s.toList.length + 1) φ x).curryLeft v (fun i => s.toList.get i) := by
  have hp : (v ::ₘ s).toList.Perm (v :: s.toList) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList]
  show lD φ x (v ::ₘ s).toList = _
  rw [lD_perm hφ hp, lD_cons]

theorem mD_cons_sum {φ : V → ℂ} {x : V} (hφ : ContDiffAt ℂ ω φ x) {ι : Type} (t : Finset ι) (c : ι → ℂ)
    (w : ι → V) (s : Multiset V) :
    mD φ x ((∑ i ∈ t, c i • w i) ::ₘ s) = ∑ i ∈ t, c i * mD φ x (w i ::ₘ s) := by
  simp only [mD_cons hφ, map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

end Sym

section Add

variable (R : Type) [CommRing R]

def addF (g : ℕ) : Fin g → PS R 2 g := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)

variable {R}

theorem ev_zero' {m n d : ℕ} (a : Fin m → Pt R n d) : ev a (0 : PS R m d) = 0 := by
  first
  | exact map_zero _
  | (simp only [ev]; exact MvPowerSeries.subst_zero _)
  | simp [ev, MvPowerSeries.subst, MvPowerSeries.eval₂]
  | simp [ev, MvPowerSeries.subst]

theorem dof_addF {g : ℕ} (v : Fin g → R) (f : PS R 1 g) :
    Dof (addF R g) v f = ∑ j, C (v j) * pderiv R ((0 : Fin 1), j) f := by
  classical
  unfold Dof
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply]
  · intro b _ hb
    simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply, hb, Ne.symm hb, ev_zero']
  · intro h
    exact absurd (Finset.mem_univ j) h

end Add

section Tay

variable {g : ℕ}

def dirs (n : Fin 1 × Fin g →₀ ℕ) : Multiset (Fin g → ℂ) :=
  (Finsupp.toMultiset n).map fun p => Pi.single p.2 1

def fct (n : Fin 1 × Fin g →₀ ℕ) : ℂ := ∏ p, ((n p).factorial : ℂ)

def tay (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) : MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun n => mD θ 0 (dirs n + s) / fct n

theorem coeff_tay (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) (n : Fin 1 × Fin g →₀ ℕ) :
    coeff n (tay θ s) = mD θ 0 (dirs n + s) / fct n := rfl

theorem dirs_add_single (n : Fin 1 × Fin g →₀ ℕ) (p : Fin 1 × Fin g) :
    dirs (n + Finsupp.single p 1) = Pi.single p.2 1 ::ₘ dirs n := by
  first
  | (simp only [dirs, map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add, Multiset.map_singleton]
     rw [add_comm, Multiset.singleton_add])
  | simp [dirs, Finsupp.toMultiset_add, add_comm]

theorem fct_ne_zero (n : Fin 1 × Fin g →₀ ℕ) : fct n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem fct_add_single (n : Fin 1 × Fin g →₀ ℕ) (p : Fin 1 × Fin g) :
    fct (n + Finsupp.single p 1) = fct n * ((n p : ℂ) + 1) := by
  unfold fct
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase Finset.univ (fun q => (((n q).factorial : ℕ) : ℂ)) (Finset.mem_univ p)]
  have h1 : ∀ q ∈ Finset.univ.erase p,
      ((((n + Finsupp.single p 1 : Fin 1 × Fin g →₀ ℕ) q).factorial : ℕ) : ℂ) = ((n q).factorial : ℂ) := by
    intro q hq
    have hqp := Finset.ne_of_mem_erase hq
    simp [Finsupp.single_apply, hqp, Ne.symm hqp]
  rw [Finset.prod_congr rfl h1, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

theorem sum_single_smul (v : Fin g → ℂ) : v = ∑ j, v j • (Pi.single j (1 : ℂ) : Fin g → ℂ) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem dof_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (s : Multiset (Fin g → ℂ)) :
    Dof (addF ℂ g) v (tay θ s) = tay θ (v ::ₘ s) := by
  classical
  rw [dof_addF]
  ext n
  have key : ∀ j : Fin g, coeff n (C (v j) * pderiv ℂ ((0 : Fin 1), j) (tay θ s)) =
      v j * mD θ 0 (Pi.single j 1 ::ₘ (dirs n + s)) / fct n := by
    intro j
    have h1 : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    have h2 := fct_ne_zero n
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_pderiv, coeff_tay, dirs_add_single, fct_add_single,
      Multiset.cons_add]
    push_cast
    field_simp
  rw [map_sum, Finset.sum_congr rfl fun j _ => key j, coeff_tay, Multiset.add_cons]
  have hs := mD_cons_sum hθ Finset.univ v (fun j => (Pi.single j (1 : ℂ) : Fin g → ℂ)) (dirs n + s)
  rw [← sum_single_smul v] at hs
  rw [hs, Finset.sum_div]

theorem dof_iter_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (k : ℕ)
    (s : Multiset (Fin g → ℂ)) :
    (Dof (addF ℂ g) v)^[k] (tay θ s) = tay θ (Multiset.replicate k v + s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, dof_tay hθ, Multiset.replicate_succ, Multiset.cons_add]

theorem foldr_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} (u : ι → Fin g → ℂ)
    (m : ι →₀ ℕ) (L : List ι) (s : Multiset (Fin g → ℂ)) :
    L.foldr (fun l f => (Dof (addF ℂ g) (u l))^[m l] f) (tay θ s) =
      tay θ ((L.map fun l => Multiset.replicate (m l) (u l)).sum + s) := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.foldr_cons, ih, dof_iter_tay hθ, List.map_cons, List.sum_cons, add_assoc]

theorem toMultiset_map_eq {ι : Type} [Fintype ι] (u : ι → Fin g → ℂ) (m : ι →₀ ℕ) :
    (Finsupp.toMultiset m).map u = ∑ l, Multiset.replicate (m l) (u l) := by
  refine Finsupp.induction_linear m ?_ ?_ ?_
  · simp
  · intro f₁ f₂ h₁ h₂
    rw [map_add, Multiset.map_add, h₁, h₂]
    simp [Multiset.replicate_add, Finset.sum_add_distrib]
  · intro a b
    rw [Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.map_singleton, Multiset.nsmul_singleton]
    rw [Finset.sum_eq_single a]
    · simp
    · intro l _ hl
      simp [Finsupp.single_apply, Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem constantCoeff_tay (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) :
    constantCoeff (tay θ s) = mD θ 0 s := by
  first
  | (rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_tay]
     simp [dirs, fct])
  | (show tay θ s 0 = _
     simp [tay, dirs, fct])

theorem constantCoeff_dmonOf_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} [Fintype ι]
    (u : ι → Fin g → ℂ) (m : ι →₀ ℕ) :
    constantCoeff (DmonOf (addF ℂ g) u m (tay θ 0)) = mD θ 0 ((Finsupp.toMultiset m).map u) := by
  unfold DmonOf
  rw [foldr_tay hθ, add_zero, constantCoeff_tay, toMultiset_map_eq]
  congr 1
  first
  | exact Finset.sum_toList _ _
  | exact Finset.sum_to_list _ _
  | simp [Finset.sum_toList]

theorem coeff_tay_zero (θ : (Fin g → ℂ) → ℂ) (n : Fin 1 × Fin g →₀ ℕ) :
    fct n * coeff n (tay θ 0) = mD θ 0 (dirs n) := by
  rw [coeff_tay, add_zero]
  first
  | (field_simp [fct_ne_zero n]; done)
  | (field_simp [fct_ne_zero n]; ring)
  | exact mul_div_cancel₀ _ (fct_ne_zero n)

theorem polyDeriv_eq_mD {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} (P : MvPolynomial ι ℂ)
    (u : ι → Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 =
      ∑ m ∈ P.support, P.coeff m * mD θ 0 ((Finsupp.toMultiset m).map u) := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hL : (Finsupp.toMultiset m).map u =
      (((Finsupp.toMultiset m).toList.map u : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  have hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m) := by
    rw [List.length_map, Multiset.length_toList]
  rw [hL, mD_coe hθ, lD_eq θ 0 _ hlen]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem constantCoeff_dpolyOf_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) {ι : Type} [Fintype ι]
    (u : ι → Fin g → ℂ) (P : MvPolynomial ι ℂ) :
    constantCoeff (DpolyOf (addF ℂ g) u P (tay θ 0)) = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u θ 0 := by
  unfold DpolyOf
  rw [polyDeriv_eq_mD hθ, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, constantCoeff_dmonOf_tay hθ]

end Tay

section TaySt

def TaylorMulSt : Prop :=
  (∀ (g : ℕ) (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    tay (f * h) 0 = tay f 0 * tay h 0 ∧ tay (f + h) 0 = tay f 0 + tay h 0) ∧
  (∀ (g : ℕ) (c : ℂ), tay (g := g) (fun _ => c) 0 = C c) ∧
  (∀ (g : ℕ) (f h : (Fin g → ℂ) → ℂ), f =ᶠ[nhds 0] h → tay f 0 = tay h 0)

end TaySt

end ReciprocityTheory.ChartRestriction.G.PullbackSections
