import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

noncomputable section

open MvPolynomial Finset

namespace Formalism.L2.KerInert.SharpPolyP.Det

variable {K : Type*} [Field K] {σ : Type*}

theorem sp_eval_update [DecidableEq σ] {p : MvPolynomial σ K} {v : σ} (h : degreeOf v p = 0) (x : σ → K) (t : K) :
    eval (Function.update x v t) p = eval x p := by
  have hv : v ∉ p.vars := by rw [mem_vars_iff_degreeOf_ne_zero]; simpa using h
  exact hom_congr_vars (f₁ := eval (Function.update x v t)) (f₂ := eval x) (by ext; simp)
    (fun i hi _ => by
      have : i ≠ v := fun e => hv (e ▸ hi)
      simp [Function.update_of_ne this]) rfl

theorem sp_degreeOf_sign {m : Type*} [Fintype m] [DecidableEq m] (π : Equiv.Perm m) (v : σ) :
    degreeOf v (((Equiv.Perm.sign π : ℤ) : MvPolynomial σ K)) = 0 := by
  rw [← map_intCast (MvPolynomial.C (σ := σ) (R := K)), degreeOf_C]

theorem sp_degreeOf_det_le {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m (MvPolynomial σ K)) (v : σ) (α : m)
    (hrow : ∀ j, degreeOf v (M α j) ≤ 1) (hoth : ∀ i j, i ≠ α → degreeOf v (M i j) = 0) :
    degreeOf v M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun π _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [sp_degreeOf_sign, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (π.symm α))]
  have h0 : ∑ i ∈ univ.erase (π.symm α), degreeOf v (M (π i) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply hoth
    intro e
    apply (Finset.mem_erase.1 hi).1
    rw [← e]; simp
  rw [h0, add_zero]
  simpa using hrow (π.symm α)

theorem sp_degreeOf_det_zero {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m (MvPolynomial σ K)) (v : σ)
    (h : ∀ i j, degreeOf v (M i j) = 0) : degreeOf v M.det = 0 := by
  rw [Matrix.det_apply']
  refine Nat.eq_zero_of_le_zero ((degreeOf_sum_le _ _ _).trans (Finset.sup_le fun π _ => ?_))
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [sp_degreeOf_sign, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp [h]

theorem sp_degreeOf_X_le (v u : σ) : degreeOf v (X u : MvPolynomial σ K) ≤ 1 := by
  classical
  rw [degreeOf_X]
  split_ifs <;> simp

variable {n : ℕ} (e : Fin n × Fin n → σ)

def gDet : MvPolynomial σ K := (Matrix.of fun i j : Fin n => (X (e (i, j)) : MvPolynomial σ K)).det

variable {e}

theorem sp_gDet_deg_other (u : σ) (hu : ∀ p, e p ≠ u) : degreeOf u (gDet (K := K) e) = 0 := by
  unfold gDet
  apply sp_degreeOf_det_zero
  intro i j
  classical
  simp only [Matrix.of_apply]
  rw [degreeOf_X, if_neg (Ne.symm (hu (i, j)))]

theorem sp_gDet_deg_le (he : Function.Injective e) (α s : Fin n) : degreeOf (e (α, s)) (gDet (K := K) e) ≤ 1 := by
  unfold gDet
  apply sp_degreeOf_det_le _ _ α
  · intro j
    exact sp_degreeOf_X_le _ _
  · intro i j hi
    classical
    simp only [Matrix.of_apply]
    rw [degreeOf_X, if_neg]
    intro h
    exact hi (congrArg Prod.fst (he h)).symm

theorem sp_gDet_deg_ge (he : Function.Injective e) (α s : Fin n) : 1 ≤ degreeOf (e (α, s)) (gDet (K := K) e) := by
  classical
  by_contra hlt
  have h0 : degreeOf (e (α, s)) (gDet (K := K) e) = 0 := by omega
  set π : Equiv.Perm (Fin n) := Equiv.swap α s with hπ
  let x : σ → K := fun u => if ∃ i, u = e (i, π i) then 1 else 0
  have hx : ∀ i j, x (e (i, j)) = if π i = j then 1 else 0 := by
    intro i j
    simp only [x]
    by_cases hij : π i = j
    · rw [if_pos ⟨i, by rw [hij]⟩, if_pos hij]
    · rw [if_neg, if_neg hij]
      rintro ⟨k, hk⟩
      have := he hk
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact hij rfl
  have hev : ∀ y : σ → K, eval y (gDet (K := K) e) = (Matrix.of fun i j : Fin n => y (e (i, j))).det := by
    intro y
    rw [gDet, RingHom.map_det]
    congr 1
    ext i j
    simp
  have h1 : eval x (gDet (K := K) e) = (Equiv.Perm.sign π : K) := by
    rw [hev]
    have : (Matrix.of fun i j : Fin n => x (e (i, j))) = π.permMatrix K := by
      ext i j
      rw [Matrix.of_apply, hx]
      simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    rw [this, Matrix.det_permutation]
  have h2 : eval (Function.update x (e (α, s)) 0) (gDet (K := K) e) = 0 := by
    rw [hev]
    apply Matrix.det_eq_zero_of_column_eq_zero s
    intro i
    simp only [Matrix.of_apply]
    by_cases hi : i = α
    · subst hi; simp
    · have hne : e (i, s) ≠ e (α, s) := fun h => hi (congrArg Prod.fst (he h))
      rw [Function.update_of_ne hne, hx]
      rw [if_neg]
      intro hs
      apply hi
      have : π i = π α := by rw [hs]; simp [hπ]
      exact π.injective this
  have h3 := sp_eval_update h0 x 0
  rw [h2, h1] at h3
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> rw [h] at h3 <;> simp at h3

theorem sp_gDet_deg (he : Function.Injective e) (α s : Fin n) : degreeOf (e (α, s)) (gDet (K := K) e) = 1 := le_antisymm (sp_gDet_deg_le he α s) (sp_gDet_deg_ge he α s)

theorem sp_gDet_ne_zero (he : Function.Injective e) (hn : 0 < n) : gDet (K := K) e ≠ 0 := by
  classical
  intro h0
  obtain ⟨x, hx⟩ : ∃ x : σ → K, ∀ i j : Fin n, x (e (i, j)) = (1 : Matrix (Fin n) (Fin n) K) i j := by
    refine ⟨fun u => if ∃ k : Fin n, e (k, k) = u then 1 else 0, fun i j => ?_⟩
    simp only [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl⟩, if_pos rfl]
    · rw [if_neg hij, if_neg]
      rintro ⟨k, hk⟩
      have h2 := he hk
      simp only [Prod.mk.injEq] at h2
      exact hij (h2.1.symm.trans h2.2)
  have h1 := congrArg (eval x) h0
  rw [map_zero, gDet, RingHom.map_det] at h1
  have h3 : (eval x).mapMatrix (Matrix.of fun i j : Fin n => (X (e (i, j)) : MvPolynomial σ K)) = 1 := by
    ext i j
    simp [hx]
  rw [h3, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem sp_merge_row [DecidableEq σ] (he : Function.Injective e) (α s s' : Fin n) :
    degreeOf (e (α, s)) (rename (fun u => if u = e (α, s') then e (α, s) else u) (gDet (K := K) e)) ≤ 1 := by
  classical
  rw [gDet, AlgHom.map_det]
  apply sp_degreeOf_det_le _ _ α
  · intro j; simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]; exact sp_degreeOf_X_le _ _
  · intro i j hi
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
    have h1 : e (i, j) ≠ e (α, s') := fun h => hi (congrArg Prod.fst (he h))
    rw [if_neg h1]
    apply degreeOf_X_of_ne
    intro h
    exact hi (congrArg Prod.fst (he h)).symm

theorem sp_merge_col [DecidableEq σ] (he : Function.Injective e) (α α' s : Fin n) :
    degreeOf (e (α, s)) (rename (fun u => if u = e (α', s) then e (α, s) else u) (gDet (K := K) e)) ≤ 1 := by
  classical
  rw [gDet, ← Matrix.det_transpose, AlgHom.map_det]
  apply sp_degreeOf_det_le _ _ s
  · intro j; simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, rename_X]
    exact sp_degreeOf_X_le _ _
  · intro i j hi
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, rename_X]
    have h1 : e (j, i) ≠ e (α', s) := fun h => hi (congrArg Prod.snd (he h))
    rw [if_neg h1]
    apply degreeOf_X_of_ne
    intro h
    exact hi (congrArg Prod.snd (he h)).symm

theorem sp_cross [DecidableEq σ] {D g h : MvPolynomial σ K} (hD : D = g * h) {v w : σ} (hvw : v ≠ w)
    (hgv : degreeOf v g = 1) (hgw : degreeOf w g = 0) (hhv : degreeOf v h = 0) (hhw : degreeOf w h = 1)
    (hm : degreeOf v (rename (fun u => if u = w then v else u) D) ≤ 1) : False := by
  have hg0 : g ≠ 0 := by intro h0; rw [h0, degreeOf_zero] at hgv; exact absurd hgv (by norm_num)
  have hh0 : h ≠ 0 := by intro h0; rw [h0, degreeOf_zero] at hhw; exact absurd hhw (by norm_num)
  have hgr : rename (fun u => if u = w then v else u) g = g := by
    have := hom_congr_vars (f₁ := (rename (R := K) (fun u => if u = w then v else u)).toRingHom) (f₂ := RingHom.id _)
      (p₁ := g) (p₂ := g) (by ext; simp) (fun i hi _ => by
        have hiw : i ≠ w := by
          intro e; rw [e, mem_vars_iff_degreeOf_ne_zero] at hi; exact hi hgw
        simp [hiw]) rfl
    simpa using this
  have hhr : rename (fun u => if u = w then v else u) h = rename (Equiv.swap v w) h := by
    have := hom_congr_vars (f₁ := (rename (R := K) (fun u => if u = w then v else u)).toRingHom)
      (f₂ := (rename (R := K) (Equiv.swap v w)).toRingHom)
      (p₁ := h) (p₂ := h) (by ext; simp) (fun i hi _ => by
        have hiv : i ≠ v := by
          intro e; rw [e, mem_vars_iff_degreeOf_ne_zero] at hi; exact hi hhv
        by_cases hiw : i = w
        · subst hiw; simp
        · simp [hiw, Equiv.swap_apply_of_ne_of_ne hiv hiw]) rfl
    simpa using this
  have hsw : degreeOf v (rename (Equiv.swap v w) h) = 1 := by
    have := degreeOf_rename_of_injective (p := h) (Equiv.swap v w).injective w
    rw [Equiv.swap_apply_right] at this
    rw [this, hhw]
  have hne : rename (Equiv.swap v w) h ≠ 0 := by
    intro h0
    apply hh0
    exact rename_injective _ (Equiv.swap v w).injective (by rw [h0, map_zero])
  rw [hD, map_mul, hgr, hhr, degreeOf_mul_eq hg0 hne, hgv, hsw] at hm
  omega

theorem sp_isUnit_of_deg_zero {h : MvPolynomial σ K} (h0 : h ≠ 0) (hd : ∀ u, degreeOf u h = 0) : IsUnit h := by
  have ht : h.totalDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro m hm
    have : m = 0 := by
      ext u
      have := monomial_le_degreeOf u hm
      rw [hd u] at this
      simpa using this
    simp [this]
  rw [totalDegree_eq_zero_iff_eq_C] at ht
  rw [ht] at h0 ⊢
  have hc : h.coeff 0 ≠ 0 := by intro hc; apply h0; rw [hc, map_zero]
  exact (isUnit_iff_ne_zero.2 hc).map C

theorem sp_gDet_irreducible (he : Function.Injective e) (hn : 0 < n) : Irreducible (gDet (K := K) e) := by
  classical
  have hD0 := sp_gDet_ne_zero (K := K) he hn
  have hsum : ∀ {g h : MvPolynomial σ K}, gDet e = g * h → ∀ u, degreeOf u g + degreeOf u h = degreeOf u (gDet (K := K) e) := by
    intro g h hgh u
    have hg : g ≠ 0 := by rintro rfl; rw [zero_mul] at hgh; exact hD0 hgh
    have hh : h ≠ 0 := by rintro rfl; rw [mul_zero] at hgh; exact hD0 hgh
    rw [hgh, degreeOf_mul_eq hg hh]

  have clos : ∀ {g h : MvPolynomial σ K}, gDet e = g * h → ∀ α0 s0, degreeOf (e (α0, s0)) g = 1 → IsUnit h := by
    intro g h hgh α0 s0 hg1
    have hs := hsum hgh
    have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hgh; exact hD0 hgh

    have hrow : ∀ α s s', degreeOf (e (α, s)) g = 1 → degreeOf (e (α, s')) g = 1 := by
      intro α s s' h1
      by_contra h2
      have hs1 := hs (e (α, s)); have hs2 := hs (e (α, s'))
      rw [sp_gDet_deg he] at hs1 hs2
      have hss : s ≠ s' := by rintro rfl; exact h2 h1
      have hvw : e (α, s) ≠ e (α, s') := fun h => hss (congrArg Prod.snd (he h))
      exact sp_cross hgh hvw h1 (by omega) (by omega) (by omega) (sp_merge_row he α s s')
    have hcol : ∀ α α' s, degreeOf (e (α, s)) g = 1 → degreeOf (e (α', s)) g = 1 := by
      intro α α' s h1
      by_contra h2
      have hs1 := hs (e (α, s)); have hs2 := hs (e (α', s))
      rw [sp_gDet_deg he] at hs1 hs2
      have hss : α ≠ α' := by rintro rfl; exact h2 h1
      have hvw : e (α, s) ≠ e (α', s) := fun h => hss (congrArg Prod.fst (he h))
      exact sp_cross hgh hvw h1 (by omega) (by omega) (by omega) (sp_merge_col he α α' s)
    apply sp_isUnit_of_deg_zero hh0
    intro u
    by_cases hu : ∃ p, e p = u
    · obtain ⟨⟨α, s⟩, rfl⟩ := hu
      have := hs (e (α, s))
      rw [sp_gDet_deg he, hcol α0 α s (hrow α0 s0 s hg1)] at this
      omega
    · push Not at hu
      have := hs u
      rw [sp_gDet_deg_other u hu] at this
      omega
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨q, hq⟩ := hu.exists_right_inv
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact zero_ne_one hq
    have := congrArg (degreeOf (e (⟨0, hn⟩, ⟨0, hn⟩))) hq
    rw [degreeOf_mul_eq hD0 hq0, sp_gDet_deg he, ← C_1, degreeOf_C] at this
    omega
  · intro g h hgh
    have hs := hsum hgh (e (⟨0, hn⟩, ⟨0, hn⟩))
    rw [sp_gDet_deg he] at hs
    by_cases hg1 : degreeOf (e (⟨0, hn⟩, ⟨0, hn⟩)) g = 1
    · exact Or.inr (clos hgh _ _ hg1)
    · have hh1 : degreeOf (e (⟨0, hn⟩, ⟨0, hn⟩)) h = 1 := by omega
      exact Or.inl (clos (g := h) (h := g) (by rw [hgh, mul_comm]) _ _ hh1)

theorem gDet_prime (he : Function.Injective e) (hn : 0 < n) : Prime (gDet (K := K) e) := UniqueFactorizationMonoid.irreducible_iff_prime.mp (sp_gDet_irreducible he hn)

end Formalism.L2.KerInert.SharpPolyP.Det

namespace Formalism.L2.KerInert.SharpPolyP

open Formalism.L2.Ker Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.KerInert.SharpPolyP.Det

variable {ι : Type} [Fintype ι] {a : ℕ}

abbrev pt (x : ι → Matrix (Fin a) (Fin a) ℂ) : ι × Fin a × Fin a → ℂ := fun k => x k.1 k.2.1 k.2.2

abbrev unpt (y : ι × Fin a × Fin a → ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ α s => y (τ, α, s)

theorem sp_eval_frDet (x : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) : eval (pt x) (frDet ℂ a τ) = (x τ).det := by
  rw [frDet, RingHom.map_det]
  congr 1
  ext α s
  simp

theorem sp_density {R : Pol ℂ ι a}
    (h : ∀ x : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (x τ).det ≠ 0) → eval (pt x) R = 0) : R = 0 := by
  classical
  have hD : (∏ τ, frDet ℂ a τ : Pol ℂ ι a) ≠ 0 := by
    intro h0
    have := congrArg (eval (pt (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)))) h0
    rw [map_prod, map_zero] at this
    simp only [sp_eval_frDet, Matrix.det_one, Finset.prod_const_one] at this
    exact one_ne_zero this
  have hRD : R * ∏ τ, frDet ℂ a τ = 0 := by
    apply MvPolynomial.funext
    intro y
    change eval (pt (unpt y)) (R * ∏ τ, frDet ℂ a τ) = eval (pt (unpt y)) 0
    rw [map_zero, map_mul, map_prod]
    by_cases hinv : ∀ τ, (unpt y τ).det ≠ 0
    · rw [h _ hinv, zero_mul]
    · push Not at hinv
      obtain ⟨τ, hτ⟩ := hinv
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [sp_eval_frDet, hτ]), mul_zero]
  exact (mul_eq_zero.1 hRD).resolve_right hD

theorem sp_eval_colSub (β : ι → Matrix (Fin a) (Fin a) ℂ) (x : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ℂ ι a) :
    eval (pt x) (colSub β P) = eval (pt (fun τ => x τ * β τ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, map_mul]
    congr 1
    simp only [colSub, aeval_X, map_sum, map_mul, eval_C, eval_X]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem sp_det_bor {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (τ : ι) : (β τ).det = ∏ r, β τ r r :=
  Matrix.det_of_isUpperTriangular (fun r s hsr => (hβ τ).1 r s hsr)

theorem sp_bor_det_ne {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (τ : ι) : (β τ).det ≠ 0 := by
  rw [sp_det_bor hβ]
  exact Finset.prod_ne_zero_iff.2 fun r _ => (hβ τ).2 r

theorem sp_wt (ν : ι → Fin a → ℕ) (F : (ι → Matrix (Fin a) (Fin a) ℂ) → ℂ)
    (hF : ∀ x β, (∀ τ, (x τ).det ≠ 0) → IsBor β → F (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ ν τ r) * F x)
    (K : ι → ℕ) (P : Pol ℂ ι a)
    (hP : ∀ x, (∀ τ, (x τ).det ≠ 0) → eval (pt x) P = F x * ∏ τ, (x τ).det ^ K τ)
    (x β : ι → Matrix (Fin a) (Fin a) ℂ) (hβ : IsBor β) :
    eval (pt (fun τ => x τ * β τ)) P = (∏ τ, ∏ r, β τ r r ^ (ν τ r + K τ)) * eval (pt x) P := by
  have hpoly : colSub β P - C (∏ τ, ∏ r, β τ r r ^ (ν τ r + K τ)) * P = 0 := by
    apply sp_density
    intro y hy
    rw [map_sub, map_mul, eval_C, sp_eval_colSub]
    have hyb : ∀ τ, (y τ * β τ).det ≠ 0 := fun τ => by
      rw [Matrix.det_mul]; exact mul_ne_zero (hy τ) (sp_bor_det_ne hβ τ)
    rw [hP _ hyb, hP _ hy, hF y β hy hβ]
    simp only [Matrix.det_mul, sp_det_bor hβ, mul_pow, Finset.prod_mul_distrib, pow_add, ← Finset.prod_pow]
    ring
  have := congrArg (eval (pt x)) hpoly
  rw [map_sub, map_mul, eval_C, sp_eval_colSub, map_zero, sub_eq_zero] at this
  exact this

theorem sp_vanish (w : ι → Fin a → ℕ) (P : Pol ℂ ι a)
    (hw : ∀ x β, IsBor β → eval (pt (fun τ => x τ * β τ)) P = (∏ τ, ∏ r, β τ r r ^ w τ r) * eval (pt x) P)
    (τ0 : ι) (hpos : ∀ r, 1 ≤ w τ0 r) (x : ι → Matrix (Fin a) (Fin a) ℂ) (hx : (x τ0).det = 0) :
    eval (pt x) P = 0 := by
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hx
  have hS : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hne
    apply hv0
    funext i
    by_contra hi
    exact hne ⟨i, by simpa using hi⟩
  obtain ⟨k, hvk, hgt⟩ : ∃ k, v k ≠ 0 ∧ ∀ i, k < i → v i = 0 := by
    refine ⟨(Finset.univ.filter fun i => v i ≠ 0).max' hS, ?_, ?_⟩
    · have := Finset.max'_mem _ hS
      simpa using this
    · intro i hi
      by_contra h
      have : i ≤ (Finset.univ.filter fun i => v i ≠ 0).max' hS := Finset.le_max' _ i (by simp [h])
      exact absurd hi (not_lt.2 this)
  let bt : ℂ → ι → Matrix (Fin a) (Fin a) ℂ := fun t τ => Matrix.of fun r s =>
    if τ = τ0 then (if s = k then (if r = k then t else if r < k then t * v r / v k else 0) else if r = s then 1 else 0)
    else if r = s then 1 else 0
  have hbor : ∀ t, t ≠ 0 → IsBor (bt t) := by
    intro t ht τ
    constructor
    · intro r s hsr
      simp only [bt, Matrix.of_apply]
      split_ifs with h1 h2 h3 h4 h5 h6 <;>
        first
        | rfl
        | (exfalso; subst_vars; exact lt_irrefl _ hsr)
        | (exfalso; subst_vars; exact lt_asymm hsr (by assumption))
    · intro r
      simp only [bt, Matrix.of_apply]
      split_ifs <;> first | exact ht | exact one_ne_zero
  let M0 : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ0 then (Matrix.of fun α s => if s = k then 0 else x τ0 α s) else x τ
  have hcol : ∀ t, (fun τ => x τ * bt t τ) = M0 := by
    intro t
    funext τ
    ext α s
    rw [Matrix.mul_apply]
    by_cases hτ : τ = τ0
    · subst hτ
      simp only [M0, bt, Matrix.of_apply, ↓reduceIte]
      by_cases hs : s = k
      · subst hs
        simp only [↓reduceIte]
        have hterm : ∀ r, x τ α r * (if r = s then t else if r < s then t * v r / v s else 0) = (t / v s) * (x τ α r * v r) := by
          intro r
          by_cases h1 : r = s
          · rw [if_pos h1, h1]; field_simp
          · by_cases h2 : r < s
            · simp only [if_neg h1, if_pos h2]; field_simp
            · have : s < r := lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1)
              simp only [if_neg h1, if_neg h2, hgt r this]; ring
        rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.mul_sum]
        have := congrFun hv α
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        rw [this, mul_zero]
      · simp only [if_neg hs]
        rw [Finset.sum_eq_single s]
        · simp
        · intro r _ hr; simp [hr]
        · simp
    · simp only [M0, bt, if_neg hτ, Matrix.of_apply]
      rw [Finset.sum_eq_single s]
      · simp
      · intro r _ hr; simp [hr]
      · simp
  have hc : ∀ t, (∏ τ, ∏ r, bt t τ r r ^ w τ r) = t ^ w τ0 k := by
    intro t
    rw [Finset.prod_eq_single τ0]
    · rw [Finset.prod_eq_single k]
      · simp [bt, Matrix.of_apply]
      · intro r _ hr; simp [bt, Matrix.of_apply, hr]
      · simp
    · intro τ _ hτ; simp [bt, Matrix.of_apply, hτ]
    · simp
  have h1 := hw x (bt 1) (hbor 1 one_ne_zero)
  have h2 := hw x (bt 2) (hbor 2 two_ne_zero)
  rw [hcol 1, hc] at h1
  rw [hcol 2, hc, h1, one_pow, one_mul] at h2
  have hm : (2 : ℂ) ^ w τ0 k ≠ 1 := by
    intro h
    have h' : (2 : ℕ) ^ w τ0 k = 1 := by exact_mod_cast h
    rw [Nat.pow_eq_one] at h'
    have := hpos k
    omega
  have h3 : ((2 : ℂ) ^ w τ0 k - 1) * eval (pt x) P = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hm)

theorem sp_dvd (w : ι → Fin a → ℕ) (P : Pol ℂ ι a)
    (hw : ∀ x β, IsBor β → eval (pt (fun τ => x τ * β τ)) P = (∏ τ, ∏ r, β τ r r ^ w τ r) * eval (pt x) P)
    (τ0 : ι) (hpos : ∀ r, 1 ≤ w τ0 r) : frDet ℂ a τ0 ∣ P := by
  classical
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : frDet ℂ 0 τ0 = (1 : Pol ℂ ι 0) := by rw [frDet]; exact Matrix.det_isEmpty
    rw [this]
    exact one_dvd _
  · have hprime : Prime (frDet ℂ a τ0) :=
      gDet_prime (K := ℂ) (e := fun p : Fin a × Fin a => ((τ0, p.1, p.2) : ι × Fin a × Fin a))
        (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2) ha
    have hmem : P ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span {frDet ℂ a τ0}) : Set (ι × Fin a × Fin a → ℂ)) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      rw [mem_zeroLocus_iff] at hy
      have hd := hy _ (Ideal.mem_span_singleton_self _)
      change eval (pt (unpt y)) _ = 0 at hd
      change eval (pt (unpt y)) P = 0
      rw [sp_eval_frDet] at hd
      exact sp_vanish w P hw τ0 hpos _ hd
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    obtain ⟨m, hm⟩ := hmem
    rw [Ideal.mem_span_singleton] at hm
    exact hprime.dvd_of_dvd_pow hm

theorem sp_main (ν : ι → Fin a → ℕ) (F : (ι → Matrix (Fin a) (Fin a) ℂ) → ℂ)
    (hF : ∀ x β, (∀ τ, (x τ).det ≠ 0) → IsBor β → F (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ ν τ r) * F x) :
    ∀ (N : ℕ) (K : ι → ℕ) (P : Pol ℂ ι a), ∑ τ, K τ = N →
      (∀ x, (∀ τ, (x τ).det ≠ 0) → eval (pt x) P = F x * ∏ τ, (x τ).det ^ K τ) →
      ∃ Q : Pol ℂ ι a, ∀ x, (∀ τ, (x τ).det ≠ 0) → F x = eval (pt x) Q := by
  classical
  intro N
  induction N with
  | zero =>
    intro K P hK hP
    refine ⟨P, fun x hx => ?_⟩
    have hK0 : ∀ τ, K τ = 0 := fun τ => (Finset.sum_eq_zero_iff.1 hK) τ (Finset.mem_univ τ)
    rw [hP x hx]
    simp [hK0]
  | succ N ih =>
    intro K P hK hP
    obtain ⟨τ0, hτ0⟩ : ∃ τ0, 1 ≤ K τ0 := by
      by_contra h
      push Not at h
      have : ∑ τ, K τ = 0 := Finset.sum_eq_zero fun τ _ => by have := h τ; omega
      omega
    have hw := sp_wt ν F hF K P hP
    have hdvd := sp_dvd (fun τ r => ν τ r + K τ) P (fun x β hβ => hw x β hβ) τ0 (fun r => by omega)
    obtain ⟨P', rfl⟩ := hdvd
    apply ih (Function.update K τ0 (K τ0 - 1)) P'
    · have h1 := Finset.add_sum_erase Finset.univ K (Finset.mem_univ τ0)
      have h2 := Finset.add_sum_erase Finset.univ (Function.update K τ0 (K τ0 - 1)) (Finset.mem_univ τ0)
      have h3 : ∑ τ ∈ univ.erase τ0, Function.update K τ0 (K τ0 - 1) τ = ∑ τ ∈ univ.erase τ0, K τ :=
        Finset.sum_congr rfl fun τ hτ => Function.update_of_ne (Finset.ne_of_mem_erase hτ) _ _
      rw [Function.update_self] at h2
      omega
    · intro x hx
      have := hP x hx
      rw [map_mul, sp_eval_frDet] at this
      have hsplit : ∏ τ, (x τ).det ^ K τ = (x τ0).det * ∏ τ, (x τ).det ^ Function.update K τ0 (K τ0 - 1) τ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ0),
          ← Finset.mul_prod_erase _ (fun τ => (x τ).det ^ Function.update K τ0 (K τ0 - 1) τ) (Finset.mem_univ τ0)]
        have h3 : ∏ τ ∈ univ.erase τ0, (x τ).det ^ Function.update K τ0 (K τ0 - 1) τ = ∏ τ ∈ univ.erase τ0, (x τ).det ^ K τ :=
          Finset.prod_congr rfl fun τ hτ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
        rw [h3, Function.update_self, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hτ0]
      rw [hsplit] at this
      apply mul_left_cancel₀ (hx τ0)
      rw [this]
      ring

theorem sharp_polynomial_frames : SharpPoly := by
  classical
  intro ι _ a Y fr hfr lam sS ν hν f hf
  obtain ⟨⟨Q0, k, hQ0⟩, heq⟩ := hf
  have hinv : ∀ y τ, (fr y τ).det ≠ 0 := fun y => (hfr (fr y)).1 ⟨y, rfl⟩
  have hwd : ∀ y y₂, fr y₂ = fr y → f y₂ = f y := by
    intro y y₂ h
    have hb : IsBor (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)) := fun τ =>
      ⟨fun r s hsr => Matrix.one_apply_ne (ne_of_gt hsr), fun r => by simp⟩
    have := heq y y₂ (fun _ => 1) hb (fun τ => by rw [h, Matrix.mul_one])
    simpa using this
  let G : Y → ℂ := fun y => (∏ τ, (fr y τ).det ^ sS τ) * f y
  let Ft : (ι → Matrix (Fin a) (Fin a) ℂ) → ℂ := fun x => if h : ∃ y, fr y = x then G h.choose else 0
  have hFt : ∀ y, Ft (fr y) = G y := by
    intro y
    have h : ∃ y', fr y' = fr y := ⟨y, rfl⟩
    simp only [Ft, dif_pos h, G]
    rw [h.choose_spec, hwd y h.choose h.choose_spec]
  have hFt_wt : ∀ x β, (∀ τ, (x τ).det ≠ 0) → IsBor β →
      Ft (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ ν τ r) * Ft x := by
    intro x β hx hβ
    obtain ⟨y, rfl⟩ := (hfr x).2 hx
    have hxb : ∀ τ, (fr y τ * β τ).det ≠ 0 := fun τ => by
      rw [Matrix.det_mul]; exact mul_ne_zero (hinv y τ) (sp_bor_det_ne hβ τ)
    obtain ⟨y₂, hy₂⟩ := (hfr (fun τ => fr y τ * β τ)).2 hxb
    rw [← hy₂, hFt, hFt]
    simp only [G]
    rw [heq y y₂ β hβ (fun τ => by rw [hy₂])]
    have hdet : ∀ τ, (fr y₂ τ).det = (fr y τ).det * ∏ r, β τ r r := fun τ => by
      rw [hy₂, Matrix.det_mul, sp_det_bor hβ]
    simp only [hdet, mul_zpow]
    have key : ∀ τ, (∏ r, β τ r r) ^ sS τ * ∏ r, β τ r r ^ lam τ r = ∏ r, β τ r r ^ ν τ r := by
      intro τ
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← zpow_add₀ ((hβ τ).2 r), add_comm, hν τ r, zpow_natCast]
    simp only [← key, Finset.prod_mul_distrib]
    ring
  have hP : ∀ x, (∀ τ, (x τ).det ≠ 0) →
      eval (pt x) (Q0 * ∏ τ, frDet ℂ a τ ^ (sS τ).toNat) = Ft x * ∏ τ, (x τ).det ^ (k τ + (-sS τ).toNat) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hfr x).2 hx
    rw [hFt, map_mul, map_prod]
    simp only [map_pow, sp_eval_frDet, G]
    have hq' : eval (pt (fr y)) Q0 = f y * ∏ τ, (fr y τ).det ^ k τ := (hQ0 y).symm
    rw [hq']
    have key : ∀ τ, (fr y τ).det ^ k τ * (fr y τ).det ^ (sS τ).toNat =
        (fr y τ).det ^ sS τ * (fr y τ).det ^ (k τ + (-sS τ).toNat) := by
      intro τ
      have hd := hinv y τ
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hd, ← zpow_add₀ hd]
      congr 1
      have := Int.toNat_sub_toNat_neg (sS τ)
      push_cast
      omega
    calc f y * (∏ τ, (fr y τ).det ^ k τ) * ∏ τ, (fr y τ).det ^ (sS τ).toNat
        = f y * ∏ τ, ((fr y τ).det ^ k τ * (fr y τ).det ^ (sS τ).toNat) := by
          rw [Finset.prod_mul_distrib, mul_assoc]
      _ = f y * ∏ τ, ((fr y τ).det ^ sS τ * (fr y τ).det ^ (k τ + (-sS τ).toNat)) := by simp only [key]
      _ = _ := by rw [Finset.prod_mul_distrib]; ring
  obtain ⟨Q, hQ⟩ := sp_main ν Ft hFt_wt _ (fun τ => k τ + (-sS τ).toNat) _ rfl hP
  refine ⟨Q, ?_⟩
  funext y
  have := hQ (fr y) (hinv y)
  rw [hFt] at this
  exact this

end Formalism.L2.KerInert.SharpPolyP
