import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

noncomputable section

namespace UpperTheory.V.Alg.M.NumericalFunctions

private def sh : Multiplicative (ℤ × ℤ) →* Module.End ℤ (ℤ × ℤ → ℤ) where
  toFun v := LinearMap.funLeft ℤ ℤ (fun p => p - v.toAdd)
  map_one' := by ext f p; simp [LinearMap.funLeft]
  map_mul' v w := by
    refine LinearMap.ext fun f => funext fun p => ?_
    simp [LinearMap.funLeft, sub_sub]

private def φ : AddMonoidAlgebra ℤ (ℤ × ℤ) →ₐ[ℤ] Module.End ℤ (ℤ × ℤ → ℤ) :=
  AddMonoidAlgebra.lift ℤ _ _ sh

private def x (v : ℤ × ℤ) : AddMonoidAlgebra ℤ (ℤ × ℤ) := AddMonoidAlgebra.single v 1

private theorem x_add (v w : ℤ × ℤ) : x (v + w) = x v * x w := by
  simp [x, AddMonoidAlgebra.single_mul_single]

private theorem frobenius_inclusion_X_eq_mul_Q (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (x v) f p = f (p - v) := by
  simp [φ, x, sh, LinearMap.funLeft]

private theorem φ_mul (a b : AddMonoidAlgebra ℤ (ℤ × ℤ)) (f : ℤ × ℤ → ℤ) : φ (a * b) f = φ a (φ b f) := by
  rw [map_mul]; rfl

private theorem φ_sub (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (1 - x v) f p = f p - f (p - v) := by
  rw [map_sub, map_one, LinearMap.sub_apply, Pi.sub_apply, frobenius_inclusion_X_eq_mul_Q]; rfl

private theorem φ_add (v : ℤ × ℤ) (f : ℤ × ℤ → ℤ) (p : ℤ × ℤ) : φ (1 + x v) f p = f p + f (p - v) := by
  rw [map_add, map_one, LinearMap.add_apply, Pi.add_apply, frobenius_inclusion_X_eq_mul_Q]; rfl

private theorem one_sub_x_ne {v : ℤ × ℤ} (hv : v ≠ 0) : 1 - x v ≠ 0 := by
  intro h
  have := φ_sub v (fun q => if q = 0 then 1 else 0) 0
  simp [h, hv] at this

private theorem dif_eq {k : ℕ} (l : Deg k →+ ℤ × ℤ) (f : ℤ × ℤ → ℤ) (L : List (Deg k)) (d : Deg k) :
    dif L (fun d => f (l d)) d = φ (L.map fun v => 1 - x (l v)).prod f (l d) := by
  induction L generalizing d with
  | nil => simp [dif]
  | cons v L ih => rw [dif, List.map_cons, List.prod_cons, φ_mul, φ_sub, ih, ih, map_sub]

private theorem ev_sub {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) :
    ∀ᶠ p in atTop, f (p - v) = c := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 h
  exact eventually_atTop.2 ⟨a + v, fun p hp => ha _ (le_sub_iff_add_le.2 hp)⟩

private theorem eventually_const_of_shift {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) :
    ∀ᶠ p in atTop, φ (x v) f p = c := by
  simpa only [frobenius_inclusion_X_eq_mul_Q] using ev_sub h v

private theorem ev_pow {f : ℤ × ℤ → ℤ} {c : ℤ} (h : ∀ᶠ p in atTop, f p = c) (v : ℤ × ℤ) (n : ℕ) :
    ∀ᶠ p in atTop, φ ((1 + x v) ^ n) f p = 2 ^ n * c := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    filter_upwards [ih, ev_sub ih v] with p h1 h2
    rw [pow_succ', φ_mul, φ_add, h1, h2]; ring

private def mons {τ : Type} (w : τ → ℤ × ℤ) (S : Finset τ) (p : ℤ × ℤ) : Set (τ →₀ ℕ) :=
  {ν | (∀ j ∉ S, ν j = 0) ∧ Finsupp.weight w ν = p}

private def N {τ : Type} (w : τ → ℤ × ℤ) (S : Finset τ) (p : ℤ × ℤ) : ℤ := (mons w S p).ncard

private theorem N_insert {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (S : Finset τ) (i : τ) (hi : i ∉ S) : φ (1 - x (w i)) (N w (insert i S)) = N w S := by
  funext p
  have h : mons w (insert i S) p =
      mons w S p ∪ (fun ν => ν + Finsupp.single i 1) '' mons w (insert i S) (p - w i) := by
    ext ν
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h0 : ν i = 0
      · left
        refine ⟨fun j hj => ?_, h2⟩
        by_cases hji : j = i
        · rw [hji, h0]
        · exact h1 j (by simp [hj, hji])
      · right
        have e1 : ν - Finsupp.single i 1 + Finsupp.single i 1 = ν :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))
        refine ⟨ν - Finsupp.single i 1, ⟨fun j hj => by simp [h1 j hj], ?_⟩, e1⟩
        rw [← h2]
        conv_rhs => rw [← e1, map_add, Finsupp.weight_single, one_smul, add_sub_cancel_right]
    · rintro (⟨h1, h2⟩ | ⟨μ, ⟨h1, h2⟩, rfl⟩)
      · exact ⟨fun j hj => h1 j (fun h => hj (by simp [h])), h2⟩
      · refine ⟨fun j hj => ?_, by simp [map_add, Finsupp.weight_single, h2]⟩
        have : i ≠ j := by rintro rfl; simp at hj
        simp [h1 j hj, this]
  rw [φ_sub, N, N, N, h, Set.ncard_union_eq _ (hfin _ _) ((hfin _ _).image _),
    Set.ncard_image_of_injective _ (add_left_injective _)]
  · push_cast; ring
  · rw [Set.disjoint_left]
    rintro ν ⟨h1, -⟩ ⟨μ, -, rfl⟩
    simpa using h1 i hi

private theorem N_prod {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (T U : Finset τ) (h : Disjoint U T) : φ (∏ i ∈ U, (1 - x (w i))) (N w (U ∪ T)) = N w T := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    rw [Finset.disjoint_insert_left] at h
    rw [Finset.prod_insert hi, mul_comm, φ_mul, Finset.insert_union, N_insert w hfin _ _ (by simp [hi, h.1]), ih h.2]

private theorem weight_pair {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hij : i ≠ j) (ν : τ →₀ ℕ)
    (h : ∀ k ∉ ({i, j} : Finset τ), ν k = 0) : Finsupp.weight w ν = ν i • w i + ν j • w j := by
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset (s := {i, j}), Finset.sum_pair hij]
  · intro k hk
    by_contra hk'
    exact Finsupp.mem_support_iff.1 hk (h k hk')
  · simp

private theorem N_one {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hi : w i = (1, 0)) (hj : w j = (0, 1)) :
    ∀ᶠ p in atTop, N w {i, j} p = 1 := by
  have hij : i ≠ j := by rintro rfl; simp [hi] at hj
  filter_upwards [eventually_ge_atTop (0 : ℤ × ℤ)] with p hp
  obtain ⟨a, b⟩ := p
  obtain ⟨ha, hb⟩ : 0 ≤ a ∧ 0 ≤ b := hp
  lift a to ℕ using ha
  lift b to ℕ using hb
  have : mons w {i, j} (a, b) = {Finsupp.single i a + Finsupp.single j b} := by
    ext ν
    constructor
    · rintro ⟨h1, h2⟩
      rw [weight_pair w hij ν h1, hi, hj] at h2
      simp at h2
      ext k
      by_cases hki : k = i
      · simp [hki, hij, h2.1]
      by_cases hkj : k = j
      · simp [hkj, hij, h2.2]
      simp [h1 k (by simp [hki, hkj]), hki, hkj]
    · rintro rfl
      refine ⟨fun k hk => ?_, by simp [map_add, Finsupp.weight_single, hi, hj]⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hk.1, hk.2]
  simp [N, this]

private theorem N_zero {τ : Type} [DecidableEq τ] (w : τ → ℤ × ℤ) {i j : τ} (hi : w i = (0, 1)) (hj : w j = (0, 2)) :
    ∀ᶠ p in atTop, N w {i, j} p = 0 := by
  have hij : i ≠ j := by rintro rfl; simp [hi] at hj
  filter_upwards [eventually_ge_atTop ((1, 1) : ℤ × ℤ)] with p hp
  have : mons w {i, j} p = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ν ⟨h1, h2⟩
    rw [weight_pair w hij ν h1, hi, hj] at h2
    have := hp.1
    rw [← h2] at this
    simp at this
  simp [N, this]

private theorem key {τ : Type} [Fintype τ] [DecidableEq τ] (w : τ → ℤ × ℤ) (hfin : ∀ S p, (mons w S p).Finite)
    (r s r' s' : ℕ) {i₀ i₁ i₂ : τ} (h₀ : w i₀ = (1, 0)) (h₁ : w i₁ = (0, 1)) (h₂ : w i₂ = (0, 2))
    (hP : ∏ i, (1 - x (w i)) =
      (1 - x (1, 0)) ^ (r + 1) * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ (r' + 1) * (1 - x (0, 2)) ^ (s' + 1)) :
    ∀ᶠ p in atTop, φ ((1 - x (2, 0)) ^ r * ((1 - x (2, 0)) ^ s * (1 - x (0, 2)) ^ r' * (1 - x (0, 2)) ^ s' *
      (1 - x (4, 2)))) (N w Finset.univ) p = 2 ^ (r + r') := by
  have h01 : i₀ ≠ i₁ := by rintro rfl; simp [h₀] at h₁
  have h12 : i₁ ≠ i₂ := by rintro rfl; simp [h₁] at h₂
  set C := (1 - x (1, 0)) ^ r * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ r' * (1 - x (0, 2)) ^ s' with hC
  have hT : ∀ T : Finset τ, φ (∏ i ∈ Tᶜ, (1 - x (w i))) (N w Finset.univ) = N w T := fun T => by
    rw [← N_prod w hfin T Tᶜ disjoint_compl_left, Finset.union_comm, Finset.union_compl]
  have nX : 1 - x (1, 0) ≠ 0 := one_sub_x_ne (by simp)
  have nY : 1 - x (0, 1) ≠ 0 := one_sub_x_ne (by simp)
  have nY2 : 1 - x (0, 2) ≠ 0 := one_sub_x_ne (by simp)
  have e1 : ∏ i ∈ ({i₀, i₁} : Finset τ)ᶜ, (1 - x (w i)) = C * (1 - x (0, 2)) := by
    apply mul_right_cancel₀ (mul_ne_zero nX nY)
    have := Finset.prod_compl_mul_prod ({i₀, i₁} : Finset τ) (fun i => 1 - x (w i))
    rw [Finset.prod_pair h01, h₀, h₁] at this
    rw [this, hP, hC]; ring
  have e2 : ∏ i ∈ ({i₁, i₂} : Finset τ)ᶜ, (1 - x (w i)) = C * (1 - x (1, 0)) := by
    apply mul_right_cancel₀ (mul_ne_zero nY nY2)
    have := Finset.prod_compl_mul_prod ({i₁, i₂} : Finset τ) (fun i => 1 - x (w i))
    rw [Finset.prod_pair h12, h₁, h₂] at this
    rw [this, hP, hC]; ring
  have hX2 : 1 - x (2, 0) = (1 + x (1, 0)) * (1 - x (1, 0)) := by
    rw [show ((2, 0) : ℤ × ℤ) = (1, 0) + (1, 0) from rfl, x_add]; ring
  have hY2 : 1 - x (0, 2) = (1 + x (0, 1)) * (1 - x (0, 1)) := by
    rw [show ((0, 2) : ℤ × ℤ) = (0, 1) + (0, 1) from rfl, x_add]; ring
  have h42 : 1 - x (4, 2) = (1 - x (0, 2)) + x (0, 2) * (1 + x (2, 0)) * ((1 + x (1, 0)) * (1 - x (1, 0))) := by
    rw [← hX2, show ((4, 2) : ℤ × ℤ) = (2, 0) + (2, 0) + (0, 2) from rfl, x_add, x_add]; ring
  have hop : (1 - x (2, 0)) ^ r * ((1 - x (2, 0)) ^ s * (1 - x (0, 2)) ^ r' * (1 - x (0, 2)) ^ s' * (1 - x (4, 2))) =
      (1 + x (1, 0)) ^ r * ((1 + x (0, 1)) ^ r' * (C * (1 - x (0, 2)) +
        x (0, 2) * ((1 + x (2, 0)) ^ 1 * ((1 + x (1, 0)) ^ 1 * (C * (1 - x (1, 0))))))) := by
    have a1 : (1 - x (2, 0)) ^ r = (1 + x (1, 0)) ^ r * (1 - x (1, 0)) ^ r := by rw [hX2, mul_pow]
    have a2 : (1 - x (0, 2)) ^ r' = (1 + x (0, 1)) ^ r' * (1 - x (0, 1)) ^ r' := by rw [hY2, mul_pow]
    rw [a1, a2, h42, hC]; ring
  rw [hop, φ_mul, φ_mul, pow_add, ← mul_one (2 ^ r')]
  refine ev_pow (ev_pow ?_ _ _) _ _
  rw [map_add, LinearMap.add_apply, ← e1, ← e2, φ_mul, φ_mul, φ_mul, hT, hT]
  filter_upwards [N_one w h₀ h₁, eventually_const_of_shift (ev_pow (ev_pow (N_zero w h₁ h₂) (1, 0) 1) (2, 0) 1) (0, 2)] with p a1 a2
  rw [Pi.add_apply, a1, a2]; simp

private def lam : Deg 3 →+ ℤ × ℤ where
  toFun d := (2 * d 0 + 4 * d 2, 2 * d 1 + 2 * d 2)
  map_zero' := by simp
  map_add' a b := by ext <;> simp <;> ring

end UpperTheory.V.Alg.M.NumericalFunctions

open UpperTheory.V.Alg.M.NumericalFunctions in
theorem UpperTheory.V.Alg.M.num_holds :
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (r s r' s' : ℕ), 1 ≤ r → (∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j) →
      ∀ᶠ d in atTop, dif (List.replicate (r - 1) (e 0) ++ (List.replicate s (e 0) ++ List.replicate r' (e 1) ++
          List.replicate s' (e 1) ++ [e 2])) (fun d : Deg 3 => cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2)) d = 2 ^ (r - 1 + r') := by
  intro τ _ wt r s r' s' hr hc
  classical
  obtain ⟨r, rfl⟩ : ∃ r₀, r = r₀ + 1 := ⟨r - 1, by omega⟩
  have hc' : ∀ j, (Finset.univ.filter fun i => wt i = j).card = mDims (r + 1) s r' s' 0 j := fun j => by
    rw [← hc j, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hex : ∀ j, mDims (r + 1) s r' s' 0 j ≠ 0 → ∃ i, wt i = j := fun j hj => by
    rw [← hc'] at hj
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.1 hj
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  have hwt : ∀ i, wt i ∈ ({-1, -2, 1, 2} : Finset ℤ) := fun i => by
    by_contra h
    have : (Finset.univ.filter fun i' => wt i' = wt i).card ≠ 0 := Finset.card_ne_zero.2 ⟨i, by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    rw [hc'] at this
    simp [mDims, h] at this
  let w : τ → ℤ × ℤ := fun i => ((negW wt i : ℤ), (posW wt i : ℤ))
  have hw : ∀ ν : τ →₀ ℕ, Finsupp.weight w ν =
      (((Finsupp.weight (negW wt) ν : ℕ) : ℤ), ((Finsupp.weight (posW wt) ν : ℕ) : ℤ)) := fun ν => by
    induction ν using Finsupp.induction_linear with
    | zero => simp [Prod.ext_iff]
    | add a b ha hb => simp [map_add, ha, hb]
    | single i n => simp [Finsupp.weight_single, w]
  have hfin : ∀ S p, (mons w S p).Finite := fun S p => by
    refine (Finsupp.finite_of_nat_weight_le (fun i => negW wt i + posW wt i) (fun i => ?_)
      (p.1.toNat + p.2.toNat)).subset ?_
    · have := hwt i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      simp only [negW, posW]; omega
    · rintro ν ⟨-, rfl⟩
      have : Finsupp.weight (fun i => negW wt i + posW wt i) ν =
          Finsupp.weight (negW wt) ν + Finsupp.weight (posW wt) ν := by
        simp [Finsupp.weight_apply, Finsupp.sum, mul_add, Finset.sum_add_distrib]
      simp [hw, this]
  have hcnt : (fun d : Deg 3 => cnt wt (2 * d 0 + 4 * d 2) (2 * d 1 + 2 * d 2)) =
      fun d => N w Finset.univ (lam d) := by
    funext d
    rw [cnt, N, ← Nat.card_coe_set_eq]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun ν => ?_)
    simp [mons, hw, lam]
  obtain ⟨i₀, h₀⟩ := hex (-1) (by simp [mDims])
  obtain ⟨i₁, h₁⟩ := hex 1 (by simp [mDims])
  obtain ⟨i₂, h₂⟩ := hex 2 (by simp [mDims])
  have hP : ∏ i, (1 - x (w i)) =
      (1 - x (1, 0)) ^ (r + 1) * (1 - x (2, 0)) ^ s * (1 - x (0, 1)) ^ (r' + 1) * (1 - x (0, 2)) ^ (s' + 1) := by
    rw [← Finset.prod_fiberwise_of_maps_to (fun i _ => hwt i)]
    have : ∀ j : ℤ, ∏ i ∈ Finset.univ.filter (fun i => wt i = j), (1 - x (w i)) =
        (1 - x (((-j).toNat : ℤ), (j.toNat : ℤ))) ^ mDims (r + 1) s r' s' 0 j := fun j => by
      rw [← hc', ← Finset.prod_const]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [← (Finset.mem_filter.1 hi).2]; rfl
    simp only [this]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide),
      mul_assoc, mul_assoc]
    rfl
  have hk := key w hfin r s r' s' (i₀ := i₀) (i₁ := i₁) (i₂ := i₂) (by simp [w, negW, posW, h₀])
    (by simp [w, negW, posW, h₁]) (by simp [w, negW, posW, h₂]) hP
  have l0 : lam (e 0) = (2, 0) := by simp [lam, e]
  have l1 : lam (e 1) = (0, 2) := by simp [lam, e]
  have l2 : lam (e 2) = (4, 2) := by simp [lam, e]
  obtain ⟨a, ha⟩ := eventually_atTop.1 hk
  filter_upwards [eventually_ge_atTop (fun _ => |a.1| + |a.2| : Deg 3)] with d hd
  rw [hcnt, dif_eq]
  simp only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, l0, l1, l2, Nat.add_sub_cancel]
  refine ha _ ?_
  have d0 : |a.1| + |a.2| ≤ d 0 := hd 0
  have d1 : |a.1| + |a.2| ≤ d 1 := hd 1
  have d2 : |a.1| + |a.2| ≤ d 2 := hd 2
  have := le_abs_self a.1
  have := le_abs_self a.2
  have := abs_nonneg a.1
  have := abs_nonneg a.2
  exact ⟨show a.1 ≤ 2 * d 0 + 4 * d 2 by linarith, show a.2 ≤ 2 * d 1 + 2 * d 2 by linarith⟩
