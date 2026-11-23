import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem second_cohomology_transfer {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (H V : Subgroup Γ) [V.Normal] (hVH : V ≤ H) (hVρ : V ≤ ρ.ker)
    (hH : (H.index : k) ≠ 0) (κ : Γ × Γ → M)
    (hκ : ∀ s t u, ρ s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t))
    (h1 : ∀ s t, ∀ v ∈ V, κ (s * v, t) = κ (s, t)) (h2 : ∀ s t, ∀ v ∈ V, κ (s, t * v) = κ (s, t))
    (a0 : Γ → M) (ha : ∀ s, ∀ v ∈ V, a0 (s * v) = a0 s)
    (hd : ∀ s ∈ H, ∀ t ∈ H, a0 (s * t) = a0 s + ρ s (a0 t) - κ (s, t)) :
    ∃ a : Γ → M, (∀ s, ∀ v ∈ V, a (s * v) = a s) ∧ dOne ρ a = κ := by
  classical
  have hfi : H.FiniteIndex := ⟨fun h => hH (by rw [h, Nat.cast_zero])⟩
  letI : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  let σ : Γ → Γ := fun g => (QuotientGroup.mk g : Γ ⧸ H).out
  have hσ : ∀ g, (σ g)⁻¹ * g ∈ H := fun g => QuotientGroup.eq.1 (Quotient.out_eq _)
  have hσh : ∀ g, ∀ h ∈ H, σ (g * h) = σ g := fun g h hh => by
    simp only [σ, QuotientGroup.mk_mul_of_mem g hh]
  let f : Γ → M := fun g => κ (σ g, (σ g)⁻¹ * g) - ρ (σ g) (a0 ((σ g)⁻¹ * g))
  have hf : ∀ g, ∀ h ∈ H, f (g * h) = f g - ρ g (a0 h) + κ (g, h) := by
    intro g h hh
    simp only [f, hσh g h hh]
    have e := hκ (σ g) ((σ g)⁻¹ * g) h
    have e2 : ρ (σ g) (ρ ((σ g)⁻¹ * g) (a0 h)) = ρ g (a0 h) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [mul_inv_cancel_left] at e
    rw [← mul_assoc, hd _ (hσ g) h hh, map_sub, map_add, e2, eq_sub_of_add_eq' e]
    abel
  have hfv : ∀ g, ∀ v ∈ V, f (g * v) = f g := by
    intro g v hv
    simp only [f, hσh g v (hVH hv)]
    rw [← mul_assoc, h2 _ _ v hv, ha _ v hv]
  let D : Γ → Γ → M := fun s g => ρ s (f g) + κ (s, g) - f (s * g)
  have hD : ∀ s t g, ρ s (D t g) + D s (t * g) = κ (s, t) + D (s * t) g := by
    intro s t g
    simp only [D, map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]
    rw [eq_sub_of_add_eq (hκ s t g)]
    abel
  have hDh : ∀ s g, ∀ h ∈ H, D s (g * h) = D s g := by
    intro s g h hh
    simp only [D]
    rw [← mul_assoc, hf g h hh, hf _ h hh]
    simp only [map_sub, map_add, map_mul, Module.End.mul_apply]
    rw [eq_sub_of_add_eq (hκ s g h)]
    abel
  have hDσ : ∀ s g, D s (σ g) = D s g := by
    intro s g
    rw [← hDh s (σ g) _ (hσ g), mul_inv_cancel_left]
  have hDv : ∀ s g, ∀ v ∈ V, D (s * v) g = D s g := by
    intro s g v hv
    simp only [D]
    have e : s * v * g = s * g * (g⁻¹ * v * g) := by group
    have hv' : g⁻¹ * v * g ∈ V := by simpa using (‹V.Normal›.conj_mem v hv g⁻¹)
    have hρ : ρ v = 1 := hVρ hv
    rw [e, hfv _ _ hv', h1 _ _ v hv, map_mul, hρ, mul_one]
  let A : Γ → M := fun s => ∑ x : Γ ⧸ H, D s x.out
  have hA : ∀ s t, A s + ρ s (A t) - A (s * t) = (H.index : k) • κ (s, t) := by
    intro s t
    have e1 : A s = ∑ x : Γ ⧸ H, D s (t * x.out) := by
      simp only [A]
      rw [← Equiv.sum_comp (MulAction.toPerm t)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hDσ s (t * x.out)]
      have : (QuotientGroup.mk (t * x.out) : Γ ⧸ H) = t • x := MulAction.Quotient.mk_smul_out H t x
      simp only [σ, this, MulAction.toPerm_apply]
    rw [e1]
    simp only [A, map_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => κ (s, t)) (fun x _ => by rw [add_comm, hD]; abel)]
    rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  refine ⟨fun s => (H.index : k)⁻¹ • A s, fun s v hv => ?_, ?_⟩
  · simp only [A, hDv _ _ v hv]
  · funext ⟨s, t⟩
    simp only [dOne, map_smul, ← smul_add, ← smul_sub, hA, smul_smul, inv_mul_cancel₀ hH, one_smul]

private def cocycleTrivializationOnPowers {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (κ : Γ × Γ → M) (x : Γ) : ℕ → M
  | 0 => κ (1, 1)
  | n + 1 => ρ x (cocycleTrivializationOnPowers ρ κ x n) - κ (x, x ^ n)

private theorem cocycle_sequence_add {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (κ : Γ × Γ → M)
    (hκ : ∀ s t u, ρ s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) (x : Γ) (i j : ℕ) :
    cocycleTrivializationOnPowers ρ κ x (i + j) = cocycleTrivializationOnPowers ρ κ x i + ρ (x ^ i) (cocycleTrivializationOnPowers ρ κ x j) - κ (x ^ i, x ^ j) := by
  induction i with
  | zero =>
    have e := hκ 1 1 (x ^ j)
    simp only [map_one, Module.End.one_apply, one_mul, add_right_inj] at e
    simp [cocycleTrivializationOnPowers, e]
  | succ i ih =>
    rw [show i + 1 + j = (i + j) + 1 by ring]
    simp only [cocycleTrivializationOnPowers, ih, map_sub, map_add, pow_succ', map_mul, Module.End.mul_apply, pow_add]
    rw [eq_sub_of_add_eq (hκ x (x ^ i) (x ^ j))]
    abel

private theorem cocycle_sequence_periodic {l : ℕ} {k Γ M : Type} [Field k] [CharP k l] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (κ : Γ × Γ → M)
    (hκ : ∀ s t u, ρ s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) (x : Γ) (r : ℕ)
    (hρ : ρ (x ^ r) = 1) (hr : ∀ t, κ (x ^ r, t) = κ (1, t)) (i j : ℕ) (hij : i ≡ j [MOD r * l]) :
    cocycleTrivializationOnPowers ρ κ x i = cocycleTrivializationOnPowers ρ κ x j := by
  have e1 : ∀ t, κ (1, t) = κ (1, 1) := fun t => by
    have e := hκ 1 1 t
    simpa using e
  have e2 : ∀ n j, cocycleTrivializationOnPowers ρ κ x (r * n + j) = n • (cocycleTrivializationOnPowers ρ κ x r - κ (1, 1)) + cocycleTrivializationOnPowers ρ κ x j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show r * (n + 1) + j = r + (r * n + j) by ring, cocycle_sequence_add ρ κ hκ, hρ, hr, e1, Module.End.one_apply, ih,
        succ_nsmul]
      abel
  have e3 : ∀ j, cocycleTrivializationOnPowers ρ κ x j = cocycleTrivializationOnPowers ρ κ x (j % (r * l)) := by
    intro j
    conv_lhs => rw [← Nat.div_add_mod j (r * l), mul_assoc, e2]
    rw [← Nat.cast_smul_eq_nsmul k, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul, zero_add]
  rw [e3 i, e3 j, hij]

theorem UpperTheory.V.Alg.exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia :
    ∀ (l : ℕ) [Fact l.Prime] (k Γ M : Type) [Field k] [CharP k l] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ] [AddCommGroup M] [Module k M] [Finite M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (I N : Subgroup Γ) [I.Normal] [N.Normal], IsClosed (I : Set Γ) → IsClosed (N : Set Γ) → N ≤ I → N ≤ ρ.ker → ¬ l ∣ N.relIndex I →
      (∃ fr : Γ, (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) → (∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n) →
      ∀ κ : Γ × Γ → M, IsLocallyConstant κ → (∀ s t u, ρ s (κ (t, u)) + κ (s, t * u) = κ (s * t, u) + κ (s, t)) → (∀ s t, ∀ n ∈ N, ∀ n' ∈ N, κ (s * n, t * n') = κ (s, t)) →
      ∃ a : Γ → M, IsLocallyConstant a ∧ (∀ s, ∀ n ∈ N, a (s * n) = a s) ∧ dOne ρ a = κ := by
  intro l hl k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hker I N _ _ _ _ hNI hNρ hidx ⟨fr, hfr⟩ hU κ hκc hκ hκN
  classical
  have core : ∀ W : Subgroup Γ, IsOpen (W : Set Γ) → IsOpen (W.normalCore : Set Γ) := by
    intro W hW
    haveI : Finite (Γ ⧸ W) := W.quotient_finite_of_isOpen hW
    haveI : W.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (W.normalCore_isClosed (W.isClosed_of_isOpen hW))
  have gen : ∀ W : Subgroup Γ, IsOpen (W : Set Γ) → I ≤ W → fr ∈ W → W = ⊤ := by
    intro W hW h1 h2
    rw [eq_top_iff, ← hfr]
    exact Subgroup.topologicalClosure_minimal _ (sup_le h1 ((Subgroup.zpowers_le).2 h2)) (W.isClosed_of_isOpen hW)
  let V0 : Subgroup Γ :=
    { carrier := {v | ∀ s t, κ (s * v, t) = κ (s, t) ∧ κ (s, t * v) = κ (s, t)}
      mul_mem' := fun {a b} ha hb s t => by
        rw [← mul_assoc, ← mul_assoc, (hb _ _).1, (hb _ _).2]; exact ha s t
      one_mem' := fun s t => by simp
      inv_mem' := fun {a} ha s t => by
        rw [← (ha _ _).1, ← (ha s (t * a⁻¹)).2]; simp }
  have hV0 : IsOpen (V0 : Set Γ) := by
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    have := (isCompact_univ (X := Γ × Γ)).eventually_forall_of_forall_eventually (x₀ := (1 : Γ))
      (P := fun v p => κ (p.1 * v, p.2) = κ p ∧ κ (p.1, p.2 * v) = κ p) (by
        intro p _
        have c1 := (hκc.comp_continuous (f := fun z : Γ × Γ × Γ => (z.2.1 * z.1, z.2.2)) (by fun_prop)).eventually_eq (1, p)
        have c2 := (hκc.comp_continuous (f := fun z : Γ × Γ × Γ => (z.2.1, z.2.2 * z.1)) (by fun_prop)).eventually_eq (1, p)
        have c3 := (hκc.comp_continuous (f := fun z : Γ × Γ × Γ => z.2) (by fun_prop)).eventually_eq (1, p)
        filter_upwards [c1, c2, c3] with z z1 z2 z3
        simp only [Function.comp, mul_one] at z1 z2 z3
        exact ⟨z1.trans z3.symm, z2.trans z3.symm⟩)
    filter_upwards [this] with v hv s t using hv (s, t) trivial
  have hNV0 : N ≤ V0 := fun n hn s t =>
    ⟨by simpa using hκN s t n hn 1 N.one_mem, by simpa using hκN s t 1 N.one_mem n hn⟩
  let V1 : Subgroup Γ := (V0 ⊓ ρ.ker).normalCore
  have hV1 : IsOpen (V1 : Set Γ) := core _ (hV0.inter hker)
  have hV1le : V1 ≤ V0 ⊓ ρ.ker := Subgroup.normalCore_le _
  have hNV1 : N ≤ V1 := Subgroup.normal_le_normalCore.2 (le_inf hNV0 hNρ)
  haveI : Finite (Γ ⧸ V1) := V1.quotient_finite_of_isOpen hV1
  let r := orderOf (fr : Γ ⧸ V1)
  have hr0 : r ≠ 0 := (orderOf_pos _).ne'
  have hfrr : fr ^ r ∈ V1 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
  obtain ⟨e, m, hm, hrm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr0 l hl.out.ne_one
  obtain ⟨U, hUo, hIU, hUi⟩ := hU (e + 1)
  let U1 := U.normalCore
  have hU1 : IsOpen (U1 : Set Γ) := core _ hUo
  have hIU1 : I ≤ U1 := Subgroup.normal_le_normalCore.2 hIU
  have hord : l ^ (e + 1) ∣ orderOf (fr : Γ ⧸ U1) := by
    have ht : (Subgroup.zpowers (fr : Γ ⧸ U1)).comap (QuotientGroup.mk' U1) = ⊤ := by
      have hle : U1 ≤ (Subgroup.zpowers (fr : Γ ⧸ U1)).comap (QuotientGroup.mk' U1) := fun u hu => by
        have : (QuotientGroup.mk' U1) u = 1 := (QuotientGroup.eq_one_iff u).2 hu
        rw [Subgroup.mem_comap, this]; exact Subgroup.one_mem _
      exact gen _ (Subgroup.isOpen_mono hle hU1) (hIU1.trans hle) (Subgroup.mem_zpowers _)
    have ht' : Subgroup.zpowers (fr : Γ ⧸ U1) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      have : y ∈ (Subgroup.zpowers (fr : Γ ⧸ U1)).comap (QuotientGroup.mk' U1) := by rw [ht]; trivial
      exact this
    rw [← Nat.card_zpowers, ht', Subgroup.card_top, ← hUi]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le U)
  let V : Subgroup Γ := V1 ⊓ U1
  have hV : IsOpen (V : Set Γ) := hV1.inter hU1
  have hNV : N ≤ V := le_inf hNV1 (hNI.trans hIU1)
  haveI : Finite (Γ ⧸ V) := V.quotient_finite_of_isOpen hV
  have hVV0 : V ≤ V0 := inf_le_left.trans (hV1le.trans inf_le_left)
  have hVρ : V ≤ ρ.ker := inf_le_left.trans (hV1le.trans inf_le_right)
  have wd : ∀ i j : ℕ, ((fr ^ i : Γ) : Γ ⧸ V) = (fr ^ j : Γ) → cocycleTrivializationOnPowers ρ κ fr i = cocycleTrivializationOnPowers ρ κ fr j := by
    intro i j hij
    have hij' := QuotientGroup.eq.1 hij
    have m1 : i ≡ j [MOD r] := by
      rw [← pow_eq_pow_iff_modEq, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow]
      exact QuotientGroup.eq.2 hij'.1
    have m2 : i ≡ j [MOD l ^ (e + 1)] := by
      refine Nat.ModEq.of_dvd hord ?_
      rw [← pow_eq_pow_iff_modEq, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow]
      exact QuotientGroup.eq.2 hij'.2
    refine cocycle_sequence_periodic ρ κ hκ fr r (hV1le hfrr).2 (fun t => ?_) i j ?_
    · simpa using ((hV1le hfrr).1 1 t).1
    · have cop : Nat.Coprime (l ^ (e + 1)) m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)
      rw [show r * l = l ^ (e + 1) * m by rw [hrm]; ring]
      exact (Nat.modEq_and_modEq_iff_modEq_mul cop).1 ⟨m2, m1.of_dvd (by rw [hrm]; exact Dvd.intro_left _ rfl)⟩
  let a0 : Γ → M := fun g =>
    if h : ∃ n : ℕ, ((fr ^ n : Γ) : Γ ⧸ V) = g then cocycleTrivializationOnPowers ρ κ fr h.choose else 0
  have ha0 : ∀ (g : Γ) (n : ℕ), ((fr ^ n : Γ) : Γ ⧸ V) = g → a0 g = cocycleTrivializationOnPowers ρ κ fr n := by
    intro g n hn
    have h : ∃ n : ℕ, ((fr ^ n : Γ) : Γ ⧸ V) = g := ⟨n, hn⟩
    simp only [a0, dif_pos h]
    exact wd _ _ (h.choose_spec.trans hn.symm)
  let H : Subgroup Γ := (Subgroup.zpowers (fr : Γ ⧸ V)).comap (QuotientGroup.mk' V)
  have hVH : V ≤ H := fun u hu => by
    have : (QuotientGroup.mk' V) u = 1 := (QuotientGroup.eq_one_iff u).2 hu
    rw [Subgroup.mem_comap, this]; exact Subgroup.one_mem _
  have hH : ∀ g ∈ H, ∃ n : ℕ, ∃ v ∈ V, g = fr ^ n * v := by
    intro g hg
    have hg' : (g : Γ ⧸ V) ∈ Subgroup.zpowers (fr : Γ ⧸ V) := hg
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 hg'
    refine ⟨n, (fr ^ n)⁻¹ * g, QuotientGroup.eq.1 ?_, by group⟩
    rw [QuotientGroup.mk_pow]; exact hn
  have hHi : (H.index : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k l]
    intro hd
    apply hidx
    have ht : H ⊔ I = ⊤ := gen _ (Subgroup.isOpen_mono (hVH.trans le_sup_left) hV) le_sup_right
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hst : MulAction.stabilizer I ((1 : Γ) : Γ ⧸ H) = H.subgroupOf I := by
      ext y
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← H.inv_mem_iff]
      change (((y : Γ) * 1 : Γ) : Γ ⧸ H) = _ ↔ _
      rw [QuotientGroup.eq]; simp
    have horb : MulAction.orbit I ((1 : Γ) : Γ ⧸ H) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      have hy : y ∈ ((I ⊔ H : Subgroup Γ) : Set Γ) := by rw [sup_comm, ht]; trivial
      rw [Subgroup.normal_mul] at hy
      obtain ⟨i, hi, h, hh, rfl⟩ := hy
      refine ⟨⟨i, hi⟩, ?_⟩
      change ((i * 1 : Γ) : Γ ⧸ H) = _
      rw [mul_one, QuotientGroup.mk_mul_of_mem i hh]
    have hix : H.relIndex I = H.index := by
      rw [Subgroup.relIndex, ← hst, MulAction.index_stabilizer, horb, Set.ncard_univ, Subgroup.index]
    exact (hix ▸ hd).trans (Subgroup.relIndex_dvd_of_le_left I (hNV.trans hVH))
  have hav : ∀ s, ∀ v ∈ V, a0 (s * v) = a0 s := by
    intro s v hv
    simp only [a0, QuotientGroup.mk_mul_of_mem s hv]
  obtain ⟨a, ha1, ha2⟩ := second_cohomology_transfer ρ H V hVH hVρ hHi κ hκ (fun s t v hv => (hVV0 hv s t).1)
    (fun s t v hv => (hVV0 hv s t).2) a0 hav (by
      intro s hs t ht
      obtain ⟨i, v, hv, rfl⟩ := hH s hs
      obtain ⟨j, w, hw, rfl⟩ := hH t ht
      have hρ : ρ v = 1 := hVρ hv
      rw [hav _ v hv, hav _ w hw, (hVV0 hv _ _).1, (hVV0 hw _ _).2, map_mul, hρ, mul_one, ha0 _ i rfl, ha0 _ j rfl,
        ← cocycle_sequence_add ρ κ hκ]
      apply ha0
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul_of_mem _ hv, QuotientGroup.mk_mul_of_mem _ hw, pow_add,
        QuotientGroup.mk_mul])
  refine ⟨a, ?_, fun s n hn => ha1 s n (hNV hn), ha2⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | x⁻¹ * y ∈ V}, hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← ha1 x _ hy, mul_inv_cancel_left]
