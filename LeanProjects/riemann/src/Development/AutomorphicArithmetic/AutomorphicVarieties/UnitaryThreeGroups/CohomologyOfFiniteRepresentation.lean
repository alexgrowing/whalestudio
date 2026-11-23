import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem continuous_of_coset_constant {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace M]
    (V : Subgroup Γ) (hV : IsOpen (V : Set Γ)) (a : Γ → M) (ha : ∀ s, ∀ v ∈ V, a (s * v) = a s) : Continuous a := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | x⁻¹ * y ∈ V}, hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← ha x _ hy, mul_inv_cancel_left]

private theorem cocycle_coboundary_averaging {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
    (ρ : Representation k G M) (N : Subgroup G) (hN : (N.index : k) ≠ 0) (f : G → M)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (h0 : ∀ n ∈ N, f n = 0) :
    ∃ m, ∀ g, f g = ρ g m - m := by
  classical
  have hfi : N.FiniteIndex := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hout : ∀ g : G, f (QuotientGroup.mk g : G ⧸ N).out = f g := fun g => by
    have h1 : ((QuotientGroup.mk g : G ⧸ N).out)⁻¹ * g ∈ N := QuotientGroup.eq.1 (Quotient.out_eq _)
    have h2 := hf (QuotientGroup.mk g : G ⧸ N).out (((QuotientGroup.mk g : G ⧸ N).out)⁻¹ * g)
    rw [mul_inv_cancel_left, h0 _ h1, map_zero, add_zero] at h2
    exact h2.symm
  let A : M := ∑ x : G ⧸ N, f x.out
  have hA : ∀ t, A = (N.index : k) • f t + ρ t A := by
    intro t
    have e1 : A = ∑ x : G ⧸ N, f (t * x.out) := by
      simp only [A]
      rw [← Equiv.sum_comp (MulAction.toPerm t)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hout (t * x.out)]
      have : (QuotientGroup.mk (t * x.out) : G ⧸ N) = t • x := MulAction.Quotient.mk_smul_out N t x
      simp only [this, MulAction.toPerm_apply]
    conv_lhs => rw [e1]
    simp only [hf, A, map_sum]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card,
      Nat.cast_smul_eq_nsmul]
  refine ⟨-((N.index : k)⁻¹ • A), fun g => ?_⟩
  have e : ρ g A = A - (N.index : k) • f g := by rw [eq_sub_iff_add_eq, add_comm]; exact (hA g).symm
  rw [map_neg, map_smul, e, smul_sub, smul_smul, inv_mul_cancel₀ hN, one_smul]
  abel

private def powerCocycleSum {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (x : Γ) (m : M) : ℕ → M
  | 0 => 0
  | n + 1 => m + ρ x (powerCocycleSum ρ x m n)

private theorem unipotent_cochain_add {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (x : Γ) (m : M) (i j : ℕ) :
    powerCocycleSum ρ x m (i + j) = powerCocycleSum ρ x m i + ρ (x ^ i) (powerCocycleSum ρ x m j) := by
  induction i with
  | zero => simp [powerCocycleSum]
  | succ i ih =>
    rw [show i + 1 + j = (i + j) + 1 by ring]
    simp only [powerCocycleSum, ih, map_add, pow_succ', map_mul, Module.End.mul_apply, pow_add]
    abel

private theorem unipotent_cochain_periodic {l : ℕ} {k Γ M : Type} [Field k] [CharP k l] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (x : Γ) (m : M) (r : ℕ)
    (hρ : ∀ n, ρ (x ^ r) (powerCocycleSum ρ x m n) = powerCocycleSum ρ x m n) (i j : ℕ) (hij : i ≡ j [MOD r * l]) :
    powerCocycleSum ρ x m i = powerCocycleSum ρ x m j := by
  have e2 : ∀ n j, powerCocycleSum ρ x m (r * n + j) = n • powerCocycleSum ρ x m r + powerCocycleSum ρ x m j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show r * (n + 1) + j = r + (r * n + j) by ring, unipotent_cochain_add, hρ, ih, succ_nsmul]
      abel
  have e3 : ∀ j, powerCocycleSum ρ x m j = powerCocycleSum ρ x m (j % (r * l)) := by
    intro j
    conv_lhs => rw [← Nat.div_add_mod j (r * l), mul_assoc, e2]
    rw [← Nat.cast_smul_eq_nsmul k, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul, zero_add]
  rw [e3 i, e3 j, hij]

private theorem invariants_of_normal_stable {k Γ M : Type} [Field k] [Group Γ] [AddCommGroup M] [Module k M]
    (ρ : Representation k Γ M) (I : Subgroup Γ) [hI : I.Normal] (y : M) (hy : ∀ i ∈ I, ρ i y = y) (g : Γ) :
    ∀ i ∈ I, ρ i (ρ g y) = ρ g y := by
  intro i hi
  have h1 : g⁻¹ * i * g ∈ I := by simpa using hI.conj_mem i hi g⁻¹
  conv_rhs => rw [← hy _ h1]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

private theorem unipotent_restriction_surjective (l : ℕ) [hl : Fact l.Prime] {k Γ M : Type} [Field k] [CharP k l] [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module k M] [TopologicalSpace M]
    (ρ : Representation k Γ M) (hker : IsOpen (ρ.ker : Set Γ)) (I : Subgroup Γ) [I.Normal] (fr : Γ)
    (hfr : (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n)
    (m : M) (hm : ∀ i ∈ I, ρ i m = m) :
    ∃ f : Γ → M, Continuous f ∧ (∀ g h, f (g * h) = f g + ρ g (f h)) ∧ (∀ i ∈ I, f i = 0) ∧ f fr = m := by
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
  have cyc : ∀ (W : Subgroup Γ) [W.Normal], IsOpen (W : Set Γ) → I ≤ W → Subgroup.zpowers (fr : Γ ⧸ W) = ⊤ := by
    intro W _ hW hIW
    have ht : (Subgroup.zpowers (fr : Γ ⧸ W)).comap (QuotientGroup.mk' W) = ⊤ := by
      have hle : W ≤ (Subgroup.zpowers (fr : Γ ⧸ W)).comap (QuotientGroup.mk' W) := fun u hu => by
        have : (QuotientGroup.mk' W) u = 1 := (QuotientGroup.eq_one_iff u).2 hu
        rw [Subgroup.mem_comap, this]; exact Subgroup.one_mem _
      exact gen _ (Subgroup.isOpen_mono hle hW) (hIW.trans hle) (Subgroup.mem_zpowers _)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have : y ∈ (Subgroup.zpowers (fr : Γ ⧸ W)).comap (QuotientGroup.mk' W) := by rw [ht]; trivial
    exact this
  have hb : ∀ n, ∀ i ∈ I, ρ i (powerCocycleSum ρ fr m n) = powerCocycleSum ρ fr m n := by
    intro n
    induction n with
    | zero => intro i _; simp [powerCocycleSum]
    | succ n ih => intro i hi; simp only [powerCocycleSum, map_add, hm i hi, invariants_of_normal_stable ρ I _ ih fr i hi]
  let V1 : Subgroup Γ := I ⊔ ρ.ker
  have hV1 : IsOpen (V1 : Set Γ) := Subgroup.isOpen_mono le_sup_right hker
  have hV1b : ∀ v ∈ V1, ∀ n, ρ v (powerCocycleSum ρ fr m n) = powerCocycleSum ρ fr m n := by
    intro v hv n
    have hv' : v ∈ ((I ⊔ ρ.ker : Subgroup Γ) : Set Γ) := hv
    rw [Subgroup.normal_mul] at hv'
    obtain ⟨i, hi, h, hh, rfl⟩ := hv'
    have hρ : ρ h = 1 := hh
    simp only [map_mul, hρ, mul_one, hb n i hi]
  haveI : Finite (Γ ⧸ V1) := V1.quotient_finite_of_isOpen hV1
  let r := orderOf (fr : Γ ⧸ V1)
  have hr0 : r ≠ 0 := (orderOf_pos _).ne'
  have hfrr : fr ^ r ∈ V1 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
  obtain ⟨e, c, hc, hrm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr0 l hl.out.ne_one
  obtain ⟨U, hUo, hIU, hUi⟩ := hU (e + 1)
  let U1 := U.normalCore
  have hU1 : IsOpen (U1 : Set Γ) := core _ hUo
  have hIU1 : I ≤ U1 := Subgroup.normal_le_normalCore.2 hIU
  have hord : l ^ (e + 1) ∣ orderOf (fr : Γ ⧸ U1) := by
    rw [← Nat.card_zpowers, cyc U1 hU1 hIU1, Subgroup.card_top, ← hUi]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le U)
  let V : Subgroup Γ := V1 ⊓ U1
  have hV : IsOpen (V : Set Γ) := hV1.inter hU1
  have hIV : I ≤ V := le_inf le_sup_left hIU1
  haveI : Finite (Γ ⧸ V) := V.quotient_finite_of_isOpen hV
  have wd : ∀ i j : ℕ, ((fr ^ i : Γ) : Γ ⧸ V) = (fr ^ j : Γ) → powerCocycleSum ρ fr m i = powerCocycleSum ρ fr m j := by
    intro i j hij
    have hij' := QuotientGroup.eq.1 hij
    have m1 : i ≡ j [MOD r] := by
      rw [← pow_eq_pow_iff_modEq, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow]
      exact QuotientGroup.eq.2 hij'.1
    have m2 : i ≡ j [MOD l ^ (e + 1)] := by
      refine Nat.ModEq.of_dvd hord ?_
      rw [← pow_eq_pow_iff_modEq, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow]
      exact QuotientGroup.eq.2 hij'.2
    refine unipotent_cochain_periodic (l := l) ρ fr m r (hV1b _ hfrr) i j ?_
    have cop : Nat.Coprime (l ^ (e + 1)) c := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hc)
    rw [show r * l = l ^ (e + 1) * c by rw [hrm]; ring]
    exact (Nat.modEq_and_modEq_iff_modEq_mul cop).1 ⟨m2, m1.of_dvd (by rw [hrm]; exact Dvd.intro_left _ rfl)⟩
  have hH : ∀ g : Γ, ∃ n : ℕ, ((fr ^ n : Γ) : Γ ⧸ V) = g := by
    intro g
    have hg' : (g : Γ ⧸ V) ∈ Subgroup.zpowers (fr : Γ ⧸ V) := by rw [cyc V hV hIV]; trivial
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 hg'
    exact ⟨n, by rw [QuotientGroup.mk_pow]; exact hn⟩
  let a0 : Γ → M := fun g => powerCocycleSum ρ fr m (hH g).choose
  have ha0 : ∀ (g : Γ) (n : ℕ), ((fr ^ n : Γ) : Γ ⧸ V) = g → a0 g = powerCocycleSum ρ fr m n :=
    fun g n hn => wd _ _ ((hH g).choose_spec.trans hn.symm)
  refine ⟨a0, continuous_of_coset_constant V hV a0 fun s v hv => ?_, fun g h => ?_, fun i hi => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hH s
    rw [ha0 s n hn, ha0 _ n (by rw [hn, QuotientGroup.mk_mul_of_mem s hv])]
  · obtain ⟨i, hi⟩ := hH g
    obtain ⟨j, hj⟩ := hH h
    have hv : (fr ^ i)⁻¹ * g ∈ V := QuotientGroup.eq.1 hi
    rw [ha0 g i hi, ha0 h j hj, ha0 (g * h) (i + j) (by rw [pow_add, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hi, hj]),
      unipotent_cochain_add]
    conv_rhs => rw [← mul_inv_cancel_left (fr ^ i) g, map_mul, Module.End.mul_apply, hV1b _ hv.1]
  · exact ha0 i 0 (by rw [pow_zero, eq_comm, QuotientGroup.mk_one, QuotientGroup.eq_one_iff]; exact hIV hi)
  · rw [ha0 fr 1 (by rw [pow_one])]
    simp [powerCocycleSum]

theorem UpperTheory.cohomology_of_finite_representation :
    ∀ (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
          (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (I N : Subgroup Γ) [I.Normal] [N.Normal], IsClosed (I : Set Γ) → IsClosed (N : Set Γ) → N ≤ I → N ≤ ρ.ker → ¬ l ∣ N.relIndex I →
          (∃ fr : Γ, (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) → (∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n) →
          Module.finrank k (H1ur ρ N) = Module.finrank k (H0 ρ) := by
  intro l hl k M _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ _ ρ hker I N _ _ _ _ hNI hNρ hidx ⟨fr, hfr⟩ hU
  have hd : ∀ m, ReciprocityTheory.Gal.d0 ρ m ∈ ReciprocityTheory.Gal.Z1 ρ := fun m =>
    ⟨continuous_of_coset_constant ρ.ker hker _ fun s v hv => by
      have hρ : ρ v = 1 := hv
      simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, hρ, mul_one], fun g h => by
      simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, map_sub, Module.End.mul_apply]; abel⟩
  let P : Submodule k M :=
    { carrier := {m | ∀ i ∈ I, ρ i m = m}
      add_mem' := fun {a b} ha hb i hi => by rw [map_add, ha i hi, hb i hi]
      zero_mem' := fun i _ => map_zero _
      smul_mem' := fun c a ha i hi => by rw [map_smul, ha i hi] }
  let Z : Submodule k (ReciprocityTheory.Gal.Z1 ρ) :=
    { carrier := {f | ∀ i ∈ I, f.1 i = 0}
      add_mem' := fun {a b} ha hb i hi => by
        show a.1 i + b.1 i = 0
        rw [ha i hi, hb i hi, add_zero]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun c a ha i hi => by
        show c • a.1 i = 0
        rw [ha i hi, smul_zero] }
  let ev : Z →ₗ[k] P :=
    { toFun := fun f => ⟨f.1.1 fr, fun i hi => by
        have h1 := f.1.2.2 i fr
        have h2 := f.1.2.2 fr (fr⁻¹ * i * fr)
        rw [f.2 (fr⁻¹ * i * fr) (by simpa using ‹I.Normal›.conj_mem i hi fr⁻¹), map_zero, add_zero,
          show fr * (fr⁻¹ * i * fr) = i * fr by group] at h2
        rw [f.2 i hi, zero_add, h2] at h1
        exact h1.symm⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro f hf
      have hf' : f.1.1 fr = 0 := congrArg Subtype.val hf
      have hc := f.1.2.2
      have h1 : f.1.1 1 = 0 := f.2 1 I.one_mem
      let S : Subgroup Γ :=
        { carrier := {g | f.1.1 g = 0}
          mul_mem' := fun {a b} ha hb => by
            show f.1.1 (a * b) = 0
            rw [hc, ha, hb, map_zero, add_zero]
          one_mem' := h1
          inv_mem' := fun {a} ha => by
            have := hc a⁻¹ a
            rw [inv_mul_cancel, h1, ha, map_zero, add_zero] at this
            exact this.symm }
      have hS : ⊤ ≤ S := by
        rw [← hfr]
        exact Subgroup.topologicalClosure_minimal _ (sup_le (fun i hi => f.2 i hi) (Subgroup.zpowers_le.2 hf'))
          (isClosed_eq f.1.2.1 continuous_const)
      exact Subtype.ext (Subtype.ext (funext fun g => hS (Subgroup.mem_top g)))
    · intro m
      obtain ⟨f, h1, h2, h3, h4⟩ := unipotent_restriction_surjective l ρ hker I fr hfr hU m.1 m.2
      exact ⟨⟨⟨f, h1, h2⟩, h3⟩, Subtype.ext h4⟩
  let E := LinearEquiv.ofBijective ev hev
  haveI : Module.Finite k Z := Module.Finite.equiv E.symm
  let π : Z →ₗ[k] ReciprocityTheory.Gal.H1 ρ := (Submodule.mkQ _).comp Z.subtype
  let δ : P →ₗ[k] Z :=
    { toFun := fun m => ⟨⟨ReciprocityTheory.Gal.d0 ρ m.1, hd m.1⟩, fun i hi => by
        show ρ i m.1 - m.1 = 0
        rw [m.2 i hi, sub_self]⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (ReciprocityTheory.Gal.d0 ρ) a.1 b.1))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (ReciprocityTheory.Gal.d0 ρ) c a.1)) }
  have hπr : LinearMap.range π = H1ur ρ N := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      show Submodule.Quotient.mk (restrictCocycles1 ρ N.subtype continuous_subtype_val f.1) =
        (0 : ReciprocityTheory.Gal.H1 (ρ.comp N.subtype))
      rw [Submodule.Quotient.mk_eq_zero]
      refine (ReciprocityTheory.Gal.mem_coboundaries1 _ _).2 ⟨0, fun j => ?_⟩
      show f.1.1 j = _
      rw [f.2 j (hNI j.2), map_zero, sub_zero]
    · intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hx' : Submodule.Quotient.mk (restrictCocycles1 ρ N.subtype continuous_subtype_val f) =
        (0 : ReciprocityTheory.Gal.H1 (ρ.comp N.subtype)) := hx
      rw [Submodule.Quotient.mk_eq_zero] at hx'
      obtain ⟨m0, hm0⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hx'
      have hN0 : ∀ n ∈ N, f.1 n = 0 := fun n hn => by
        have e : f.1 n = ρ n m0 - m0 := hm0 ⟨n, hn⟩
        have hρ : ρ n = 1 := hNρ hn
        rw [e, hρ, Module.End.one_apply, sub_self]
      obtain ⟨m, hm⟩ := cocycle_coboundary_averaging (ρ.comp I.subtype) (N.subgroupOf I)
        (by rw [Ne, CharP.cast_eq_zero_iff k l]; exact hidx) (fun g => f.1 g) (fun g h => f.2.2 g h)
        (fun n hn => hN0 n hn)
      let b : ReciprocityTheory.Gal.Z1 ρ := ⟨ReciprocityTheory.Gal.d0 ρ m, hd m⟩
      refine ⟨⟨f - b, fun j hj => ?_⟩, (Submodule.Quotient.eq _).2 ?_⟩
      · have e : f.1 j = ρ j m - m := hm ⟨j, hj⟩
        show f.1 j - ReciprocityTheory.Gal.d0 ρ m j = 0
        rw [ReciprocityTheory.Gal.amitsur_d0_apply, e, sub_self]
      · show ((f - b) - f).1 ∈ ReciprocityTheory.Gal.B1 ρ
        rw [sub_sub_cancel_left]
        exact (ReciprocityTheory.Gal.B1 ρ).neg_mem ⟨m, rfl⟩
  have hπk : LinearMap.ker π = LinearMap.range δ := by
    ext f
    constructor
    · intro hf
      have hf' : (Submodule.Quotient.mk f.1 : ReciprocityTheory.Gal.H1 ρ) = 0 := hf
      rw [Submodule.Quotient.mk_eq_zero] at hf'
      obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hf'
      refine ⟨⟨m, fun i hi => ?_⟩, Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))⟩
      have e : f.1.1 i = ρ i m - m := hm i
      rw [f.2 i hi] at e
      exact sub_eq_zero.1 e.symm
    · rintro ⟨m, rfl⟩
      show (Submodule.Quotient.mk (δ m).1 : ReciprocityTheory.Gal.H1 ρ) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨m.1, rfl⟩
  have hle : H0 ρ ≤ P := fun m hm i _ => hm i
  have hδk : LinearMap.ker δ = (H0 ρ).comap P.subtype := by
    ext m
    constructor
    · intro hm g
      have e : ρ g m.1 - m.1 = 0 := congrFun (congrArg (fun z : Z => z.1.1) hm) g
      exact sub_eq_zero.1 e
    · intro hm
      exact Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g)))
  have e1 := LinearMap.finrank_range_add_finrank_ker π
  have e2 := LinearMap.finrank_range_add_finrank_ker δ
  rw [hπr, hπk, E.finrank_eq] at e1
  rw [hδk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at e2
  omega
