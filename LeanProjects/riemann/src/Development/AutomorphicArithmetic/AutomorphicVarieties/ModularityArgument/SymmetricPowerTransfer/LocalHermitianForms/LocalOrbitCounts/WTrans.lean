import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem stab_smul_comm {T Y : Type} [CommGroup T] [MulAction T Y] (t : T) (y : Y) :
    MulAction.stabilizer T (t • y) = MulAction.stabilizer T y := by
  ext s
  simp only [MulAction.mem_stabilizer_iff]
  rw [smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]

private theorem out_mk_smul {T Y : Type} [Group T] [MulAction T Y] (y : Y) :
    ∃ t : T, (Quotient.mk (MulAction.orbitRel T Y) y).out = t • y := by
  obtain ⟨t, ht⟩ := MulAction.orbitRel_apply.mp (Quotient.mk_out (s := MulAction.orbitRel T Y) y)
  exact ⟨t, ht.symm⟩

private theorem mk_smul_eq {T Y : Type} [Group T] [MulAction T Y] (t : T) (y : Y) :
    Quotient.mk (MulAction.orbitRel T Y) (t • y) = Quotient.mk (MulAction.orbitRel T Y) y := by
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit y t))

private theorem wcount_sub {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (k : Y → ℂ) :
    wcount C k = ∑ᶠ o : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0},
      ((MulAction.stabilizer T o.1.out).relIndex C : ℂ) * k o.1.out := by
  classical
  set g : MulAction.orbitRel.Quotient T Y → ℂ :=
    fun o => ((MulAction.stabilizer T o.out).relIndex C : ℂ) * k o.out with hg
  have hs : Function.support g ⊆ {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} := by
    intro o ho
    simp only [Set.mem_setOf_eq]
    intro h0
    exact (Function.mem_support.mp ho) (by simp [hg, h0])
  have h1 := finsum_set_coe_eq_finsum_mem (f := g) {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0}
  rw [← finsum_mem_inter_support g, Set.inter_eq_right.mpr hs, finsum_mem_support] at h1
  exact h1.symm

theorem UpperTheory.V.Z.Sym.Loc.wTrans :
    ∀ (T Y Y' : Type) [CommGroup T] [MulAction T Y] [MulAction T Y'] (C : Subgroup T) (k : Y → ℂ) (k' : Y' → ℂ) (R : Y → Y' → Prop),
    (∀ (t : T) y, k (t • y) = k y) → (∀ (t : T) y', k' (t • y') = k' y') → (∀ (t : T) y y', R y y' → R (t • y) (t • y')) →
    (∀ y y', R y y' → k y = k' y') → (∀ y, k y ≠ 0 → ∃! y', R y y') → (∀ y', k' y' ≠ 0 → ∃! y, R y y') →
    wcount C k = wcount C k' := by
  classical
  intro T Y Y' _ _ _ C k k' R hk hk' hR hkk hex hex'
  rw [wcount_sub C k, wcount_sub C k']
  have stab_eq : ∀ y y', R y y' → k y ≠ 0 → k' y' ≠ 0 →
      MulAction.stabilizer T y = MulAction.stabilizer T y' := by
    intro y y' hyy hy hy'
    ext s
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro hs
      have h1 : R y (s • y') := by simpa [hs] using hR s y y' hyy
      exact (hex y hy).unique h1 hyy
    · intro hs
      have h1 : R (s • y) y' := by simpa [hs] using hR s y y' hyy
      exact (hex' y' hy').unique h1 hyy
  let pick : ∀ o : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0}, Y' :=
    fun o => Classical.choose (hex o.1.out o.2).exists
  have pick_R : ∀ o, R o.1.out (pick o) := fun o => Classical.choose_spec (hex o.1.out o.2).exists
  have pick_k : ∀ o, k' (pick o) ≠ 0 := fun o => by
    rw [← hkk _ _ (pick_R o)]
    exact o.2
  have e_mem : ∀ o, Quotient.mk (MulAction.orbitRel T Y') (pick o) ∈
      {o' : MulAction.orbitRel.Quotient T Y' | k' o'.out ≠ 0} := by
    intro o
    obtain ⟨t, ht⟩ := out_mk_smul (T := T) (pick o)
    show k' _ ≠ 0
    rw [ht, hk']
    exact pick_k o
  let e : {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} →
      {o' : MulAction.orbitRel.Quotient T Y' | k' o'.out ≠ 0} :=
    fun o => ⟨Quotient.mk _ (pick o), e_mem o⟩
  refine finsum_eq_of_bijective e ⟨?_, ?_⟩ ?_
  · intro o1 o2 h
    have h' : Quotient.mk (MulAction.orbitRel T Y') (pick o1) = Quotient.mk _ (pick o2) :=
      congrArg Subtype.val h
    obtain ⟨t, ht⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h')
    have h2 : R (t • o2.1.out) (pick o1) := by
      rw [← ht]
      exact hR t _ _ (pick_R o2)
    have h3 : t • o2.1.out = o1.1.out := (hex' _ (pick_k o1)).unique h2 (pick_R o1)
    apply Subtype.ext
    rw [← Quotient.out_eq o1.1, ← Quotient.out_eq o2.1, ← h3, mk_smul_eq]
  · rintro ⟨o', ho'⟩
    obtain ⟨z, hz, -⟩ := hex' o'.out ho'
    have hkz : k z ≠ 0 := by
      rw [hkk _ _ hz]
      exact ho'
    have hmem : Quotient.mk (MulAction.orbitRel T Y) z ∈
        {o : MulAction.orbitRel.Quotient T Y | k o.out ≠ 0} := by
      obtain ⟨s, hs⟩ := out_mk_smul (T := T) z
      show k _ ≠ 0
      rw [hs, hk]
      exact hkz
    refine ⟨⟨_, hmem⟩, ?_⟩
    obtain ⟨s, hs⟩ := out_mk_smul (T := T) z
    have h1 : R (Quotient.mk (MulAction.orbitRel T Y) z).out (s • o'.out) := by
      rw [hs]
      exact hR s _ _ hz
    have h2 : pick ⟨_, hmem⟩ = s • o'.out := (hex _ hmem).unique (pick_R ⟨_, hmem⟩) h1
    apply Subtype.ext
    show Quotient.mk _ (pick ⟨_, hmem⟩) = o'
    rw [h2, mk_smul_eq, Quotient.out_eq]
  · intro o
    obtain ⟨t, ht⟩ := out_mk_smul (T := T) (pick o)
    show _ = ((MulAction.stabilizer T (Quotient.mk (MulAction.orbitRel T Y') (pick o)).out).relIndex C : ℂ) *
      k' (Quotient.mk (MulAction.orbitRel T Y') (pick o)).out
    rw [ht, stab_smul_comm, hk', ← hkk _ _ (pick_R o), stab_eq _ _ (pick_R o) o.2 (pick_k o)]
