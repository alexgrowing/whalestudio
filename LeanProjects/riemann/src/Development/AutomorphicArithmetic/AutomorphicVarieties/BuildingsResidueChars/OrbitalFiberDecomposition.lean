import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

open MulAction

private theorem fib_abs {O I : Type} {P : I → Type} (F : ∀ i, P i → O) (S : ∀ i, Set (P i)) (B : Set O) (hB : B.Finite)
    (w : O → ℂ) (wi : ∀ i, P i → ℂ) (hw : ∀ o, o ∉ B → w o = 0) (hwi : ∀ i p, p ∉ S i → wi i p = 0)
    (hF : ∀ i, ∀ p ∈ S i, F i p ∈ B ∧ wi i p = w (F i p)) (hs : ∀ o ∈ B, ∃ i, ∃ p ∈ S i, F i p = o)
    (hij : ∀ i j, ∀ p ∈ S i, ∀ q ∈ S j, F i p = F j q → i = j) (hinj : ∀ i, Set.InjOn (F i) (S i)) :
    ∑ᶠ o, w o = ∑ᶠ i, ∑ᶠ p, wi i p := by
  classical
  have h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o := by
    intro i
    rw [finsum_mem_image (hinj i), finsum_mem_def]
    congr 1
    funext p
    by_cases hp : p ∈ S i
    · rw [Set.indicator_of_mem hp, (hF i p hp).2]
    · rw [Set.indicator_of_notMem hp, hwi i p hp]
  have hsub : ∀ i, F i '' S i ⊆ B := by
    rintro i _ ⟨p, hp, rfl⟩
    exact (hF i p hp).1
  have hI : {i | (S i).Nonempty}.Finite := by
    let g : {i | (S i).Nonempty} → B := fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩
    have hg : Function.Injective g := fun i j h =>
      Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))
    haveI := hB.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg)
  have hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i := by
    ext o
    simp only [Set.mem_iUnion]
    constructor
    · intro ho
      obtain ⟨i, p, hp, rfl⟩ := hs o ho
      exact ⟨i, ⟨p, hp⟩, p, hp, rfl⟩
    · rintro ⟨i, _, ho⟩
      exact hsub i ho
  have h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o := by
    rw [finsum_mem_def]
    congr 1
    funext o
    by_cases ho : o ∈ B
    · rw [Set.indicator_of_mem ho]
    · rw [Set.indicator_of_notMem ho, hw o ho]
  rw [h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]
  · congr 1
    funext i
    by_cases hi : i ∈ {i | (S i).Nonempty}
    · rw [Set.indicator_of_mem hi, h1]
    · rw [Set.indicator_of_notMem hi, h1]
      have : S i = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
      rw [this, Set.image_empty, finsum_mem_empty]
  · intro i _ j _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    exact hne (hij i j p hp q hq h.symm)

private theorem rel_smul {H X : Type} [Group H] [MulAction H X] (H₀ : Subgroup H) (hn : H₀.Normal) (h : H) (x : X) :
    H₀.relIndex (stabilizer H (h • x)) = H₀.relIndex (stabilizer H x) := by
  have h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hn.conj_mem y hy h
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, ?_⟩
      · simpa using hn.conj_mem z hz h⁻¹
      · simp [mul_assoc]
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← h0]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

private theorem out_mk {H X : Type} [Group H] [MulAction H X] (x : X) :
    ∃ h : H, (Quotient.mk (orbitRel H X) x).out = h • x := by
  have : (Quotient.mk (orbitRel H X) x).out ∈ orbit H x :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))
  obtain ⟨h, hh⟩ := this
  exact ⟨h, hh.symm⟩

private theorem mk_smul {H X : Type} [Group H] [MulAction H X] (h : H) (x : X) :
    Quotient.mk (orbitRel H X) (h • x) = Quotient.mk (orbitRel H X) x :=
  Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)

theorem UpperTheory.orbitalFiber_decomposition :
    UpperTheory.V.Z.Sym.Glob.Fib.Decomp := by
  intro H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu
  unfold UpperTheory.V.Z.Sym.gq
  have hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x' :=
    fun x x' h => orbitRel_apply.1 (Quotient.exact h)
  refine fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X))
    (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨T, hT⟩ := hT
    refine (T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_
    obtain ⟨h, s, hs, ho⟩ := hT _ ho
    refine ⟨s, hs, ?_⟩
    rw [← mk_smul h s, ← ho]
    exact Quotient.out_eq o
  · intro o ho
    have : k o.out = 0 := not_not.1 ho
    rw [this, zero_div]
  · intro i p hp
    have : ki i p.out = 0 := not_not.1 hp
    rw [this, zero_div]
  · intro i p hp
    have hp' : ki i p.out ≠ 0 := hp
    obtain ⟨h, hh⟩ := out_mk (H := H) (e i p.out)
    have hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out := by rw [hh, hk, hke i _ hp']
    refine ⟨fun h0 => hp' (hv ▸ h0), ?_⟩
    have hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]
      · intro hg
        obtain ⟨_, a, rfl⟩ := hu i i _ _ g hp' hp' hg
        refine ⟨a, hinj i ?_, rfl⟩
        rw [he]
        exact hg
    show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out /
      (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)
    rw [hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]
  · intro o ho
    obtain ⟨i, y, h, hy, hx⟩ := hs _ ho
    obtain ⟨a, ha⟩ := out_mk (H := Hi i) y
    refine ⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩
    · show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0
      rwa [ha, hki]
    · show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o
      rw [ha, he, mk_smul, ← mk_smul h, ← hx]
      exact Quotient.out_eq o
  · intro i j p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ hpq.symm
    exact (hu i j _ _ h hp hq hh).1
  · intro i p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ (Eq.symm hpq)
    obtain ⟨_, a, rfl⟩ := hu i i _ _ h hp hq hh
    rw [← he] at hh
    have h3 := hinj i hh
    rw [← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]
    exact (mk_smul a _).symm
