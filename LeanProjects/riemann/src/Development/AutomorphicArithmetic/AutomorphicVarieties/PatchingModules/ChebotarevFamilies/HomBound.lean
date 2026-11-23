import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem closure_normal_frattini_le_kernel (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) [hN : H.Normal] (hH : IsOpen (H : Set Γ)) (S : Set Γ) (χ : H →* Multiplicative (ZMod l))
    (hχ : IsOpen (χ.ker : Set H))
    (hS : ∀ t ∈ S, ∀ g : Γ, g * t * g⁻¹ ∈ χ.ker.map H.subtype) :
    (Subgroup.normalClosure S ⊔ PL l H).topologicalClosure ≤ χ.ker.map H.subtype := by
  have hl : ∀ z : Multiplicative (ZMod l), z ^ l = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow]
  have hKo : IsOpen ((χ.ker.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hχ
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hKo)
  refine sup_le ?_ ?_
  · rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    exact hS a ha c
  · let K : OpenSubgroup Γ := ⟨χ.ker.map H.subtype, hKo⟩
    have : Finite (Γ ⧸ K.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hKo
    have : Subgroup.FiniteIndex K.toSubgroup := Subgroup.finiteIndex_of_finite_quotient
    let U : OpenNormalSubgroup Γ :=
      { toSubgroup := Subgroup.normalCore K.toSubgroup
        isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _
          (K.toSubgroup.normalCore_isClosed K.isClosed) }
    have hU : ∀ h ∈ H, ∃ e, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨1, ?_⟩
      intro b
      have hb : b * h * b⁻¹ ∈ H := hN.conj_mem h hh b
      refine ⟨⟨b * h * b⁻¹, hb⟩ ^ l, MonoidHom.mem_ker.2 (by rw [map_pow, hl]), ?_⟩
      simp [conj_pow]
    unfold PL
    exact iInf_le_of_le U (iInf_le_of_le hU (Subgroup.normalCore_le K.toSubgroup))

private theorem twisted_kernel_forms_nonvanishing (l : ℕ) {Γ' Γ : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] (p : Γ' →* Γ) (hp : Continuous p)
    (hs : Function.Surjective p) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (χ : H.comap p →* Multiplicative (ZMod l)) (hχ : IsOpen (χ.ker : Set (H.comap p)))
    (hk : p.ker ≤ χ.ker.map (H.comap p).subtype) :
    ∃ ψ : HomL l H, ∀ x, ψ.1 (p.subgroupComap H x) = χ x := by
  set q := p.subgroupComap H with hqdef
  have hq : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : q.ker ≤ χ.ker := by
    intro x hx
    have h1 : p x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    obtain ⟨y, hy, hyx⟩ := hk (MonoidHom.mem_ker.2 h1 : x.1 ∈ p.ker)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let φ : H →* Multiplicative (ZMod l) :=
    (q.liftOfRightInverse (Function.surjInv hq) (Function.rightInverse_surjInv hq)) ⟨χ, hker⟩
  have hφ : ∀ x, φ (q x) = χ x := fun x =>
    q.liftOfRightInverse_comp_apply _ _ ⟨χ, hker⟩ x
  have hcont : Continuous q := (hp.comp continuous_subtype_val).subtype_mk _
  have hNc : IsClosed ((H.comap p : Subgroup Γ') : Set Γ') :=
    (Subgroup.isClosed_of_isOpen H hH).preimage hp
  haveI : CompactSpace (H.comap p) := isCompact_iff_compactSpace.1 hNc.isCompact
  have hc : IsClosed ((χ.ker : Set (H.comap p))ᶜ) := hχ.isClosed_compl
  have himg : IsClosed (q '' (χ.ker : Set (H.comap p))ᶜ) := (hc.isCompact.image hcont).isClosed
  have hopen : IsOpen (φ.ker : Set H) := by
    convert himg.isOpen_compl using 1
    ext y
    obtain ⟨x, rfl⟩ := hq y
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h x' hx' hxx
      apply hx'
      rw [← hφ x', hxx, h]
    · intro h
      by_contra hne
      exact h x (by rw [← hφ]; exact hne) rfl
  exact ⟨⟨φ, hopen⟩, hφ⟩

theorem UpperTheory.V.Pa.homBound :
    ∀ (l : ℕ) [Fact l.Prime] (Γ' : Type) [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [TotallyDisconnectedSpace Γ'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (p : Γ' →* Γ) (H : OpenNormalSubgroup Γ) (q : ℕ) (ta : Fin q → Γ'), Continuous p → Function.Surjective p → (∀ j, p (ta j) = 1) → p.ker ≤ (Subgroup.normalClosure (Set.range ta) ⊔ PL l (H.toSubgroup.comap p)).topologicalClosure → Finite (HomL l H.toSubgroup) → Finite (HomL l (H.toSubgroup.comap p)) ∧ Nat.card (HomL l (H.toSubgroup.comap p)) ≤ Nat.card (HomL l H.toSubgroup) * l ^ (q * H.toSubgroup.index) := by
  intro l _ Γ' _ _ _ _ _ Γ _ _ _ _ _ p H q ta hp hs hta hker hfin
  set N : Subgroup Γ' := H.toSubgroup.comap p with hN
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hNo : IsOpen (N : Set Γ') := H.isOpen.preimage hp
  haveI : Finite (Γ' ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNo
  have hHn : H.toSubgroup.Normal := inferInstance
  have hmem : ∀ (g : Γ') (j : Fin q), g * ta j * g⁻¹ ∈ N := by
    intro g j
    show p (g * ta j * g⁻¹) ∈ H.toSubgroup
    simp [hta]
  let f : HomL l N → (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) :=
    fun χ jc => χ.1 ⟨jc.2.out * ta jc.1 * jc.2.out⁻¹, hmem _ _⟩
  haveI : Nonempty (HomL l N) := ⟨⟨1, by simp⟩⟩
  let g : (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) → HomL l N := Function.invFun f
  have hg : ∀ χ, f (g (f χ)) = f χ := fun χ => Function.invFun_eq ⟨χ, rfl⟩
  have key : ∀ χ : HomL l N, ∃ ψ : HomL l H.toSubgroup,
      ∀ x, ψ.1 (p.subgroupComap H.toSubgroup x) = (χ.1 * (g (f χ)).1⁻¹) x := by
    intro χ
    have hopenδ : IsOpen (((χ.1 * (g (f χ)).1⁻¹).ker : Subgroup N) : Set N) := by
      refine Subgroup.isOpen_mono (H₁ := χ.1.ker ⊓ (g (f χ)).1.ker) ?_ ?_
      · intro x hx
        simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hx
        simp [MonoidHom.mem_ker, hx.1, hx.2]
      · exact χ.2.inter (g (f χ)).2
    have hS : ∀ t ∈ Set.range ta, ∀ g' : Γ',
        g' * t * g'⁻¹ ∈ (χ.1 * (g (f χ)).1⁻¹).ker.map N.subtype := by
      rintro t ⟨j, rfl⟩ g'
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g'
      set c : Γ' ⧸ N := (QuotientGroup.mk g' : Γ' ⧸ N)
      have hb : c.out * (h : Γ')⁻¹ * c.out⁻¹ ∈ N := by
        show p (c.out * (h : Γ')⁻¹ * c.out⁻¹) ∈ H.toSubgroup
        rw [map_mul, map_mul, map_inv, map_inv]
        exact hHn.conj_mem _ (H.toSubgroup.inv_mem h.2) _
      have ha := congrFun (hg χ) (j, c)
      refine ⟨⟨c.out * (h : Γ')⁻¹ * c.out⁻¹, hb⟩ * ⟨c.out * ta j * c.out⁻¹, hmem _ _⟩ *
        ⟨c.out * (h : Γ')⁻¹ * c.out⁻¹, hb⟩⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv]
        have : (χ.1 * (g (f χ)).1⁻¹) ⟨c.out * ta j * c.out⁻¹, hmem _ _⟩ = 1 := by
          simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
          exact mul_inv_eq_one.2 ha.symm
        rw [this, mul_one, mul_inv_cancel]
      · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hh]
        group
    have hk' : p.ker ≤ (χ.1 * (g (f χ)).1⁻¹).ker.map N.subtype :=
      hker.trans (closure_normal_frattini_le_kernel l N hNo (Set.range ta) _ hopenδ hS)
    exact twisted_kernel_forms_nonvanishing l p hp hs H.toSubgroup H.isOpen _ hopenδ hk'
  choose D hD using key
  let F : HomL l N → (Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) × HomL l H.toSubgroup :=
    fun χ => (f χ, D χ)
  have hF : Function.Injective F := by
    intro χ χ' h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e : ∀ x, (χ.1 * (g (f χ)).1⁻¹) x = (χ'.1 * (g (f χ')).1⁻¹) x := by
      intro x
      rw [← hD, ← hD, h2]
    rw [h1] at e
    apply Subtype.ext
    ext x
    have e' := e x
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply] at e'
    exact mul_right_cancel (G := Multiplicative (ZMod l)) e'
  haveI : Finite (HomL l N) := Finite.of_injective F hF
  refine ⟨inferInstance, ?_⟩
  have hidx : Nat.card (Γ' ⧸ N) = H.toSubgroup.index :=
    Subgroup.index_comap_of_surjective _ hs
  have hZ : Nat.card (Multiplicative (ZMod l)) = l :=
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod l)
  calc Nat.card (HomL l N)
      ≤ Nat.card ((Fin q × (Γ' ⧸ N) → Multiplicative (ZMod l)) × HomL l H.toSubgroup) :=
        Nat.card_le_card_of_injective F hF
    _ = Nat.card (HomL l H.toSubgroup) * l ^ (q * H.toSubgroup.index) := by
        rw [Nat.card_prod, mul_comm, Nat.card_fun, Nat.card_prod, Nat.card_fin, hidx, hZ]
