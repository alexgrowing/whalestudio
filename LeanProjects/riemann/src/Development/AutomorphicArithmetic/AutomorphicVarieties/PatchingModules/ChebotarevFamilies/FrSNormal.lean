import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa.FrattiniSubgroup

private theorem exists_hom (l : ℕ) [hl : Fact l.Prime] (Q : Type) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup l Q) : ∃ φ : Q →* Multiplicative (ZMod l), φ.ker ≠ ⊤ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hQ
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact not_nontrivial_iff_subsingleton.mpr hk.1 ‹_›
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime l (n := k - 1)
    (hk ▸ pow_dvd_pow l (Nat.sub_le k 1))
  have hidx : K.index = l := by
    have h := K.card_mul_index
    rw [hK, hk] at h
    have e : l ^ k = l ^ (k - 1) * l := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hl.out.pos _) h
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card
    (by rw [hidx, hk, Nat.Prime.pow_minFac hl.out hk0])
  have hcard : Nat.card (Q ⧸ K) = l := by rw [← Subgroup.index_eq_card, hidx]
  let e := mulEquivOfPrimeCardEq hcard (G' := Multiplicative (ZMod l)) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), fun htop => ?_⟩
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q ∈ (e.toMonoidHom.comp (QuotientGroup.mk' K)).ker := htop ▸ Subgroup.mem_top q
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
    exact hq
  rw [hKtop, Subgroup.index_top] at hidx
  exact hl.out.one_lt.ne hidx

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

private def frS (l : ℕ) (K : Subgroup Γ) : Subgroup Γ :=
  (⨅ φ : {φ : K →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set K)}, φ.1.ker).map K.subtype

private theorem frS_normal (l : ℕ) (K : Subgroup Γ) [hK : K.Normal] : (frS l K).Normal := by
  constructor
  intro x hx g
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  let c : K →* K := (MulAut.conjNormal g).toMonoidHom
  have hc : ∀ y : K, (c y : Γ) = g * y * g⁻¹ := fun y => MulAut.conjNormal_apply g y
  have hcc : Continuous c := by
    have h1 : Continuous fun y : K => g * (y : Γ) * g⁻¹ :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 := h1.subtype_mk (fun y => hK.conj_mem y y.2 g)
    convert h2 using 1
    funext y
    exact Subtype.ext (hc y)
  refine Subgroup.mem_map.mpr ⟨c k, ?_, hc k⟩
  rw [Subgroup.mem_iInf] at hk ⊢
  intro ψ
  have hφ : IsOpen ((ψ.1.comp c).ker : Set K) := by
    show IsOpen (c ⁻¹' (ψ.1.ker : Set K))
    exact ψ.2.preimage hcc
  exact hk ⟨ψ.1.comp c, hφ⟩

private theorem frS_open (l : ℕ) (h : PhiCond Γ l) (K : Subgroup Γ) (hK : IsOpen (K : Set Γ)) :
    IsOpen (frS l K : Set Γ) := by
  haveI := h K hK
  unfold frS
  rw [Subgroup.coe_map, Subgroup.coe_iInf]
  exact hK.isOpenMap_subtype_val _ (isOpen_iInter_of_finite fun φ => φ.2)

private def fr (l : ℕ) (h : PhiCond Γ l) (K : OpenNormalSubgroup Γ) : OpenNormalSubgroup Γ where
  toSubgroup := frS l K.toSubgroup
  isOpen' := frS_open l h _ K.isOpen
  isNormal' := frS_normal l _

private theorem fr_le (l : ℕ) (h : PhiCond Γ l) (K : OpenNormalSubgroup Γ) :
    (fr l h K).toSubgroup ≤ K.toSubgroup := Subgroup.map_subtype_le _

private theorem fr_lt (l : ℕ) [Fact l.Prime] [CompactSpace Γ] (h : PhiCond Γ l) (K V : OpenNormalSubgroup Γ)
    (hp : ∀ k ∈ K.toSubgroup, ∃ e : ℕ, k ^ l ^ e ∈ V.toSubgroup) (hn : ¬ K.toSubgroup ≤ V.toSubgroup) :
    (fr l h K).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) <
      K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup) := by
  let π := (QuotientGroup.mk' V.toSubgroup).subgroupMap K.toSubgroup
  haveI : Finite (Γ ⧸ V.toSubgroup) := (inferInstance : Finite (Γ ⧸ (V.toOpenSubgroup : Subgroup Γ)))
  have hπk : ∀ k : K.toSubgroup, ((π k : K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) :
      Γ ⧸ V.toSubgroup) = QuotientGroup.mk' V.toSubgroup k :=
    fun k => MonoidHom.subgroupMap_apply_coe _ _ k
  haveI : Nontrivial (K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) := by
    obtain ⟨k, hkK, hkV⟩ := Set.not_subset.mp hn
    refine ⟨⟨π ⟨k, hkK⟩, 1, fun h => hkV ?_⟩⟩
    have := congrArg Subtype.val h
    rw [hπk] at this
    exact (QuotientGroup.eq_one_iff k).mp this
  have hQ : IsPGroup l (K.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) := by
    intro q
    obtain ⟨k, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ q
    obtain ⟨e, he⟩ := hp k k.2
    refine ⟨e, ?_⟩
    show (π k) ^ l ^ e = 1
    rw [← map_pow]
    apply Subtype.ext
    rw [hπk]
    exact (QuotientGroup.eq_one_iff _).mpr (by simpa using he)
  obtain ⟨φ, hφ⟩ := exists_hom l _ hQ
  let ψ : K.toSubgroup →* Multiplicative (ZMod l) := φ.comp π
  have hψopen : IsOpen (ψ.ker : Set K.toSubgroup) := by
    refine Subgroup.isOpen_mono (H₁ := V.toSubgroup.comap K.toSubgroup.subtype) ?_ ?_
    · intro y hy
      rw [MonoidHom.mem_ker]
      have : π y = 1 := by
        apply Subtype.ext
        rw [hπk]
        exact (QuotientGroup.eq_one_iff _).mpr hy
      show φ (π y) = 1
      rw [this, map_one]
    · exact V.toOpenSubgroup.isOpen.preimage continuous_subtype_val
  refine lt_of_le_of_ne (Subgroup.map_mono (fr_le l h K)) fun heq => hφ ?_
  rw [eq_top_iff]
  intro q _
  obtain ⟨k, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ q
  have hk : QuotientGroup.mk' V.toSubgroup (k : Γ) ∈
      (fr l h K).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ k.2
  obtain ⟨f, hf, hfk⟩ := Subgroup.mem_map.mp hk
  obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hf
  have hf'ψ : f' ∈ ψ.ker := (Subgroup.mem_iInf.mp hf') ⟨ψ, hψopen⟩
  have hπeq : π k = π f' := by
    apply Subtype.ext
    rw [hπk, hπk]
    exact hfk.symm
  rw [MonoidHom.mem_ker] at hf'ψ ⊢
  show φ (π k) = 1
  rw [hπeq]
  exact hf'ψ

private theorem pow_mem (l : ℕ) [CompactSpace Γ] (H : Subgroup Γ) (V : OpenNormalSubgroup Γ)
    (hV : PL l H ≤ V.toSubgroup) : ∀ k ∈ H, ∃ e : ℕ, k ^ l ^ e ∈ V.toSubgroup := by
  intro k hk
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup}
  haveI : Nonempty ι := ⟨⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ, isNormal' := inferInstance },
    fun h _ => ⟨0, Subgroup.mem_top _⟩⟩⟩
  let t : ι → Set Γ := fun i => (i.1.toSubgroup : Set Γ)
  have hdir : Directed (· ⊇ ·) t := by
    intro i j
    have hopen : IsOpen ((i.1.toSubgroup ⊓ j.1.toSubgroup : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.coe_inf]
      exact i.1.toOpenSubgroup.isOpen.inter j.1.toOpenSubgroup.isOpen
    let U : OpenNormalSubgroup Γ :=
      { toSubgroup := i.1.toSubgroup ⊓ j.1.toSubgroup, isOpen' := hopen, isNormal' := inferInstance }
    have hU : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U.toSubgroup := by
      intro h hh
      obtain ⟨e1, h1⟩ := i.2 h hh
      obtain ⟨e2, h2⟩ := j.2 h hh
      refine ⟨e1 + e2, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
      · rw [pow_add, pow_mul]
        exact Subgroup.pow_mem _ h1 _
      · rw [pow_add, mul_comm, pow_mul]
        exact Subgroup.pow_mem _ h2 _
    exact ⟨⟨U, hU⟩, fun x hx => (Subgroup.mem_inf.mp hx).1, fun x hx => (Subgroup.mem_inf.mp hx).2⟩
  have hclosed : ∀ i : ι, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hVc : IsCompact ((V.toSubgroup : Set Γ)ᶜ) :=
    V.toOpenSubgroup.isOpen.isClosed_compl.isCompact
  have hempty : (V.toSubgroup : Set Γ)ᶜ ∩ ⋂ i : ι, t i = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxV, hx⟩
    apply hxV
    apply hV
    simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf]
    intro U hU
    exact Set.mem_iInter.mp hx ⟨U, hU⟩
  obtain ⟨i, hi⟩ := hVc.elim_directed_family_closed t hclosed hempty hdir
  obtain ⟨e, he⟩ := i.2 k hk
  refine ⟨e, ?_⟩
  by_contra hne
  have hmem : k ^ l ^ e ∈ (V.toSubgroup : Set Γ)ᶜ ∩ t i := ⟨hne, he⟩
  rw [hi] at hmem
  exact hmem

end UpperTheory.V.Pa.FrattiniSubgroup

open UpperTheory.V.Pa.FrattiniSubgroup in
theorem UpperTheory.V.Pa.frat :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H : OpenNormalSubgroup Γ), PhiCond Γ l → ∃ W : ℕ → OpenNormalSubgroup Γ, (∀ N, (W N).toSubgroup ≤ H.toSubgroup) ∧ ∀ V : OpenNormalSubgroup Γ, PL l H.toSubgroup ≤ V.toSubgroup → ∀ᶠ N in atTop, (W N).toSubgroup ≤ V.toSubgroup := by
  intro l _ Γ _ _ _ _ _ H hΦ
  let W : ℕ → OpenNormalSubgroup Γ := fun N =>
    Nat.rec (motive := fun _ => OpenNormalSubgroup Γ) H (fun _ K => fr l hΦ K) N
  have hWs : ∀ N, W (N + 1) = fr l hΦ (W N) := fun N => rfl
  have hanti : ∀ N, (W (N + 1)).toSubgroup ≤ (W N).toSubgroup := fun N => by
    rw [hWs]
    exact fr_le l hΦ (W N)
  have hmono : Antitone fun N => (W N).toSubgroup := antitone_nat_of_succ_le hanti
  refine ⟨W, fun N => hmono (Nat.zero_le N), fun V hV => ?_⟩
  have hpow := pow_mem l H.toSubgroup V hV
  haveI : Finite (Γ ⧸ V.toSubgroup) :=
    (inferInstance : Finite (Γ ⧸ (V.toOpenSubgroup : Subgroup Γ)))
  obtain ⟨m, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt : WellFounded (α := Subgroup (Γ ⧸ V.toSubgroup)) (· < ·)).has_min
      (Set.range fun N => (W N).toSubgroup.map (QuotientGroup.mk' V.toSubgroup)) ⟨_, ⟨0, rfl⟩⟩
  have hN : (W N).toSubgroup ≤ V.toSubgroup := by
    by_contra hn
    refine hmin _ ⟨N + 1, rfl⟩ ?_
    show (W (N + 1)).toSubgroup.map (QuotientGroup.mk' V.toSubgroup) <
      (W N).toSubgroup.map (QuotientGroup.mk' V.toSubgroup)
    rw [hWs]
    exact fr_lt l hΦ (W N) V (fun k hk => hpow k (hmono (Nat.zero_le N) hk)) hn
  exact Filter.eventually_atTop.mpr ⟨N, fun M hM => (hmono hM).trans hN⟩
