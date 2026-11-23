import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LevelS
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.StrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GwTame
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

open scoped Pointwise in
private theorem ch_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (v : G F Ω)
    (B : ValuationSubring Ω) (g : G F Ω) (hg : g ∈ Ine (F := F) (v • B)) : v⁻¹ * g * v ∈ Ine (F := F) B := by
  have hl : IsLift (RingEquiv.refl F) v.toRingEquiv := fun y => v.commutes y
  have hA : ∀ x : Ω, v.toRingEquiv x ∈ v • B ↔ x ∈ B := fun x => by
    show v • x ∈ v • B ↔ x ∈ B
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have e : v⁻¹ * g * v = conjGal hl g := AlgEquiv.ext fun _ => rfl
  rw [e]
  exact conjGal_mem_Ine hl hA hg

private theorem ch_idx {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (K : Subgroup H) (hK : ¬ l ∣ K.index)
    (χ : H →* (ZMod (l ^ 1))ˣ) : ¬ l ∣ (K ⊓ χ.ker).index := by
  intro h
  rw [← Subgroup.relIndex_mul_index (inf_le_left : K ⊓ χ.ker ≤ K), Subgroup.inf_relIndex_left, hl.out.dvd_mul] at h
  refine h.elim (fun h => ?_) hK
  replace h := h.trans (Subgroup.relIndex_dvd_index_of_normal _ _)
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [Subgroup.index_ker] at h
  have h2 := h.trans (Subgroup.card_subgroup_dvd_card χ.range)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h2
  have h3 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h2
  omega

private def chZero {H k : Type} [Group H] [Field k] (K : Subgroup H) (χ : H →* kˣ) (z : H → k)
    (hz : ∀ s t, z (s * t) = z s + χ s * z t) : Subgroup H where
  carrier := {g | g ∈ K ∧ z g = 0}
  one_mem' := ⟨K.one_mem, by simpa using hz 1 1⟩
  mul_mem' {a b} ha hb := ⟨K.mul_mem ha.1 hb.1, by rw [hz, ha.2, hb.2, mul_zero, add_zero]⟩
  inv_mem' {a} ha := ⟨K.inv_mem ha.1, by
    have h1 : z 1 = 0 := by simpa using hz 1 1
    have h2 := hz a⁻¹ a
    rw [inv_mul_cancel, h1, ha.2, mul_zero, add_zero] at h2
    exact h2.symm⟩

private theorem chZero_normal {H k : Type} [Group H] [Field k] (K : Subgroup H) [hK : K.Normal] (χ : H →* kˣ)
    (hχ : ∀ g ∈ K, χ g = 1) (z : H → k) (hz : ∀ s t, z (s * t) = z s + χ s * z t) : (chZero K χ z hz).Normal :=
  ⟨fun n hn g => ⟨hK.conj_mem n hn.1 g, by
    have h1 : z 1 = 0 := by simpa using hz 1 1
    have h2 := hz g g⁻¹
    rw [mul_inv_cancel, h1] at h2
    rw [hz, hz, hn.2, map_mul, hχ n hn.1, mul_one, mul_zero, add_zero, ← h2]⟩⟩

private theorem ch_card {k V : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V] {n : ℕ} (h : Module.rank k V ≤ n) :
    Finite V ∧ Nat.card V ≤ Nat.card k ^ n := by
  haveI : Module.Finite k V := Module.rank_lt_aleph0_iff.1 (h.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨Module.finite_of_finite k, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := k) (V := V)]
  exact Nat.pow_le_pow_right Nat.card_pos (Module.finrank_le_of_rank_le h)

private theorem ch_rank {k V : Type} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Finite V] {n : ℕ}
    (h : Nat.card V ≤ Nat.card k ^ n) : Module.rank k V ≤ n := by
  haveI : Module.Finite k V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k) (V := V)] at h
  rw [← Module.finrank_eq_rank]
  exact Nat.cast_le.2 ((Nat.pow_le_pow_iff_right Finite.one_lt_card).1 h)

private theorem ch_unr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (k : Type) [Field k] [Finite k] [CharP k l] (K : Subgroup (G F Ω)) [K.Normal] (ho : IsOpen (K : Set (G F Ω)))
    (hi : ¬ l ∣ K.index) (χ : G F Ω →* kˣ) (hχ : ∀ g ∈ K, χ g = 1) (C₀ : ℕ) (hC : clRk l K ≤ C₀) (Y : Type)
    (f : Y → G F Ω → k) (h1 : ∀ y, IsLocallyConstant (f y)) (h2 : ∀ y s t, f y (s * t) = f y s + χ s * f y t)
    (h3 : ∀ y (A : ValuationSubring Ω), ∀ g ∈ Ine (F := F) A ⊓ K, f y g = 0)
    (h4 : ∀ a b m, (∀ g, f a g - f b g = χ g * m - m) → a = b) : Nat.card Y ≤ Nat.card k ^ C₀ := by
  let N : Subgroup (G F Ω) := Subgroup.normalClosure (⋃ A : ValuationSubring Ω, (Ine (F := F) A ⊓ K : Subgroup (G F Ω)))
  have hN : ∀ y, N ≤ chZero K χ (f y) (h2 y) := fun y => by
    haveI := chZero_normal K χ hχ (f y) (h2 y)
    exact Subgroup.normalClosure_le_normal (Set.iUnion_subset fun A g hg => ⟨hg.2, h3 y A g hg⟩)
  have hNK : N ≤ K := Subgroup.normalClosure_le_normal (Set.iUnion_subset fun A g hg => hg.2)
  let κ : G F Ω ⧸ N →* kˣ := QuotientGroup.lift N χ fun g hg => hχ g (hNK hg)
  let loc : ∀ _ : Empty, G F Ω ⧸ N →* G F Ω ⧸ N := fun _ => MonoidHom.id _
  have hr := strGen F Ω l k ⊤ K le_top ho (by rwa [Subgroup.relIndex_top_right]) (G F Ω ⧸ N)
    ((QuotientGroup.mk' N).comp (⊤ : Subgroup (G F Ω)).subtype) (QuotientGroup.continuous_mk.comp continuous_subtype_val)
    ((QuotientGroup.mk'_surjective N).comp fun g => ⟨⟨g, trivial⟩, rfl⟩) Empty (fun _ => G F Ω ⧸ N) loc κ
    (fun u hu => hχ u.1 hu) (fun A u ha hb => Or.inl ((QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure (Set.mem_iUnion.2 ⟨A, ha, hb⟩))))
  rw [Nat.card_of_isEmpty, Cardinal.lift_id, Nat.cast_zero, add_zero] at hr
  obtain ⟨hfin, hcard⟩ := ch_card (hr.trans hC)
  let z : Y → G F Ω ⧸ N → k := fun y => Quotient.lift (f y) fun a b hab => by
    have e := h2 y a (a⁻¹ * b)
    rw [(hN y (QuotientGroup.leftRel_apply.1 hab)).2, mul_inv_cancel_left, mul_zero, add_zero] at e
    exact e.symm
  have hz : ∀ y, (z y, (0 : Empty → k)) ∈ Z1C loc (chRep κ) fun _ => ⊥ := fun y =>
    ⟨fun s => (QuotientGroup.isQuotientMap_mk N).isOpen_preimage.1 (h1 y s), fun s t => by
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective t
      exact h2 y s t, fun v => v.elim⟩
  refine (Nat.card_le_card_of_injective (fun y => (Submodule.Quotient.mk ⟨_, hz y⟩ : H1C loc (chRep κ) fun _ => ⊥))
    fun a b hab => ?_).trans hcard
  obtain ⟨m, hm, -⟩ := (Submodule.Quotient.eq _).1 hab
  exact h4 a b m fun g => hm (QuotientGroup.mk g)

private theorem ch_trace (R k : Type) [Field R] [Field k] [Finite k] [Algebra R k] :
    ∃ τ : k ≃+ TDual R k, ∀ a m, τ a m = Algebra.trace R k (a * m) := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  haveI : Module.Finite R k := Module.Finite.of_finite
  exact ⟨((Algebra.traceForm R k).toDual (traceForm_nondegenerate R k)).toAddEquiv, fun a m => rfl⟩

open scoped Classical in
private theorem ch_fix {k I T : Type} [Field k] [Finite k] (u : I → kˣ) (e : T → k) (he : Function.Injective e)
    (h : ∀ t i, u i * e t = e t) : Nat.card T ≤ Nat.card k ^ (if ∀ i, u i = 1 then 1 else 0) := by
  split_ifs with hu
  · rw [pow_one]
    exact Nat.card_le_card_of_injective e he
  · obtain ⟨i, hi⟩ := not_forall.1 hu
    have h0 : ∀ t, e t = 0 := fun t => by
      by_contra h'
      exact hi (Units.ext (mul_right_cancel₀ h' ((h t i).trans (one_mul _).symm)))
    haveI : Subsingleton T := ⟨fun a b => he ((h0 a).trans (h0 b).symm)⟩
    rw [pow_zero]
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance

theorem UpperTheory.V.GC.character_H1_galois_quotient :
    Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], IsTotallyReal F → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (κ : Γ →* kˣ), (∀ g ∈ (K ⊓ (cycMod F Ω l 1).ker), κ (π g) = 1) →
    ∀ c : InfinitePlace F → G F Ω, (∀ w, IsCCAt w (c w)) → ∀ (A : S → ValuationSubring Ω), (∀ v, IsPlaceOver (A v) v.1) → ∀ C₀ : ℕ, clRk l (K ⊓ (cycMod F Ω l 1).ker) ≤ C₀ →
    ∀ (V : Type) (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] (loc : ∀ v, Gv v →* Γ),
    Module.rank k (H1C loc (chRep κ) fun _ => ⊤) + (Nat.card {w // κ (π (c w)) = 1} : Cardinal) ≤
      ((Nat.card {_u : Unit // κ = 1} + C₀ + finrank ℚ F + Nat.card {v : S // ∀ g ∈ Dec (F := F) (A v), κ (π g) = cycF F Ω l k g} : ℕ) : Cardinal) := by
  intro P F Ω _ _ _ _ _ l hl hF S K Γ _ _ _ _ _ _ π h k _ _ hch κ hκ c hc A hA C₀ hC V Gv _ _ loc
  classical
  obtain ⟨S', p, hSS, hp, hps, hπ, -⟩ := levelS F Ω l S K Γ π h
  have hπ' : ∀ g, p (toGS Ω _ g) = π g := fun g => DFunLike.congr_fun hπ g
  have hS' : ContainsAbove S' l := fun v hv => hSS (h.above v hv)
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (Ω := Ω) (r := 1) hS'
  have hμ' : ∀ g, μ (toGS Ω _ g) = cycMod F Ω l 1 g := fun g => DFunLike.congr_fun hμ g
  haveI := h.normal
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact hl.out⟩
  letI : Algebra (ZMod (l ^ 1)) k := @ZMod.algebra k _ (l ^ 1) (by rwa [pow_one])
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have ho : IsOpen ((K ⊓ (cycMod F Ω l 1).ker : Subgroup (G F Ω)) : Set (G F Ω)) :=
    h.isOpen.inter ((isOpen_discrete {1}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod)
  have hi := ch_idx l K h.idx (cycMod F Ω l 1)
  let ω : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* kˣ := (Units.map (algebraMap (ZMod (l ^ 1)) k).toMonoidHom).comp μ
  have hω : ∀ g, ω (toGS Ω _ g) = cycF F Ω l k g := fun g => Units.ext (by
    show algebraMap (ZMod (l ^ 1)) k (μ (toGS Ω _ g)) = _
    rw [hμ']
    exact RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod (l ^ 1)) k)
      (ZMod.castHom (dvd_pow_self l one_ne_zero) k)) _)
  let κ' : GS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) →* kˣ := (κ.comp p)⁻¹ * ω
  have hκ' : ∀ g, κ' (toGS Ω _ g) = (κ (π g))⁻¹ * cycF F Ω l k g := fun g => by
    show (κ (p (toGS Ω _ g)))⁻¹ * ω (toGS Ω _ g) = _
    rw [hπ', hω]
  have hK1 : ∀ g ∈ K ⊓ (cycMod F Ω l 1).ker, κ' (toGS Ω _ g) = 1 := fun g hg => by
    rw [hκ', hκ g hg, cycF, MonoidHom.comp_apply, show cycMod F Ω l 1 g = 1 from hg.2, map_one, inv_one, mul_one]
  let ρ : Representation (ZMod (l ^ 1)) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 F)))) k := Loc.resCoef (ZMod (l ^ 1)) (chRep κ')
  have hρa : ∀ g m, ρ g m = κ' g * m := fun _ _ => rfl
  have hρ : ContAction ρ := by
    have h1 : IsLocallyConstant fun g => κ' (toGS Ω _ g) := by
      rw [IsLocallyConstant.iff_exists_open]
      intro g
      refine ⟨(fun x => g⁻¹ * x) ⁻¹' (K ⊓ (cycMod F Ω l 1).ker : Subgroup (G F Ω)), ho.preimage (by fun_prop),
        by simp, fun x hx => ?_⟩
      have := hK1 _ hx
      rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at this
      exact this.symm
    have h2 : IsLocallyConstant κ' := fun s => (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (h1 s)
    exact (continuous_of_discreteTopology (f := fun q : k × k => q.1 * q.2)).comp
      (((h2.comp Units.val).continuous.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨τ, hτ⟩ := ch_trace (ZMod (l ^ 1)) k
  have hτe : ∀ g a, twDual μ ρ g (τ a) = τ (κ (p g) * a) := fun g a => TDual.ext fun m => by
    rw [twDual_apply, hτ, hτ, hρa, ← smul_eq_mul, ← map_smul, Algebra.smul_def]
    congr 1
    have e : κ' g⁻¹ * ω g = κ (p g) := by
      show (κ (p g⁻¹))⁻¹ * ω g⁻¹ * ω g = _
      rw [map_inv, map_inv, map_inv, inv_inv, inv_mul_cancel_right]
    rw [← e, Units.val_mul]
    show (ω g : k) * _ = _
    ring
  let A' : S' → ValuationSubring Ω := fun v => if hv : v.1 ∈ S then A ⟨v.1, hv⟩ else placeOf Ω v.1
  have hA' : ∀ v, IsPlaceOver (A' v) v.1 := fun v => by
    by_cases hv : v.1 ∈ S
    · simp only [A', dif_pos hv]
      exact hA ⟨v.1, hv⟩
    · simp only [A', dif_neg hv]
      exact isPlaceOver_placeOf Ω v.1
  choose s hs using Submodule.Quotient.mk_surjective
    ((continuousCoboundaries1 (chRep κ) fun _ : V => (⊤ : Submodule k k)).comap (Z1C loc (chRep κ) fun _ => ⊤).subtype)
  let f : (H1C loc (chRep κ) fun _ => ⊤) → Z1 (twDual μ ρ) := fun x => ⟨fun g => τ ((s x).1.1 (p g)),
    (((s x).2.1.comp_continuous hp).comp τ).continuous, fun a b => by
      beta_reduce
      rw [map_mul p, (s x).2.2.1, map_add, hτe, chRep_apply]⟩
  obtain ⟨hfin, hle⟩ := gwTame P l h.odd S S' h.above hS' A' hA' _ ho hi k ρ hρ μ hμ
    (fun g hg => ⟨LinearMap.ext fun m => by rw [hρa, hK1 g hg, Units.val_one, one_mul]; rfl, (hμ' g).trans hg.2⟩) c hc _ f
    (fun a b hab => by
      obtain ⟨φ, hφ⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 hab)
      obtain ⟨m, rfl⟩ := τ.surjective φ
      rw [← hs a, ← hs b]
      refine (Submodule.Quotient.eq _).2 ⟨m, fun g => ?_, fun _ => trivial⟩
      obtain ⟨g, rfl⟩ := hps g
      have e : τ ((s a).1.1 (p g)) - τ ((s b).1.1 (p g)) = _ := hφ g
      rw [hτe, ← map_sub, ← map_sub] at e
      exact τ.injective e)
    (fun x q hq g hg => by
      show τ ((s x).1.1 (p (toGS Ω _ g))) = 0
      have e : π g = 1 := by
        rw [← MonoidHom.mem_ker, h.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨q.1, hq, A' q, hA' q, hg.1, hg.2.1⟩
      have e1 : (s x).1.1 1 = 0 := by simpa using (s x).2.2.1 1 1
      rw [hπ', e, e1, map_zero])
  have b1 : Nat.card {y : H1 ρ // ∃ z : Z1 ρ, Submodule.Quotient.mk z = y ∧
      ∀ v : S', ∀ g ∈ Ine (F := F) (A' v) ⊓ (K ⊓ (cycMod F Ω l 1).ker), z.1 (toGS Ω _ g) = 0} ≤ Nat.card k ^ C₀ := by
    refine ch_unr l k _ ho hi (κ'.comp (toGS Ω _)) hK1 C₀ hC _ (fun y g => y.2.choose.1 (toGS Ω _ g))
      (fun y => ((IsLocallyConstant.iff_continuous _).2 y.2.choose.2.1).comp_continuous (continuous_toGS Ω _))
      (fun y s t => by rw [map_mul, y.2.choose.2.2]; rfl) (fun y B g hg => ?_) fun a b m hm => ?_
    · have hz : ∀ s t, y.2.choose.1 (toGS Ω _ (s * t)) = y.2.choose.1 (toGS Ω _ s) +
          (κ'.comp (toGS Ω _)) s * y.2.choose.1 (toGS Ω _ t) := fun s t => by rw [map_mul, y.2.choose.2.2]; rfl
      have h1 := (chZero (K ⊓ (cycMod F Ω l 1).ker) _ (fun g => y.2.choose.1 (toGS Ω _ g)) hz).one_mem
      obtain ⟨p1, p2, -⟩ := Base.places F Ω l B
      by_cases hB : B = ⊤
      · have e : g = 1 := Subgroup.mem_bot.1 ((p2 hB).1 ▸ hg.1)
        rw [e]
        exact h1.2
      obtain ⟨v, hv⟩ := p1 hB
      by_cases hvS : v ∈ S'
      · obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver (hA' ⟨v, hvS⟩) hv
        have h2 : σ⁻¹ * g * σ ∈ K ⊓ (cycMod F Ω l 1).ker := Subgroup.Normal.conj_mem' inferInstance _ hg.2 _
        have h3 := (chZero_normal (K ⊓ (cycMod F Ω l 1).ker) (κ'.comp (toGS Ω _)) hK1
          (fun g => y.2.choose.1 (toGS Ω _ g)) hz).conj_mem (σ⁻¹ * g * σ)
          ⟨h2, y.2.choose_spec.2 ⟨v, hvS⟩ _ ⟨ch_conj σ _ g hg.1, h2⟩⟩ σ
        rw [show σ * (σ⁻¹ * g * σ) * σ⁻¹ = g by group] at h3
        exact h3.2
      · have e : toGS Ω (S' : Set (HeightOneSpectrum (𝓞 F))) g = toGS Ω _ 1 := by
          rw [map_one]
          refine (QuotientGroup.eq_one_iff _).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
          simp only [Set.mem_iUnion]
          exact ⟨v, hvS, B, hv, hg.1⟩
        show y.2.choose.1 (toGS Ω _ g) = 0
        rw [e]
        exact h1.2
    · refine Subtype.ext (a.2.choose_spec.1.symm.trans (Eq.trans ?_ b.2.choose_spec.1))
      refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      exact hm g
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card k ^ Nat.card {_u : Unit // κ = 1} := by
    refine (ch_fix (fun g => κ (p g)) (fun t : H0 (twDual μ ρ) => τ.symm t.1)
      (τ.symm.injective.comp Subtype.val_injective) fun t g => τ.injective ?_).trans
      (Nat.pow_le_pow_right Nat.card_pos ?_)
    · rw [← hτe, τ.apply_symm_apply]
      exact t.2 g
    · split_ifs with h1
      · haveI : Nonempty {_u : Unit // κ = 1} := ⟨⟨(), MonoidHom.ext fun g => by
          obtain ⟨g, rfl⟩ := hps g
          exact h1 g⟩⟩
        exact Nat.card_pos
      · exact Nat.zero_le _
  have b3 : (∏ v : S', if v.1 ∈ S then Nat.card (H0 (ρ.comp (locFam S' A' v))) else 1) ≤
      Nat.card k ^ Nat.card {v : S // ∀ g ∈ Dec (F := F) (A v), κ (π g) = cycF F Ω l k g} := by
    let Q : S' → Prop := fun v => v.1 ∈ S ∧ ∀ g ∈ Dec (F := F) (A' v), κ (π g) = cycF F Ω l k g
    have h1 : Nat.card {v // Q v} ≤ Nat.card {v : S // ∀ g ∈ Dec (F := F) (A v), κ (π g) = cycF F Ω l k g} :=
      Nat.card_le_card_of_injective (fun v => ⟨⟨v.1.1, v.2.1⟩, by
        have := v.2.2
        simp only [A', dif_pos v.2.1] at this
        exact this⟩) fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj (Subtype.mk.inj hab)))
    refine le_trans ?_ (Nat.pow_le_pow_right Nat.card_pos h1)
    rw [Nat.card_eq_fintype_card (α := {v // Q v}), Fintype.card_subtype, Finset.card_filter,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun v _ => ?_
    by_cases hv : v.1 ∈ S
    · rw [if_pos hv]
      refine (ch_fix (fun g : Dec (F := F) (A' v) => κ' (toGS Ω _ g.1)) (fun t : H0 (ρ.comp (locFam S' A' v)) => t.1)
        Subtype.val_injective fun t g => t.2 g).trans (Nat.pow_le_pow_right Nat.card_pos ?_)
      split_ifs with h2 h3
      · exact le_rfl
      · exact (h3 ⟨hv, fun g hg => inv_mul_eq_one.1 ((hκ' g).symm.trans (h2 ⟨g, hg⟩))⟩).elim
      all_goals exact Nat.zero_le _
    · rw [if_neg hv]
      exact Nat.one_le_pow _ _ Nat.card_pos
  have b4 : archH0Card S' ρ c ≤ Nat.card k ^ Nat.card {w // ¬ κ (π (c w)) = 1} := by
    rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one, Nat.card_eq_fintype_card (α := {w // ¬ κ (π (c w)) = 1}),
      Fintype.card_subtype, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum,
      Finset.filter_true_of_mem fun w _ => hF.isReal w]
    refine Finset.prod_le_prod' fun w _ => ?_
    refine (ch_fix (fun _ : Unit => κ' (toGS Ω _ (c w))) (fun t : {m : k // ρ (toGS Ω _ (c w)) m = m} => t.1)
      Subtype.val_injective fun t _ => t.2).trans (Nat.pow_le_pow_right Nat.card_pos ?_)
    by_cases h2 : ∀ _ : Unit, κ' (toGS Ω _ (c w)) = 1
    · rw [if_pos h2, if_pos]
      intro h3
      obtain ⟨j, hj, -⟩ := hc w
      have h4 : cycZ F Ω l (c w) = -1 := IsConjOm.cyc (E := F) (show IsConjOm (c w).toRingEquiv from ⟨j, hj⟩)
      have h5 := h2 ()
      rw [hκ', h3, inv_one, one_mul] at h5
      have h6 : (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
          ((PadicInt.toZModPow 1 : ℤ_[l] →+* ZMod (l ^ 1)) (cycZ F Ω l (c w) : ℤ_[l]ˣ)) = 1 := congrArg Units.val h5
      rw [h4, Units.val_neg, Units.val_one, map_neg, map_one, map_neg, map_one] at h6
      have h7 : ((2 : ℕ) : k) = 0 := by
        push_cast
        linear_combination -h6
      exact h.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((@CharP.cast_eq_zero_iff k _ l hch 2).1 h7))
    · rw [if_neg h2]
      exact Nat.zero_le _
  have b5 : Nat.card {w // ¬ κ (π (c w)) = 1} + Nat.card {w // κ (π (c w)) = 1} = finrank ℚ F := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Nat.sub_add_cancel (Fintype.card_subtype_le _), InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      ← InfinitePlace.card_add_two_mul_card_eq_rank, IsTotallyReal.nrComplexPlaces_eq_zero]
  have b6 := hle.trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b1 b2) b3) b4)
  rw [← pow_add, ← pow_add, ← pow_add] at b6
  refine (add_le_add_left (ch_rank b6) _).trans ?_
  rw [← Nat.cast_add, Nat.cast_le]
  omega
