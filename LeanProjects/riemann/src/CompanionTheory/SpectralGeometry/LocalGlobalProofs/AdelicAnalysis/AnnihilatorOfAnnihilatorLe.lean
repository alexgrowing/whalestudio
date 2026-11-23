import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CofinalDual

theorem card_le_of_pairing {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have hne : ∀ x y, b x y ≠ 0 := fun x y h => by
    have := hn x y
    simp [h] at this
  have h0 : ∀ x, b x 0 = 1 := fun x => by
    have := hr x 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne x 0)).1 this.symm
  let f : A → AddChar B ℂ := fun x =>
    { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }
  have hf : Function.Injective f := by
    intro x x' h
    have e : ∀ y, b x y = b x' y := fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h
    have : x - x' = 0 := hk _ fun y => by
      have h1 := hl (x - x') x' y
      rw [sub_add_cancel, e y] at h1
      exact (mul_eq_right₀ (hne x' y)).1 h1.symm
    exact sub_eq_zero.1 this
  have e : Nat.card (AddChar B ℂ) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  exact e ▸ Nat.card_le_card_of_injective f hf

theorem index_eq_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by
  have hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y := by
    intro x x' y h
    have hm : -x + x' ∈ N := QuotientAddGroup.eq.1 h
    have := hl x (-x + x') y
    rw [add_neg_cancel_left, (hN _).1 hm y, mul_one] at this
    exact this.symm
  have hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y' := by
    intro x y y' h
    have hm : -y + y' ∈ M := QuotientAddGroup.eq.1 h
    have := hr x y (-y + y')
    rw [add_neg_cancel_left, (hM _).1 hm x, mul_one] at this
    exact this.symm
  let b : X ⧸ N → Y ⧸ M → ℂ := fun p q => c (Quotient.out p) (Quotient.out q)
  have hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y := fun x y => by
    change c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y
    rw [hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]
  have bn : ∀ p q, ‖b p q‖ = 1 := fun p q => hn _ _
  have bl : ∀ p p' q, b (p + p') q = b p q * b p' q := by
    intro p p' q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective p'
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hl]
  have br : ∀ p q q', b p (q + q') = b p q * b p q' := by
    intro p q q'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hr]
  have k1 : ∀ p, (∀ q, b p q = 1) → p = 0 := by
    intro p h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    exact (QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])
  have k2 : ∀ q, (∀ p, b p q = 1) → q = 0 := by
    intro q h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])
  exact le_antisymm (card_le_of_pairing b bn bl br k1)
    (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q')
      (fun q p p' => bl p p' q) k2)

theorem relIndex_ne_zero_of_isOpen {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (S T : AddSubgroup V) (hS : IsOpen (S : Set V))
    (hT : IsCompact (T : Set V)) : S.relIndex T ≠ 0 := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T) :=
    hS.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : (S.addSubgroupOf T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact this.index_ne_zero

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by
  classical
  haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩
  haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)
  let o : T ⧸ S.addSubgroupOf T → T := fun q => Quotient.out q
  have ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q := fun q => QuotientAddGroup.out_eq' q
  let C : T ⧸ S.addSubgroupOf T → Set V := fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)
  have hU : (T : Set V) = ⋃ q, C q := by
    ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩
      have h := QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))
      exact AddSubgroup.mem_addSubgroupOf.1 h
    · rintro ⟨q, hq⟩
      have h1 : -(o q : V) + v ∈ T := hST hq
      have := T.add_mem (o q).2 h1
      simpa using this
  have hd : Pairwise (Function.onFun Disjoint C) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have h1 : -(o q : V) + v ∈ S := hv
    have h2 : -(o q' : V) + v ∈ S := hv'
    have h3 : -(o q : V) + (o q' : V) ∈ S := by
      have := S.sub_mem h1 h2
      have e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V) := by abel
      rwa [e] at this
    have h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T) :=
      QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))
    rw [ho, ho] at h4
    exact h4
  have hm : ∀ q, MeasurableSet (C q) := fun q =>
    (hS.preimage (continuous_const.add continuous_id)).measurableSet
  have hc : ∀ q, μ (C q) = μ S := fun q => measure_preimage_add μ _ _
  rw [hU, measure_iUnion hd hm, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

def perpSub {V : Type} [AddCommGroup V] (χ : V → V → ℂ) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  add_mem' := by
    intro y y' hy hy' x hx
    rw [hs, ha, hs y, hs y', hy x hx, hy' x hx, one_mul]
  zero_mem' := by
    intro x _
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have := ha 0 0 x
    rw [add_zero] at this
    rw [hs]
    exact (mul_eq_left₀ hne).1 this.symm
  neg_mem' := by
    intro y hy x hx
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have h0 : χ 0 x = 1 := by
      have := ha 0 0 x
      rw [add_zero] at this
      exact (mul_eq_left₀ hne).1 this.symm
    have := ha y (-y) x
    rw [add_neg_cancel, h0, hs y x, hy x hx, one_mul] at this
    rw [hs]
    exact this.symm

theorem relIndex_eq_of_pairing {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by
  haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩
  haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩
  refine index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _)
    (fun x x' y => ha _ _ _)
    (fun x y y' => by
      change χ x ((y : V) + y') = _
      rw [hs, ha, hs y, hs y']) _ _ ?_ ?_
  · intro x
    rw [AddSubgroup.mem_addSubgroupOf, hX x x.2]
    exact ⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩
  · intro y
    rw [AddSubgroup.mem_addSubgroupOf, hY y y.2]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

theorem selfDual_of_between : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  intro V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂
  let Q : AddSubgroup V → AddSubgroup V := perpSub χ hs hn ha
  have hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1 := fun _ _ => Iff.rfl
  have hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A := fun _ => rfl
  have anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A :=
    fun A B h y hy x hx => hy x (h hx)
  have hself : ∀ A : AddSubgroup V, A ≤ Q (Q A) := fun A x hx y hy => by
    rw [hs]
    exact hy x hx
  have placeRankTwoOne : Q L₂ ≤ Q L₁ := anti _ _ (h1.trans h2)
  have P2 : Q L₂ ≤ Q L := anti _ _ h2
  have P1 : Q L ≤ Q L₁ := anti _ _ h1
  have LM : L ≤ Q (Q L) := hself L
  have ML : Q (Q L) ≤ L₂ := fun z hz => dd₂ (anti _ _ P2 hz)
  have n0 : L₁.relIndex L₂ ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂
  have p0 : (Q L₂).relIndex (Q L₁) ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁
  have ea := AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2
  have ep := AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1
  have ek := AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML
  have a0 : L₁.relIndex L ≠ 0 := fun h => n0 (by rw [← ea, h, zero_mul])
  have a'0 : L.relIndex L₂ ≠ 0 := fun h => n0 (by rw [← ea, h, mul_zero])
  have q0 : (Q L₂).relIndex (Q L) ≠ 0 := fun h => p0 (by rw [← ep, h, zero_mul])
  have q'0 : (Q L).relIndex (Q L₁) ≠ 0 := fun h => p0 (by rw [← ep, h, mul_zero])
  have m0 : (Q (Q L)).relIndex L₂ ≠ 0 := fun h => a'0 (by rw [← ek, h, mul_zero])
  have kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1 := fun x =>
    ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by
      rw [hs]
      exact h y hy⟩
  have e1 : L₁.relIndex L = (Q L).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L y) a0 q'0
  have e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L) :=
    relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L)
      (fun x _ => by
        rw [hQ]
        exact forall₂_congr fun y _ => by rw [hs])
      (fun y _ => hQ L₂ y) m0 q0
  have e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L₂ y) n0 p0
  have e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L) := by
    have : L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L) := by
      rw [ea, e3, ← ep, e1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this
  have hk : L.relIndex (Q (Q L)) = 1 := by
    have : L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂ := by
      rw [ek, one_mul, e2, e4]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this
  have MLe : Q (Q L) ≤ L := AddSubgroup.relIndex_eq_one.1 hk
  have oP : IsOpen (Q L : Set V) := AddSubgroup.isOpen_mono P2 oP₂
  refine ⟨?_, oP, MLe, ?_⟩
  · exact cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1
  · change μ L * μ (Q L) = 1
    change μ L₂ * μ (Q L₂) = 1 at m₂
    rw [measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0,
      ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.CofinalDual
