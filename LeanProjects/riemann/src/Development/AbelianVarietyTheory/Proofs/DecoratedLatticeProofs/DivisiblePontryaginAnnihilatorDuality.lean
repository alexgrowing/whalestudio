import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave

namespace GlobalTheory.DualTransfer

theorem exists_hom {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A)
    (hM : ∀ a ∈ M, ∀ b, e a b = 1) :
    ∃ f : B →+ AddChar (A ⧸ M) ℂ, ∀ b (a : A), f b (a : A ⧸ M) = e a b := by
  have key : ∀ b (a a' : A), -a + a' ∈ M → e a b = e a' b := by
    intro b a a' h
    have ha : a' = a + (-a + a') := by abel
    rw [ha, h1, hM _ h b, mul_one]
  let ψ : B → AddChar (A ⧸ M) ℂ := fun b =>
    { toFun := fun q => Quotient.liftOn' q (fun a => e a b)
        (fun a a' h => key b a a' (QuotientAddGroup.leftRel_apply.mp h))
      map_zero_eq_one' := h3 b
      map_add_eq_mul' := by
        intro q q'
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
        obtain ⟨a', rfl⟩ := QuotientAddGroup.mk_surjective q'
        exact h1 a a' b }
  refine ⟨{ toFun := ψ, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h4 a
  · intro b b'
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h2 a b b'
  · intro b a
    rfl

theorem card_range {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (M : AddSubgroup A) (K : AddSubgroup B) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (f : B →+ AddChar (A ⧸ M) ℂ) (hf : ∀ b (a : A), f b (a : A ⧸ M) = e a b) :
    Nat.card f.range = Nat.card (B ⧸ K) := by
  have hker : f.ker = K := by
    ext b
    rw [AddMonoidHom.mem_ker, hK, AddChar.eq_zero_iff]
    constructor
    · intro h a
      rw [← hf]
      exact h _
    · intro h q
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [hf]
      exact h a
  rw [← hker]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv).symm

theorem exists_separating {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A) (K : AddSubgroup B)
    [Finite (A ⧸ M)] [Finite (B ⧸ K)]
    (hM : ∀ a, a ∈ M ↔ ∀ b, e a b = 1) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (H : AddSubgroup A) (hMH : M ≤ H) (x : A) (hx : x ∉ H) :
    ∃ b, (∀ u ∈ H, e u b = 1) ∧ e x b ≠ 1 := by
  classical
  obtain ⟨f, hf⟩ := exists_hom e h1 h2 h3 h4 M (fun a ha b => (hM a).mp ha b)
  obtain ⟨f', hf'⟩ := exists_hom (fun b a => e a b) (fun b b' a => h2 a b b')
    (fun b a a' => h1 a a' b) (fun b => h4 b) (fun a => h3 a) K (fun b hb a => (hK b).mp hb a)
  have c1 := card_range e M K hK f hf
  have c2 := card_range (fun b a => e a b) K M hM f' hf'
  have : Fintype (A ⧸ M) := Fintype.ofFinite _
  have : Fintype (B ⧸ K) := Fintype.ofFinite _
  have cA : Nat.card (AddChar (A ⧸ M) ℂ) = Nat.card (A ⧸ M) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have cB : Nat.card (AddChar (B ⧸ K) ℂ) = Nat.card (B ⧸ K) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have le1 : Nat.card f.range ≤ Nat.card (AddChar (A ⧸ M) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have le2 : Nat.card f'.range ≤ Nat.card (AddChar (B ⧸ K) ℂ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have htop : f.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by omega)
  set r := QuotientAddGroup.map M H (AddMonoidHom.id A) (fun a ha => hMH ha) with hr
  have : Finite (A ⧸ H) := Finite.of_surjective r (fun q => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨(a : A ⧸ M), rfl⟩)
  have hx0 : (x : A ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨ψ0, hψ0⟩ := AddChar.exists_apply_ne_zero.mpr hx0
  have hmem : ψ0.compAddMonoidHom r ∈ f.range := by
    rw [htop]
    exact AddSubgroup.mem_top _
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, fun u hu => ?_, ?_⟩
  · rw [← hf b u, hb, AddChar.compAddMonoidHom_apply]
    have hu0 : (u : A ⧸ H) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr hu
    show ψ0 (u : A ⧸ H) = 1
    rw [hu0]
    exact ψ0.map_zero_eq_one
  · rw [← hf b x, hb, AddChar.compAddMonoidHom_apply]
    exact hψ0

theorem finite_quot {G : Type} [AddCommGroup G] (A L₀ : AddSubgroup G) (N : ℕ) (hN : 0 < N)
    (tf : Function.Injective fun t : G => N • t)
    (hA : ∀ t ∈ A, N • t ∈ L₀)
    (fin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) :
    Finite (A ⧸ (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A) := by
  classical
  obtain ⟨R, hR, hcov⟩ := fin (N * N) (Nat.mul_pos hN hN)
  set S := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A with hS
  let c : G → A ⧸ S := fun r =>
    if h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u then
      ((Classical.choose h : A) : A ⧸ S) else 0
  have key : ∀ t : A, ∃ r ∈ R, c r = (t : A ⧸ S) := by
    intro t
    obtain ⟨r, hr, u, hu, htu⟩ := hcov _ (hA t t.2)
    have h : ∃ t : A, ∃ u ∈ L₀, N • (t : G) = r + (N * N) • u := ⟨t, u, hu, htu⟩
    refine ⟨r, hr, ?_⟩
    simp only [c, dif_pos h]
    obtain ⟨u', hu', ht'⟩ := Classical.choose_spec h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    refine ⟨u - u', L₀.sub_mem hu hu', ?_⟩
    apply tf
    show N • (N • (u - u')) = N • (((-Classical.choose h + t : A)) : G)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, smul_add, smul_neg, htu, ht', smul_smul, smul_sub]
    abel
  have hfin : Set.Finite (Set.univ : Set (A ⧸ S)) := by
    refine (hR.image c).subset ?_
    intro q _
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, hc⟩ := key t
    exact ⟨r, hr, hc⟩
  exact Set.finite_univ_iff.mp hfin

theorem mem_of_double_annihilator : ∀ {G : Type} [AddCommGroup G] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (X Y L₀ L₀' L : AddSubgroup G), L₀ ≤ X → L₀' ≤ Y → L ≤ X → (∀ u ∈ L₀, ∀ y ∈ L₀', χ u y = 1) → (∀ x ∈ X, (∀ y ∈ L₀', χ x y = 1) → x ∈ L₀) → (∀ y ∈ Y, (∀ u ∈ L₀, χ u y = 1) → y ∈ L₀') → (∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) → (∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y) → (∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) → (∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀', ∃ r ∈ R, ∃ u ∈ L₀', t = r + k • u) → ∀ N : ℕ, 0 < N → (∀ u ∈ L₀, N • u ∈ L) → (∀ u ∈ L, N • u ∈ L₀) → ∀ x ∈ X, N • x ∈ L₀ → (∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → χ x y = 1) → x ∈ L := by
  intro G _ χ hχ X Y L₀ L₀' L hL₀ hL₀' hL hortho hX hY dX dY tf fin0 fin0' N hN hNL hLN x hx hNx hxY
  by_contra hxL
  set P : AddSubgroup G := X ⊓ L₀.comap (nsmulAddMonoidHom N) with hP
  set Q : AddSubgroup G := Y ⊓ L₀'.comap (nsmulAddMonoidHom N) with hQ
  have memP : ∀ t, t ∈ P ↔ t ∈ X ∧ N • t ∈ L₀ := fun t => Iff.rfl
  have memQ : ∀ t, t ∈ Q ↔ t ∈ Y ∧ N • t ∈ L₀' := fun t => Iff.rfl
  set M := (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf P with hM
  set K := (L₀'.map (nsmulAddMonoidHom N)).addSubgroupOf Q with hK
  have fM : Finite (P ⧸ M) :=
    finite_quot P L₀ N hN (tf N hN) (fun t ht => ((memP t).mp ht).2) fin0
  have fK : Finite (Q ⧸ K) :=
    finite_quot Q L₀' N hN (tf N hN) (fun t ht => ((memQ t).mp ht).2) fin0'
  have memM : ∀ a : P, a ∈ M ↔ ∃ u ∈ L₀, N • u = (a : G) := by
    intro a
    simp only [M, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have memK : ∀ b : Q, b ∈ K ↔ ∃ v ∈ L₀', N • v = (b : G) := by
    intro b
    simp only [K, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, nsmulAddMonoidHom_apply]
  have eM : ∀ a : P, a ∈ M ↔ ∀ b : Q, χ a b = 1 := by
    intro a
    rw [memM]
    constructor
    · rintro ⟨u, hu, hua⟩ b
      rw [← hua, hχ.nsmul]
      exact hortho u hu _ ((memQ b).mp b.2).2
    · intro h
      obtain ⟨x', hx'X, hx'a⟩ := dX N hN a ((memP a).mp a.2).1
      refine ⟨x', hX x' hx'X (fun y hy => ?_), hx'a⟩
      obtain ⟨y', hy'Y, hy'y⟩ := dY N hN y (hL₀' hy)
      have hy'Q : y' ∈ Q := (memQ y').mpr ⟨hy'Y, hy'y ▸ hy⟩
      rw [← hy'y, ← hχ.nsmul, hx'a]
      exact h ⟨y', hy'Q⟩
  have eK : ∀ b : Q, b ∈ K ↔ ∀ a : P, χ a b = 1 := by
    intro b
    rw [memK]
    constructor
    · rintro ⟨v, hv, hvb⟩ a
      rw [← hvb, ← hχ.nsmul]
      exact hortho _ ((memP a).mp a.2).2 v hv
    · intro h
      obtain ⟨y', hy'Y, hy'b⟩ := dY N hN b ((memQ b).mp b.2).1
      refine ⟨y', hY y' hy'Y (fun u hu => ?_), hy'b⟩
      obtain ⟨x', hx'X, hx'u⟩ := dX N hN u (hL₀ hu)
      have hx'P : x' ∈ P := (memP x').mpr ⟨hx'X, hx'u ▸ hu⟩
      rw [← hx'u, hχ.nsmul, hy'b]
      exact h ⟨x', hx'P⟩
  have hMH : M ≤ L.addSubgroupOf P := by
    intro a ha
    obtain ⟨u, hu, hua⟩ := (memM a).mp ha
    rw [AddSubgroup.mem_addSubgroupOf, ← hua]
    exact hNL u hu
  have hxP : x ∈ P := (memP x).mpr ⟨hx, hNx⟩
  have hxH : (⟨x, hxP⟩ : P) ∉ L.addSubgroupOf P := by
    rw [AddSubgroup.mem_addSubgroupOf]
    exact hxL
  obtain ⟨b, hb1, hb2⟩ := exists_separating (fun (a : P) (b : Q) => χ a b)
    (fun a a' b => hχ.left a a' b) (fun a b b' => hχ.right a b b')
    (fun b => hχ.zero_left b) (fun a => hχ.zero_right a) M K eM eK
    (L.addSubgroupOf P) hMH ⟨x, hxP⟩ hxH
  apply hb2
  refine hxY b ((memQ b).mp b.2).1 (fun u hu => ?_)
  have huP : u ∈ P := (memP u).mpr ⟨hL hu, hLN u hu⟩
  exact hb1 ⟨u, huP⟩ ((AddSubgroup.mem_addSubgroupOf).mpr hu)

end GlobalTheory.DualTransfer
