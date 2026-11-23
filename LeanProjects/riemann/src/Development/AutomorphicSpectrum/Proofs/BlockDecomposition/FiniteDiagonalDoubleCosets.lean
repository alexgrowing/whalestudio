import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitCount

theorem finsum_comp_eq {P D : Type} (g : P → D) (f : D → ℂ) (S : Finset D)
    (hS : ∀ Q, f Q ≠ 0 → Q ∈ S) (hfin : ∀ Q ∈ S, (g ⁻¹' {Q}).Finite) :
    ∑ᶠ p, f (g p) = ∑ Q ∈ S, (Nat.card (g ⁻¹' {Q}) : ℂ) * f Q := by
  have hT : (g ⁻¹' (S : Set D)).Finite := Set.Finite.preimage' S.finite_toSet hfin
  have hsupp : Function.support (fun p => f (g p)) ⊆ (hT.toFinset : Set P) := by
    intro p hp
    simpa using hS _ hp
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hmaps : ∀ p ∈ hT.toFinset, g p ∈ S := by
    intro p hp
    simpa using hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hfil : hT.toFinset.filter (fun p => g p = Q) = (hfin Q hQ).toFinset := by
    ext p
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_coe]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hQ, h⟩
  rw [hfil, Finset.sum_congr rfl (g := fun _ => f Q)]
  · rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset (hfin Q hQ)]
  · intro p hp
    have : g p = Q := by simpa using hp
    rw [this]

theorem abstract_sum {D D₁ P : Type} (π : D → D₁) (Ψ : D₁ → P → D)
    (hπ : ∀ q p, π (Ψ q p) = q) (f : D → ℂ) (hf : (Function.support f).Finite) (c : D₁ → ℂ)
    (hfib : ∀ Q, f Q ≠ 0 → (Ψ (π Q) ⁻¹' {Q}).Finite) :
    ∑ᶠ Q, (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q =
      ∑ᶠ q, c q * ∑ᶠ p, f (Ψ q p) := by
  have hS : ∀ Q, f Q ≠ 0 → Q ∈ hf.toFinset := fun Q h => by simpa using h
  have hempty : ∀ q Q, π Q ≠ q → Ψ q ⁻¹' {Q} = ∅ := by
    intro q Q hne
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hne (h ▸ hπ q p)
  have hinner : ∀ q, c q * ∑ᶠ p, f (Ψ q p) = ∑ Q ∈ hf.toFinset,
      if π Q = q then (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q else 0 := by
    intro q
    rw [finsum_comp_eq (Ψ q) f hf.toFinset hS, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun Q _ => ?_
      by_cases hq : π Q = q
      · subst hq
        rw [if_pos rfl, mul_assoc]
      · rw [if_neg hq, hempty q Q hq]
        simp
    · intro Q hQ
      by_cases hq : π Q = q
      · subst hq
        exact hfib Q (by simpa using hQ)
      · rw [hempty q Q hq]
        exact Set.finite_empty
  have hsupp : Function.support (fun q => c q * ∑ᶠ p, f (Ψ q p)) ⊆
      ((hf.toFinset.image π : Finset D₁) : Set D₁) := by
    intro q hq
    by_contra hnot
    apply hq
    show c q * ∑ᶠ p, f (Ψ q p) = 0
    rw [hinner q]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    rw [if_neg]
    intro h
    exact hnot (by simpa using ⟨Q, by simpa using hQ, h⟩)
  have hsuppL : Function.support
      (fun Q => (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q) ⊆ (hf.toFinset : Set D) := by
    intro Q hQ
    have : f Q ≠ 0 := fun h => hQ (by simp [h])
    simpa using this
  rw [finsum_eq_sum_of_support_subset _ hsupp, finsum_eq_sum_of_support_subset _ hsuppL]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_image_of_mem π hQ)]

variable {H : Type} [Group H]

abbrev cj {G : Type} [Group G] (L : Subgroup G) (x : G) : Subgroup G :=
  L.map (MulAut.conj x).toMonoidHom

theorem mem_cj {G : Type} [Group G] {L : Subgroup G} {x g : G} :
    g ∈ cj L x ↔ x⁻¹ * g * x ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have : x⁻¹ * (MulAut.conj x).toMonoidHom l * x = l := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hl
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

abbrev dg : H →* H × H := (MonoidHom.id H).prod (MonoidHom.id H)

theorem dg_injective : Function.Injective (dg (H := H)) := fun _ _ h => congrArg Prod.fst h

theorem mem_map_dg {Z : Subgroup H} {g : H × H} : g ∈ Z.map dg ↔ g.1 = g.2 ∧ g.1 ∈ Z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨rfl, ht⟩
  · rintro ⟨e, h⟩
    exact ⟨g.1, h, Prod.ext rfl e⟩

theorem inf_diag {Z L : Subgroup H} {Δ M : Subgroup (H × H)}
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (y : H × H) :
    Δ ⊓ M.map (MulAut.conj y).toMonoidHom = ((Z ⊓ cj L y.1) ⊓ cj L y.2).map dg := by
  ext g
  have hc : g ∈ M.map (MulAut.conj y).toMonoidHom ↔
      y.1⁻¹ * g.1 * y.1 ∈ L ∧ y.2⁻¹ * g.2 * y.2 ∈ L := by
    have := mem_cj (L := M) (x := y) (g := g)
    rw [this, hM]
    rfl
  rw [Subgroup.mem_inf, hc, hΔ, mem_map_dg, Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj]
  constructor
  · rintro ⟨⟨e, hz⟩, h1, h2⟩
    exact ⟨e, ⟨hz, h1⟩, e ▸ h2⟩
  · rintro ⟨e, ⟨hz, h1⟩, h2⟩
    exact ⟨⟨e, hz⟩, h1, e ▸ h2⟩

noncomputable def wt (Z L C : Subgroup H) (y : H × H) : ℕ :=
  ((Z ⊓ cj L y.1) ⊓ cj L y.2).relIndex C

theorem relIndex_diag {Z L : Subgroup H} {Δ M : Subgroup (H × H)}
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (C : Subgroup H) (y : H × H) :
    (Δ ⊓ M.map (MulAut.conj y).toMonoidHom).relIndex (C.map dg) = wt Z L C y := by
  rw [inf_diag hΔ hM, Subgroup.relIndex_map_map_of_injective _ _ dg_injective, wt]

theorem cj_mul_right {L : Subgroup H} {l : H} (hl : l ∈ L) (x : H) : cj L (x * l) = cj L x := by
  ext g
  rw [mem_cj, mem_cj]
  have e : (x * l)⁻¹ * g * (x * l) = l⁻¹ * (x⁻¹ * g * x) * l := by group
  rw [e]
  constructor
  · intro h
    have := L.mul_mem (L.mul_mem hl h) (L.inv_mem hl)
    have e2 : l * (l⁻¹ * (x⁻¹ * g * x) * l) * l⁻¹ = x⁻¹ * g * x := by group
    rwa [e2] at this
  · intro h
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) h) hl

theorem cj_mul_left (L : Subgroup H) (t x : H) : cj L (t * x) = cj (cj L x) t := by
  ext g
  rw [mem_cj, mem_cj, mem_cj]
  have e : (t * x)⁻¹ * g * (t * x) = x⁻¹ * (t⁻¹ * g * t) * x := by group
  rw [e]

theorem cj_eq_self {K : Subgroup H} {t : H} (h1 : ∀ c ∈ K, t * c * t⁻¹ ∈ K)
    (h2 : ∀ c ∈ K, t⁻¹ * c * t ∈ K) : cj K t = K := by
  ext g
  rw [mem_cj]
  constructor
  · intro h
    have := h1 _ h
    have e : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
    rwa [e] at this
  · exact h2 g

theorem conj_injective (t : H) : Function.Injective (MulAut.conj t).toMonoidHom :=
  (MulAut.conj t).injective

theorem wt_invariant {Z L C : Subgroup H} (hC : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    {t l l' : H} (ht : t ∈ Z) (hl : l ∈ L) (hl' : l' ∈ L) (x h : H) :
    wt Z L C (t * x * l, t * h * l') = wt Z L C (x, h) := by
  have hZ : cj Z t = Z := cj_eq_self (fun c hc => Z.mul_mem (Z.mul_mem ht hc) (Z.inv_mem ht))
    (fun c hc => Z.mul_mem (Z.mul_mem (Z.inv_mem ht) hc) ht)
  have hCt : cj C t = C := cj_eq_self (hC t ht) (fun c hc => by
    have := hC t⁻¹ (Z.inv_mem ht) c hc
    rwa [inv_inv] at this)
  simp only [wt]
  rw [cj_mul_right hl, cj_mul_right hl', cj_mul_left, cj_mul_left]
  have e : (Z ⊓ cj (cj L x) t) ⊓ cj (cj L h) t = cj ((Z ⊓ cj L x) ⊓ cj L h) t := by
    unfold cj
    rw [Subgroup.map_inf _ _ _ (conj_injective t), Subgroup.map_inf _ _ _ (conj_injective t)]
    exact congrArg (· ⊓ _) (congrArg (· ⊓ _) hZ.symm)
  rw [e]
  conv_lhs => rw [← hCt]
  exact Subgroup.relIndex_map_map_of_injective _ _ (conj_injective t)

section Classes

variable {Z L : Subgroup H} {Δ M : Subgroup (H × H)}

theorem mk_eq_iff (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (y y' : H × H) :
    DoubleCoset.mk Δ M y = DoubleCoset.mk Δ M y' ↔
      ∃ t ∈ Z, ∃ l ∈ L, ∃ l' ∈ L, y'.1 = t * y.1 * l ∧ y'.2 = t * y.2 * l' := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨d, hd, m, hm, e⟩
    obtain ⟨e1, hz⟩ := (hΔ d).1 hd
    obtain ⟨m1, m2⟩ := (hM m).1 hm
    refine ⟨d.1, hz, m.1, m1, m.2, m2, ?_, ?_⟩
    · rw [e]
      rfl
    · rw [e, e1]
      rfl
  · rintro ⟨t, ht, l, hl, l', hl', e1, e2⟩
    exact ⟨(t, t), (hΔ _).2 ⟨rfl, ht⟩, (l, l'), (hM _).2 ⟨hl, hl'⟩, Prod.ext e1 e2⟩

theorem out_invariant {α : Type} (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (G : H × H → α)
    (hG : ∀ t ∈ Z, ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, G (t * x * l, t * h * l') = G (x, h)) (y : H × H) :
    G (Quotient.out (DoubleCoset.mk Δ M y)) = G y := by
  obtain ⟨t, ht, l, hl, l', hl', e1, e2⟩ :=
    (mk_eq_iff hΔ hM y (Quotient.out (DoubleCoset.mk Δ M y))).1
      (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y)).symm
  have e : Quotient.out (DoubleCoset.mk Δ M y) = (t * y.1 * l, t * y.2 * l') := Prod.ext e1 e2
  rw [e]
  exact hG t ht l hl l' hl' y.1 y.2

variable (Z L Δ M) in

noncomputable def proj (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    DoubleCoset.Quotient (Z : Set H) (L : Set H) :=
  DoubleCoset.mk Z L (Quotient.out Q).1

variable (Z L Δ M) in

noncomputable def lift (q : DoubleCoset.Quotient (Z : Set H) (L : Set H)) (p : H ⧸ L) :
    DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)) :=
  DoubleCoset.mk Δ M (Quotient.out q, p.out)

theorem proj_mk (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (y : H × H) : proj Z L Δ M (DoubleCoset.mk Δ M y) = DoubleCoset.mk Z L y.1 := by
  obtain ⟨t, ht, l, hl, l', hl', e1, -⟩ :=
    (mk_eq_iff hΔ hM (Quotient.out (DoubleCoset.mk Δ M y)) y).1
      (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y))
  rw [proj, DoubleCoset.eq]
  exact ⟨t, ht, l, hl, e1⟩

theorem proj_lift (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (q : DoubleCoset.Quotient (Z : Set H) (L : Set H)) (p : H ⧸ L) :
    proj Z L Δ M (lift Z L Δ M q p) = q := by
  rw [lift, proj_mk hΔ hM]
  exact DoubleCoset.out_eq' Z L q

theorem exists_rep (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    ∃ h : H, DoubleCoset.mk Δ M (Quotient.out (proj Z L Δ M Q), h) = Q := by
  obtain ⟨t, ht, l, hl, e⟩ := (DoubleCoset.eq Z L (Quotient.out (proj Z L Δ M Q))
    (Quotient.out Q).1).1 (DoubleCoset.out_eq' Z L (proj Z L Δ M Q))
  refine ⟨t⁻¹ * (Quotient.out Q).2, Eq.trans ?_ (DoubleCoset.out_eq' Δ M Q)⟩
  rw [mk_eq_iff hΔ hM]
  exact ⟨t, ht, l, hl, 1, L.one_mem, e, by simp⟩

theorem fiber_eq_orbit (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (x h : H) :
    {p : H ⧸ L | DoubleCoset.mk Δ M (x, p.out) = DoubleCoset.mk Δ M (x, h)} =
      MulAction.orbit (Z ⊓ cj L x : Subgroup H) (QuotientGroup.mk h : H ⧸ L) := by
  ext p
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  rw [mk_eq_iff hΔ hM]
  constructor
  · rintro ⟨t, ht, l, hl, l', hl', e1, e2⟩
    have e1' : x = t * x * l := e1
    have e2' : h = t * p.out * l' := e2
    have hb : t⁻¹ ∈ cj L x := by
      rw [mem_cj]
      have : x⁻¹ * t⁻¹ * x = l := by
        have : t⁻¹ * x = x * l := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
          exact e1'
        rw [mul_assoc, this]
        group
      rw [this]
      exact hl
    refine ⟨⟨t⁻¹, Subgroup.mem_inf.2 ⟨Z.inv_mem ht, hb⟩⟩, ?_⟩
    change (QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = p
    have hq : (QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = QuotientGroup.mk p.out := by
      rw [QuotientGroup.eq]
      have : (t⁻¹ * h)⁻¹ * p.out = l'⁻¹ := by
        rw [e2']
        group
      rw [this]
      exact L.inv_mem hl'
    rw [hq, QuotientGroup.out_eq']
  · rintro ⟨⟨b, hb⟩, e⟩
    obtain ⟨hbZ, hbL⟩ := Subgroup.mem_inf.1 hb
    have e' : (QuotientGroup.mk (b * h) : H ⧸ L) = p := e
    have hq : (QuotientGroup.mk (b * h) : H ⧸ L) = QuotientGroup.mk p.out := by
      rw [e', QuotientGroup.out_eq']
    rw [QuotientGroup.eq] at hq
    rw [mem_cj] at hbL
    have hl2 : p.out⁻¹ * (b * h) ∈ L := by
      have := L.inv_mem hq
      have e3 : ((b * h)⁻¹ * p.out)⁻¹ = p.out⁻¹ * (b * h) := by group
      rwa [e3] at this
    refine ⟨b⁻¹, Z.inv_mem hbZ, x⁻¹ * b * x, hbL, p.out⁻¹ * (b * h), hl2, ?_, ?_⟩
    · show x = b⁻¹ * x * (x⁻¹ * b * x)
      group
    · show h = b⁻¹ * p.out * (p.out⁻¹ * (b * h))
      group

theorem ncard_orbit (L B : Subgroup H) (h : H) :
    (MulAction.orbit B (QuotientGroup.mk h : H ⧸ L)).ncard = (B ⊓ cj L h).relIndex B := by
  rw [← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext b
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cj]
  change (QuotientGroup.mk ((b : H) * h) : H ⧸ L) = QuotientGroup.mk h ↔ _
  rw [eq_comm, QuotientGroup.eq]
  have e : h⁻¹ * ((b : H) * h) = h⁻¹ * b * h := by group
  rw [e]
  exact ⟨fun hh => ⟨b.2, hh⟩, fun hh => hh.2⟩

theorem weight_fiber {C : Subgroup H} (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (h1 : ∀ x : H, Z ⊓ cj L x ≤ C ∧ (Z ⊓ cj L x).relIndex C ≠ 0)
    (h2 : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    (lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q}).Finite ∧
      wt Z L C (Quotient.out Q) = (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))).relIndex C *
        Nat.card (lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q}) := by
  obtain ⟨h, hh⟩ := exists_rep (Z := Z) (L := L) hΔ hM Q
  have hw := out_invariant hΔ hM (wt Z L C)
    (fun t ht l hl l' hl' x h => wt_invariant h2 ht hl hl' x h) (Quotient.out (proj Z L Δ M Q), h)
  rw [hh] at hw
  have hset : lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q} =
      MulAction.orbit (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q)) : Subgroup H)
        (QuotientGroup.mk h : H ⧸ L) := by
    rw [← fiber_eq_orbit hΔ hM, hh]
    rfl
  have hmul := Subgroup.relIndex_mul_relIndex
    ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h)
    (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) C inf_le_left
    (h1 (Quotient.out (proj Z L Δ M Q))).1
  have hA : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex C ≠ 0 := by
    have := Subgroup.relIndex_inf_ne_zero (h1 (Quotient.out (proj Z L Δ M Q))).2 (h1 h).2
    have e : (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ (Z ⊓ cj L h) =
        (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
        (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    rwa [e] at this
  have hB : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex
      (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hA hmul.symm
  have hcard := ncard_orbit L (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) h
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact Set.finite_of_ncard_ne_zero (hcard ▸ hB)
  · rw [hset, Nat.card_coe_set_eq, hcard, hw]
    show ((Z ⊓ cj L _) ⊓ cj L h).relIndex C = _
    rw [← hmul, mul_comm]

end Classes

theorem orbit_count_gen (Z L C : Subgroup H) (Δ M : Subgroup (H × H))
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (F : H × H → ℂ)
    (h1 : ∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧
      (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0)
    (h2 : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (h3 : ∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h))
    (h4 : ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h))
    (hfin : {Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)) |
      F (Quotient.out Q) ≠ 0}.Finite) :
    ∑ᶠ Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)),
        (((Δ ⊓ M.map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex
          (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
      ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
        (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) *
          ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  have hF : ∀ t ∈ Z, ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (t * x * l, t * h * l') = F (x, h) := by
    intro t ht l hl l' hl' x h
    rw [h4 l hl l' hl', h3 t ht]
  have hw := weight_fiber (C := C) hΔ hM h1 h2
  have key := abstract_sum (proj Z L Δ M) (lift Z L Δ M) (proj_lift hΔ hM)
    (fun Q => F (Quotient.out Q)) hfin
    (fun q => (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ))
    (fun Q _ => (hw Q).1)
  have hR : ∀ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (∑ᶠ p : H ⧸ L, F (Quotient.out (lift Z L Δ M q p))) =
        ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := fun q =>
    finsum_congr fun p => out_invariant hΔ hM F hF _
  simp only [hR] at key
  rw [← key]
  refine finsum_congr fun Q => ?_
  have e := relIndex_diag hΔ hM C (Quotient.out Q)
  rw [e, (hw Q).2]
  push_cast
  rfl

theorem orbit_count : ∀ (H : Type) [Group H] (Z L C : Subgroup H) (F : H × H → ℂ),
  (∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧ (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) →
  (∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C) →
  (∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h)) →
  (∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h)) →
  {Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)) | F (Quotient.out Q) ≠ 0}.Finite →
  ∑ᶠ Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)),
      (((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) ⊓ (L.prod L).map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
    ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  intro H _ Z L C F h1 h2 h3 h4 hfin
  exact orbit_count_gen Z L C _ _
    (fun g => mem_map_dg) (fun g => Subgroup.mem_prod) F h1 h2 h3 h4 hfin

end GlobalTheory.CompanionTheory.OrbitCount
