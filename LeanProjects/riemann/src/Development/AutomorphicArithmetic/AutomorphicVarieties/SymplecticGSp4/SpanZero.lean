import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem list_neg {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : ((L.map d).sum).2 < 0) :
    ∃ a ∈ L, (d a).2 < 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : (d b).2 < 0
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem list_pos {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : 0 < ((L.map d).sum).2) :
    ∃ a ∈ L, 0 < (d a).2 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : 0 < (d b).2
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem span_zero {O S K : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (T : Set S) (hT : ∀ y ∈ T, ∃ h : y ∈ B, ξ ⟨y, h⟩ = 0)
    (x : B) (hx : x.1 ∈ Submodule.span O T) : ξ x = 0 := by
  obtain ⟨x, hxB⟩ := x
  have hx' : x ∈ Submodule.span O T := hx
  clear hx
  suffices H : ∃ h : x ∈ B, ξ ⟨x, h⟩ = 0 by
    obtain ⟨_, h⟩ := H
    exact h
  clear hxB
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hT y hy
  | zero => exact ⟨B.zero_mem, map_zero ξ⟩
  | add y z _ _ hy hz =>
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨B.add_mem hy1 hz1, ?_⟩
    have e : (⟨y + z, B.add_mem hy1 hz1⟩ : B) = ⟨y, hy1⟩ + ⟨z, hz1⟩ := rfl
    rw [e, map_add, hy2, hz2, add_zero]
  | smul a y _ hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨B.smul_mem hy1 a, ?_⟩
    have e : (⟨a • y, B.smul_mem hy1 a⟩ : B) = a • ⟨y, hy1⟩ := rfl
    rw [e, map_smul, hy2, smul_zero]

private theorem prod_zero {O S K α : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (e : α → B) (L : List α) (a : α) (ha : a ∈ L) (h0 : ξ (e a) = 0) :
    ∃ h : (L.map fun a => (e a).1).prod ∈ B, ξ ⟨_, h⟩ = 0 := by
  have hp : (((L.map e).prod : B) : S) = (L.map fun a => (e a).1).prod := by
    simpa [List.map_map, Function.comp_def] using map_list_prod B.val (L.map e)
  have hm : (L.map fun a => (e a).1).prod ∈ B := by
    rw [← hp]
    exact ((L.map e).prod).2
  refine ⟨hm, ?_⟩
  have e1 : (⟨_, hm⟩ : B) = (L.map e).prod := Subtype.ext hp.symm
  rw [e1, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  simp only [List.mem_map, Function.comp_apply]
  exact ⟨a, ha, h0⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.signs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, (wt i j).2 < 0 → ¬ Ge (M.rep ξ) i j) → NegZero M.gr (ξ.comp M.toSS)) ∧ ((∀ i j, 0 < (wt i j).2 → ¬ Ge (M.rep ξ) i j) → PosZero M.gr (ξ.comp M.toSS)) ∧ (PosZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 0 2) ∧ (NegZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 2 0) ∧ ∀ ξ' : M.SS →ₐ[c.O] PadicAlgCl l, Same0 M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) → (∀ g i, M.rep ξ g i i = M.rep ξ' g i i) ∧ (DiagType (M.rep ξ) → DiagType (M.rep ξ')) := by
  intro Ω _ _ _ l _ c D hD M _ h0 ξ
  have hv : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j, M.rep ζ g i j = ζ (M.ent g i j) := fun _ _ _ _ => rfl
  have hwt : ∀ i j : Fin 4, (wt i j).1 = 0 → True := fun _ _ _ => trivial
  have zero_of : ∀ n : ℤ, ∀ f ∈ M.gr n,
      (∀ L : List (G ℚ Ω × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = ((0 : ℤ), n) →
        ∃ a ∈ L, ξ (M.ent a.1 a.2.1 a.2.2) = 0) → ξ (M.toSS f) = 0 := by
    intro n f hf hL
    have hx := (kerA D hD M).2.2 n f hf
    rw [spanMono D hD M h0] at hx
    apply span_zero M.SS ξ (mono M.ru.hom ((0 : ℤ), n)) _ (M.toSS f) hx
    rintro y ⟨L, hsum, rfl⟩
    obtain ⟨a, ha, hz⟩ := hL L hsum
    exact prod_zero M.SS ξ (fun a => M.ent a.1 a.2.1 a.2.2) L a ha hz
  have from_part : ∀ n : ℤ, ∀ g i j, wt i j = ((0 : ℤ), n) → ∃ f ∈ M.gr n, M.toSS f = M.ent g i j := by
    intro n g i j he
    apply (kerA D hD M).2.1 n (M.ent g i j)
    have := M.entry_mem g i j
    rw [he] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hneg n hn f hf
    rw [AlgHom.comp_apply]
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_neg (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hneg _ _ hlt ⟨a.1, hne⟩
  · intro hpos n hn f hf
    rw [AlgHom.comp_apply]
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_pos (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hpos _ _ hlt ⟨a.1, hne⟩
  · rintro hpos ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part 1 g 0 2 (by decide)
    apply hg
    have := hpos 1 one_pos f hf
    rw [AlgHom.comp_apply, hfx] at this
    exact this
  · rintro hneg ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part (-1) g 2 0 (by decide)
    apply hg
    have := hneg (-1) (by norm_num) f hf
    rw [AlgHom.comp_apply, hfx] at this
    exact this
  · intro ξ' hs
    have key : ∀ x : M.SS, (x : M.S) ∈ M.sPart ((0 : ℤ), 0) → ξ x = ξ' x := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (kerA D hD M).2.1 0 x hx
      exact hs f hf
    constructor
    · intro g i
      rw [hv, hv]
      apply key
      have := M.entry_mem g i i
      rwa [show wt i i = ((0 : ℤ), 0) by simp [wt]] at this
    · intro hd i j hij ⟨g, hg⟩ ⟨h, hh⟩
      rw [hv] at hg hh
      have hp : ((M.ent g i j * M.ent h j i : M.SS) : M.S) ∈ M.sPart ((0 : ℤ), 0) := by
        rw [spanMono D hD M h0]
        apply Submodule.subset_span
        refine ⟨[(g, i, j), (h, j, i)], ?_, ?_⟩
        · refine Prod.ext ?_ ?_ <;> simp [wt] <;> ring
        · simp [Model.ent]
      have he := key _ hp
      rw [map_mul, map_mul] at he
      apply mul_ne_zero hg hh
      rw [← he]
      by_cases a : ξ (M.ent g i j) = 0
      · rw [a, zero_mul]
      · have hnot := hd i j hij ⟨g, by rw [hv]; exact a⟩
        have hz : ξ (M.ent h j i) = 0 := by
          by_contra hz
          exact hnot ⟨h, by rw [hv]; exact hz⟩
        rw [hz, mul_zero]
