import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

private theorem count_cls {Y T : Type*} (E : T → T → Prop) (hE : ∀ t, E t t) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (t : T) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count {t' | E t t'} = (s.filter fun y => R y t).card := by
  rw [Multiset.count_map, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun y _ => ⟨fun h => ?_, fun h => ⟨?_, t, h⟩⟩
  · have : t ∈ {t' | E t t'} := hE t
    rw [h.1] at this
    exact this
  · exact Set.ext fun t' => (hR y t h t').symm

private theorem count_ncls {Y T : Type*} (E : T → T → Prop) (R : Y → T → Prop)
    (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t') (s : Multiset Y) (S : Set T) (hS : ¬ ∃ t, S = {t' | E t t'}) :
    ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}).count S = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 h
  obtain ⟨t, ht⟩ := (Multiset.mem_filter.1 hy).2
  exact hS ⟨t, Set.ext fun t' => hR y t ht t'⟩

private theorem total {Y T ι : Type*} [Fintype ι] {Y' : ι → Type*} (E : T → T → Prop) (hE : ∀ t, E t t)
    (R : Y → T → Prop) (hR : ∀ y t, R y t → ∀ t', R y t' ↔ E t t')
    (R' : ∀ i, Y' i → T → Prop) (hR' : ∀ i y t, R' i y t → ∀ t', R' i y t' ↔ E t t')
    (s : Multiset Y) (s' : ∀ i, Multiset (Y' i)) (F : ℕ) (f : ι → ℕ)
    (h : ∀ t, F * (s.filter fun y => R y t).card = ∑ i, f i * ((s' i).filter fun y => R' i y t).card) :
    F * (s.filter fun y => ∃ t, R y t).card = ∑ i, f i * ((s' i).filter fun y => ∃ t, R' i y t).card := by
  have key : F • ((s.filter fun y => ∃ t, R y t).map fun y => {t | R y t}) =
      ∑ i, f i • (((s' i).filter fun y => ∃ t, R' i y t).map fun y => {t | R' i y t}) := by
    ext S
    rw [Multiset.count_sum']
    simp only [Multiset.count_nsmul]
    by_cases hS : ∃ t, S = {t' | E t t'}
    · obtain ⟨t, rfl⟩ := hS
      rw [count_cls E hE R hR, h t]
      exact Finset.sum_congr rfl fun i _ => by rw [count_cls E hE (R' i) (hR' i)]
    · rw [count_ncls E R hR s S hS, mul_zero]
      exact (Finset.sum_eq_zero fun i _ => by rw [count_ncls E (R' i) (hR' i) _ S hS, mul_zero]).symm
  have := congrArg Multiset.card key
  simpa [Multiset.card_sum, Multiset.card_nsmul] using this

private theorem card_le_sum {s : Multiset ℕ} (h : ∀ y ∈ s, 0 < y) : s.card ≤ s.sum := by
  simpa using Multiset.card_nsmul_le_sum (a := 1) h

private theorem sum_card_filter {Y : Type*} (s : Multiset Y) (d F : ℕ) (A : Y → ℕ → Prop) (B : Y → Prop)
    (h1 : ∀ y, B y → ((Finset.range d).filter (A y)).card = F) (h2 : ∀ y j, A y j → B y) :
    ∑ j ∈ Finset.range d, (s.filter fun y => A y j).card = F * (s.filter B).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ih, mul_add]
    congr 1
    by_cases hB : B y
    · rw [← h1 y hB, Finset.card_filter, if_pos hB, Multiset.card_singleton, mul_one]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    · rw [if_neg hB]
      exact Finset.sum_eq_zero fun j _ => by rw [if_neg fun hA => hB (h2 y j hA)]; simp

private theorem loc_pow {K : Type} [Field K] [NumberField K] (η : HChar K) (j : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (η ^ j).loc v = η.loc v ^ j := by
  ext1 x
  show (η ^ j).1 _ = η.1 _ ^ j
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem cls_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ζ a b : kˣ →* ℂˣ} (h : IsUnram (ζ * a)) : IsUnram (ζ * b) ↔ IsUnram (a⁻¹ * b) := by
  constructor
  · intro h'
    have := isUnram_mul (isUnram_inv h) h'
    rwa [show (ζ * a)⁻¹ * (ζ * b) = a⁻¹ * b by rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]] at this
  · intro h'
    have := isUnram_mul h h'
    rwa [mul_assoc, mul_inv_cancel_left] at this

private theorem all_of_le {Y : Type*} {s : Multiset Y} {p : Y → Prop} (h : s.card ≤ (s.filter p).card) :
    ∀ y ∈ s, p y :=
  Multiset.filter_eq_self.1 (Multiset.eq_of_le_of_card_le (Multiset.filter_le p s) h)

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam in
theorem UpperTheory.V.Z.Gam.upDownOf :
    UpperTheory.V.Z.Gam.UpDownOf := by
  intro hS hN hM K L _ _ _ _ _ _ _ _ hp n hn π P hBC v
  obtain ⟨η, hη, hloc⟩ := hN K L hp
  have hSK := hS K n (by omega) π v
  have hSL := fun w : PlacesOver L v => hS L n (by omega) P w.1
  obtain ⟨s, hs⟩ := hSK.1
  choose s' hs' using fun w => (hSL w).1
  obtain ⟨w₀⟩ : Nonempty (PlacesOver L v) :=
    ⟨(placesOverEquiv L v).symm (Classical.choice (Ideal.nonempty_primesOver v.asIdeal))⟩
  have hf : ∀ w : PlacesOver L v, 0 < fdeg w := fun w => Ideal.inertiaDeg'_pos _ _
  have hcs : s.card ≤ n := by
    obtain ⟨-, h1, h2⟩ := hSK.2.2.1 s hs
    rw [← h1, ← Multiset.card_map Sigma.fst s]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have hcs' : ∀ w, (s' w).card ≤ n := fun w => by
    obtain ⟨-, h1, h2⟩ := (hSL w).2.2.1 _ (hs' w)
    rw [← h1, ← Multiset.card_map Sigma.fst (s' w)]
    exact card_le_sum fun d hd => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hd; exact h2 y hy
  have key := total (T := {θ : (v.adicCompletion K)ˣ →* ℂˣ // IsSmoothChar θ})
    (fun a b => IsUnram ((a.1⁻¹ * b.1).comp (nm w₀))) (fun a x _ => by simp)
    (fun y t => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram ((ξ * t.1).comp (nm w₀)))
    (by
      rintro y t ⟨ξ, hξ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ξ, hξ, rfl, h'⟩⟩
        (cls_iff (ζ := ξ.comp (nm w₀)) (a := t.1.comp (nm w₀)) (b := t'.1.comp (nm w₀)) h)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    (fun (w : PlacesOver L v) y t => ∃ ζ hζ, y = IrrGL.ofChar ζ hζ ∧ IsUnram (ζ * t.1.comp (nm w)))
    (by
      rintro w y t ⟨ζ, hζ, rfl, h⟩ t'
      refine Iff.trans ⟨?_, fun h' => ⟨ζ, hζ, rfl, h'⟩⟩ ((cls_iff (b := t'.1.comp (nm w)) h).trans
        ⟨(hloc v w).2.1 w₀ (t.1⁻¹ * t'.1), (hloc v w₀).2.1 w (t.1⁻¹ * t'.1)⟩)
      rintro ⟨ξ', hξ', e, h'⟩
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact h')
    s s' (∑ w : PlacesOver L v, fdeg w) (fun w => fdeg w) (fun t => by
      refine Eq.trans ?_ (hM K L hp n hn π P hBC η hη v s s' hs hs' t.1 t.2)
      symm
      refine sum_card_filter s _ _
        (fun y j => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * (t.1 * (η ^ j).loc v))) _ ?_ ?_
      · rintro y ⟨ξ, hξ, rfl, h⟩
        rw [← ((hloc v w₀).2.2 (ξ * t.1) (hξ.mul t.2)).2.2 h]
        congr 1
        refine Finset.filter_congr fun j _ => ⟨?_, fun h' => ⟨ξ, hξ, rfl, by rwa [← mul_assoc]⟩⟩
        rintro ⟨ξ', hξ', e, h'⟩
        obtain rfl := IrrGL.ofChar_inj.1 e
        rwa [mul_assoc]
      · rintro y j ⟨ξ, hξ, rfl, h⟩
        refine ⟨ξ, hξ, rfl, fun x hx => ?_⟩
        have h1 := ((hloc v w₀).2.2 _ (isSmoothChar_of_isUnram h)).2.1 h x hx
        have h2 : η.loc v (nm w₀ x) = 1 := DFunLike.congr_fun (hloc v w₀).1 x
        simpa [loc_pow, h2] using h1)
  constructor
  · intro hT w
    have h1 := (hSK.2.2.1 s hs).1.1 hT
    have hn' : s.card = n := by
      rw [← (hSK.2.2.1 s hs).2.1, Multiset.map_congr rfl h1]; simp
    rw [Multiset.filter_eq_self.2 fun y hy => by
      obtain ⟨ξ, hξ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨ξ⁻¹, hξ.inv⟩, ξ, hξ, rfl, fun x _ => by simp⟩, hn', Finset.sum_mul] at key
    have h2 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left _
      ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hcs' w))).1 key.symm w (Finset.mem_univ w)
    have h3 := all_of_le ((hcs' w).trans (Nat.eq_of_mul_eq_mul_left (hf w) h2).ge)
    refine ⟨((hSL w).2.2.1 _ (hs' w)).1.2 fun y hy => ?_, fun r hr ζ hζ hm => ?_⟩
    · obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
      rfl
    · obtain rfl := (hSL w).2.1 _ _ (hs' w) hr
      obtain ⟨t, ζ', hζ', e, h⟩ := h3 _ hm
      obtain rfl := IrrGL.ofChar_inj.1 e
      exact ⟨t.1, t.2, h⟩
  · intro hT
    have h1 := fun w => ((hSL w).2.2.1 _ (hs' w)).1.1 (hT w).1
    have hn' : ∀ w, (s' w).card = n := fun w => by
      rw [← ((hSL w).2.2.1 _ (hs' w)).2.1, Multiset.map_congr rfl (h1 w)]; simp
    replace key := key.trans (Finset.sum_congr (g := fun w : PlacesOver L v => fdeg w * n) rfl fun w _ => by
      rw [Multiset.filter_eq_self.2 fun y hy => by
        obtain ⟨ζ, hζ, rfl⟩ := GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar y (h1 w y hy)
        obtain ⟨χ, hχ, h⟩ := (hT w).2 _ (hs' w) ζ hζ hy
        exact ⟨⟨χ, hχ⟩, ζ, hζ, rfl, h⟩, hn' w])
    rw [← Finset.sum_mul] at key
    have hF : 0 < ∑ w : PlacesOver L v, fdeg w := Finset.sum_pos (fun w _ => hf w) ⟨w₀, Finset.mem_univ _⟩
    have h3 := all_of_le (hcs.trans (Nat.eq_of_mul_eq_mul_left hF key).ge)
    refine (hSK.2.2.1 s hs).1.2 fun y hy => ?_
    obtain ⟨t, ζ, hζ, rfl, -⟩ := h3 y hy
    rfl
