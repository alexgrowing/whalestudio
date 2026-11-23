import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafIrredPf

lemma mem_range {C0 D0 S T : Scheme.{0}} {v0 : C0 ⟶ D0} {c0 : C0 ⟶ T} {q : D0 ⟶ S} {t : T ⟶ S}
    (h : IsPullback v0 c0 q t) (x : D0) (y : T) (hxy : q x = t y) : x ∈ Set.range v0 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t) x y hxy
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← hz, ← h.isoPullback_inv_fst]
  rfl

lemma spec_gen {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (y : Sp Ω) (p : Sp R) :
    toR R y ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) ((toR R) y) p).mp
  intro a ha
  have hA : (toR R).base y = PrimeSpectrum.comap (algebraMap R Ω) y := by
    rw [Spec.map_base]; rfl
  change a ∈ ((toR R).base y).asIdeal at ha
  rw [hA] at ha
  let y' : PrimeSpectrum Ω := y
  have ha' : algebraMap R Ω a ∈ y'.asIdeal := ha
  rw [Ideal.eq_bot_of_prime y'.asIdeal, Ideal.mem_bot] at ha'
  have ha := ha'
  have : a = 0 := Subtype.ext (by simpa using ha)
  rw [this]; exact p.asIdeal.zero_mem

theorem LeafIrred_of : LeafIrred := by
  intro k _ Ω _ _ R _ C0 D0 c0 q v0 hc hq h
  obtain ⟨hint, -, -⟩ := hc
  have := hint
  have := hq
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : IrreducibleSpace C0 := irreducibleSpace_of_isIntegral C0
  have hirr : IsIrreducible (Set.range v0) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C0).image v0 v0.continuous.continuousOn
  have hdense : Dense (Set.range v0) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨c⟩ := (inferInstance : Nonempty C0)
    have hopen : IsOpen (q '' U) := q.isOpenMap U hU
    have hmem : toR R (c0 c) ∈ q '' U := (spec_gen R (c0 c) (q x)).mem_open hopen ⟨x, hx, rfl⟩
    obtain ⟨x', hx'U, hx'⟩ := hmem
    exact ⟨x', hx'U, mem_range h x' (c0 c) hx'⟩
  have : IsIrreducible (Set.univ : Set D0) := by
    rw [← hdense.closure_eq]; exact hirr.closure
  exact { isPreirreducible_univ := this.2, toNonempty := ⟨this.1.some⟩ }

end LateralTheory.E.LeafIrredPf
