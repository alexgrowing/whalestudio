import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

noncomputable section

namespace Formalism.L2.Pj

open NumberField AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

theorem frBor_of_tri {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x)
    (hu : ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt y.x (y.u τ) cf (y'.u τ i)) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  obtain ⟨u0, hu0⟩ := gen_unit (x := y.x) y.s s' y.gen gen'
  classical
  refine ⟨fun o => match o with
    | none => u0
    | some p => (hu p.1 p.2).choose_spec.1.unit, rfl, fun τ i => ?_, 𝟙 _, ?_, ?_, ?_⟩
  · exact ⟨(hu τ i).choose, (hu τ i).choose_spec.1.unit_spec.symm, (hu τ i).choose_spec.2.1,
      (hu τ i).choose_spec.2.2⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · intro i h
    simp only
    rw [← hu0 i]
    simp only [Scheme.Hom.appLE]
    have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
    rw [e]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

theorem frBor_trans (hT : TanLin Xo) {S : Type} [CommRing S] [Algebra c.F S] {y y' y'' : FrPt Xo c S}
    {t1 t2 : Ix Dw → Sˣ} (h1 : FrBor t1 y y') (h2 : FrBor t2 y' y'') : ∃ t : Ix Dw → Sˣ, FrBor t y y'' := by
  obtain ⟨hx1, hu1, -⟩ := h1
  obtain ⟨hx2, hu2, -⟩ := h2
  refine frBor_of_tri y y'' (hx2.trans hx1) fun τ i => ?_
  choose cf1 h1a h1b h1c using hu1 τ
  obtain ⟨cf2, h2a, h2b, h2c⟩ := hu2 τ i
  let A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S := Matrix.of fun k j => cf1 j k
  have h2c' : IsCombAt y.x (y'.u τ) cf2 (y''.u τ i) := by rw [← hx1]; exact h2c
  have hc := hT S y.x (y.u τ) (y.tan τ) (y'.u τ) A cf2 (y''.u τ i) (fun j => h1c j) h2c'
  refine ⟨A.mulVec cf2, ?_, fun k hk => ?_, hc⟩
  · have e : A.mulVec cf2 i = cf1 i i * cf2 i := by
      simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
      refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · rw [h1b j i hlt, zero_mul]
      · rw [h2b j hgt, mul_zero]
    rw [e, h1a i, h2a]
    exact (Units.isUnit _).mul (Units.isUnit _)
  · simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_or_gt j i with hji | hij
    · rw [h1b j k (lt_of_le_of_lt hji hk), zero_mul]
    · rw [h2b j hij, mul_zero]

end Gen

end Formalism.L2.Pj
