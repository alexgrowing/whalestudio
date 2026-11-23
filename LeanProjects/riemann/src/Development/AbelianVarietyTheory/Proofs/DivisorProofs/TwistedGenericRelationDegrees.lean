import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry

open GlobalTheory.ShFam GlobalTheory.GradedNorm GlobalTheory.ProjVar.Var

theorem grSq_submatrix_cast {m m' : ℕ} (h : m = m') (M : Matrix (Fin m') (Fin m') ℂ) (i : Fin m) :
    grSq (M.submatrix (Fin.cast h) (Fin.cast h)) i = grSq M (Fin.cast h i) := by
  subst h
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem prod_grSq_push (T : Tw Z) {σ : c.F →+* ℂ} (G G' : EigMet Z σ) (n n' : Letter Dw → ℤ)
    (hn : ∀ z, n' (T.letter z) = n z) (y q : CxPts (genStr Z) σ) (hq : q = T.pt y) (hM : T.MetAt y G G')
    (g : EigFrame Z σ (y.1 ≫ genι Z)) (g' : EigFrame Z σ (q.1 ≫ genι Z)) (hp : T.Push g g') :
    ∏ z : Letter Dw, grSq (G.gram q g' z.1) z.2 ^ n z = ∏ z : Letter Dw, grSq (G'.gram y g z.1) z.2 ^ n' z := by
  subst hq
  simp only [hM g g' hp, grSq_submatrix_cast]
  exact Fintype.prod_equiv T.letter _ _ fun z => by rw [hn]; rfl

theorem prodPow_relab (T : Tw Z) {A B : Type} [CommGroup A] [CommGroup B] (h : A →* B)
    (t t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → B) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → A) (n n' : Letter Dw → ℤ)
    (ht : ∀ τ i, t (T.emb τ) (T.ix i) = h (t' τ i) * t₀ τ i) (hn : ∀ z, n' (T.letter z) = n z) :
    prodPow t n' = h (prodPow t' n) * prodPow t₀ n := by
  calc prodPow t n' = ∏ z : Letter Dw, t (T.letter z).1 (T.letter z).2 ^ n' (T.letter z) :=
        (Fintype.prod_equiv T.letter _ _ fun _ => rfl).symm
    _ = ∏ z : Letter Dw, (h (t' z.1 z.2) * t₀ z.1 z.2) ^ n z :=
        Finset.prod_congr rfl fun z _ => by rw [hn]; exact congrArg (· ^ n z) (ht z.1 z.2)
    _ = _ := by simp only [mul_zpow, Finset.prod_mul_distrib, prodPow, map_prod, map_zpow]

end GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry

open GlobalTheory.ShFam GlobalTheory.GradedNorm GlobalTheory.ProjVar.Var

theorem pn_met_carry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) (n n' : Letter Dw → ℤ) (σ : F →+* ℂ) (G G' : EigMet Z (embOf e σ)), T.LocRel C C' φ ψ t₀ → (∀ z, n' (T.letter z) = n z) → (∀ y, T.MetAt y G G') → ∀ (p : GlobalTheory.TrueGeo.Pts C.Y σ) (p' : GlobalTheory.TrueGeo.Pts C'.Y σ), p'.1 = p.1 ≫ φ.hom → ∀ g : C'.Y.Fnˣ, (divOf C' n).IsEqn (under p') g → (GlobalTheory.TrueGeo.cxSt F).pn C.Y σ (divOf C n') (C.met G' n') ((GlobalTheory.TrueGeo.cxSt F).cx C.Y σ ((Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n)⁻¹ : C.Y.Fnˣ)) p = (GlobalTheory.TrueGeo.cxSt F).pn C'.Y σ (divOf C' n) (C'.met G n) ((GlobalTheory.TrueGeo.cxSt F).cx C'.Y σ (g⁻¹ : C'.Y.Fnˣ)) p' := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ _ e C C' φ ψ t₀ n n' σ G G' hL hn hM p p' hp g hg
  obtain ⟨q, -, χ', f', h1, h2⟩ := C'.exists_adapted p'
  obtain ⟨g', hg'⟩ := f'.exists_isMap (evStalk p') h2.2.1 h2.1
  have hA' : C'.Adapted p' q.1 g' 1 := ⟨χ', f', h1, hg'.tri h2.2.1 h2.1⟩
  have hbase : base p' = φ.hom (base p) := by
    show p'.1 _ = _
    rw [hp]
    rfl
  obtain ⟨a, χ, f, t, ha1, ha2, ha3, ha4, ha5, ha6⟩ := hL.2.2 (base p) (base p') χ' f' q.1 hbase h1
  have hev : (evStalk p).comp a = evStalk p' := EigLoc.spMap_inj ((cancel_mono (C'.Y.X.fromSpecStalk (base p'))).1 (by
    show Spec.map (CommRingCat.ofHom a ≫ CommRingCat.ofHom (evStalk p)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    refine (congrArg (_ ≫ ·) ha1.symm).trans ?_
    rw [← Category.assoc]
    refine (congrArg (· ≫ φ.hom) (C.spMap_evStalk p)).trans ?_
    exact hp.symm.trans (C'.spMap_evStalk p').symm))
  have hφ : embOf e σ = (evStalk p).comp χ := by
    rw [ha2, ← RingHom.comp_assoc, hev]
    exact h2.2.1
  have hx : (C.down p).1 ≫ genι Z = spMap (evStalk p) ≫ stalkPt C.Y (base p) ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, C.spMap_evStalk]
    exact Category.assoc _ _ _
  obtain ⟨k, hk⟩ := f.exists_isMap (evStalk p) hφ hx
  have hA : C.Adapted p t k 1 := ⟨χ, f, ha4, hk.tri hφ hx⟩
  have hpt : C'.down p' = T.pt (C.down p) := Subtype.ext (by
    show p'.1 ≫ C'.π = (p.1 ≫ C.π) ≫ T.g.hom
    rw [hp, Category.assoc, hL.1, Category.assoc])
  have hpush : T.Push k g' := ⟨rfl, by rw [hpt]; exact T.pt_ι _, fun τ i => by
    rw [hg' τ i, hk (T.emb τ) (T.ix i), ← hev, ← GlobalTheory.GradedPieces.dual_comp, ha6, Category.assoc]⟩
  have hgen : C'.genSq G n g' = C.genSq G' n' k :=
    prod_grSq_push T G G' n n' hn (C.down p) (C'.down p') hpt (hM _) k g' hpush
  have he' : p' ∈ eqnSet σ (divOf C' n) (prodPow q.1 n) := FlagCpt.prodPow_mem n hA'.mem_eqnSet
  have he : p ∈ eqnSet σ (divOf C n') (prodPow t n') := FlagCpt.prodPow_mem n' hA.mem_eqnSet
  have hg0 : p' ∈ eqnSet σ (divOf C' n) g := hg
  obtain ⟨z, hz, hzv⟩ := (CartierDiv.IsEqn.iff_unitAt hg0).1 he'
  have key : prodPow t n' = Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (prodPow q.1 n) * prodPow t₀ n :=
    prodPow_relab T _ t t₀ q.1 n n' ha5 hn
  have hratio : ((prodPow t n' : C.Y.Fnˣ) : C.Y.Fn) / ((Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n : C.Y.Fnˣ) : C.Y.Fn) =
      algebraMap _ C.Y.X.functionField (a z) := by
    rw [key, Units.val_mul, Units.val_mul, mul_div_mul_right _ _ (Units.ne_zero _)]
    show ψ _ / ψ _ = _
    rw [← map_div₀, ← hzv, ha3]
  have hu : p ∈ eqnSet σ (divOf C n') (Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n) := by
    refine (CartierDiv.IsEqn.iff_unitAt he).2 ⟨((hz.map a).unit⁻¹ : _ˣ), Units.isUnit _, ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ← hratio, inv_div]
  have L : (GlobalTheory.TrueGeo.cxSt F).pn C.Y σ (divOf C n') (C.met G' n') ((GlobalTheory.TrueGeo.cxSt F).cx C.Y σ
      ((Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n)⁻¹ : C.Y.Fnˣ)) p =
      (C.met G' n').h (Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n) p := pn_frame hu
  have R : (GlobalTheory.TrueGeo.cxSt F).pn C'.Y σ (divOf C' n) (C'.met G n) ((GlobalTheory.TrueGeo.cxSt F).cx C'.Y σ (g⁻¹ : C'.Y.Fnˣ)) p' =
      (C'.met G n).h g p' := pn_frame hg0
  rw [L, R, (C.met G' n').trans _ _ p hu he,
    (C'.met G n).trans _ _ p' hg0 he', FlagCpt.met_h G' n' hA, FlagCpt.met_h G n hA', hgen]
  have v1 : Var.tv (Units.map (ψ : C'.Y.Fn →* C.Y.Fn) g * prodPow t₀ n) (prodPow t n') p = evStalk p' z := by
    rw [Var.tv, hratio, (hasVal_cx_stalk _).val_eq, ← hev]
    rfl
  have v2 : Var.tv g (prodPow q.1 n) p' = evStalk p' z := by
    rw [Var.tv, ← hzv, (hasVal_cx_stalk _).val_eq]
  rw [v1, v2]
  simp [prodPow]

end GlobalTheory.ShFam.GalCarry
