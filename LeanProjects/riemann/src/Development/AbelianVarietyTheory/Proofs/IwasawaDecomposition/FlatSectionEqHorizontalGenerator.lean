import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeightStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationFlagPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConstStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelabelMatrixStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodUnfoldedFamilyPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagTorusAlgebraicallyClosedStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmE

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ShFam.Horiz

open GlobalTheory.CxPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isCoord_frameCast {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} {Y : FlagCpt Z e} {k : Type}
    [Field k] {φ : c.F →+* k} {x x' : Sp k ⟶ Z.X} (h : x = x') {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
    {n : Letter Dw → ℤ} {s : Y.Y.Fn} {v : k} (hc : IsCoord Y p g n s v) : IsCoord Y p (frameCast h g) n s v := by
  subst h
  exact hc

theorem rigid {Z : Model Xo c β} {σ : c.F →+* ℂ} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {h : CxFr Z σ → ℂ} (hh : HorFn τ h) {s : C.Y.Fn}
    (hs : ∀ y, (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))).GeneratesAt y s) :
    ∃ b : ℂ, ∀ (a : CxFr Z σ) (p : CxPts C.Y.str (σ.comp e.toRingHom)) (v : ℂ), Inner a.1 → a.1.1 = p.1 ≫ C.π →
      IsCoord C p.1 a.2 (expo Dw (detSym Dw (fun _ => false) none τ)) s v → h a = b * v := by
  obtain ⟨W, δ, a, hW, hδ, ha, hf, hc, hco⟩ := GlobalTheory.T.exists_local_equation_flag_points E H Dw l Xo c O β Z σ F e C τ hτ
  obtain ⟨hne, hd⟩ := GlobalTheory.T.complexPoints_nonempty_dense_variety F C.Y (σ.comp e.toRingHom)
  have hA := hd (C.π ⁻¹ᵁ (genBd Z).compl) ⟨genericPt C.Y (IsLocalRing.closedPoint C.Y.Fn), fun hb =>
    hb ⟨_, congrArg (fun g => g (IsLocalRing.closedPoint C.Y.Fn)) C.y0_x⟩⟩
  let R := AnRead.all C.Y.str (σ.comp e.toRingHom) C.Y.dim
  set A := ptsIn C.Y.str (σ.comp e.toRingHom) (C.π ⁻¹ᵁ (genBd Z).compl) with hAdef
  choose u hu he using fun y => GlobalTheory.ShFam.Hor.Sec.exists_extension R C.π hA (isOpen_ptsIn (W y)) (ha y) (hf y) hh.2.2.1 hh.2.2.2
  choose r hr using fun y => exists_unit_fnOf_eq (U := W y) (f := s * (δ y : C.Y.Fn))
    fun x hx => (hδ y x hx).generatesAt_iff.1 (hs x)
  have evu : ∀ y (z : CxPts C.Y.str (σ.comp e.toRingHom)), z ∈ ptsIn C.Y.str (σ.comp e.toRingHom) (W y) →
      ev C.Y.str (σ.comp e.toRingHom) _ (r y).val z * ev C.Y.str (σ.comp e.toRingHom) _ ((r y)⁻¹).val z = 1 := fun y z hz => by
    rw [← ev_mul, Units.mul_inv]
    exact ev_one hz
  have tr : ∀ y y' (z : CxPts C.Y.str (σ.comp e.toRingHom)), z ∈ ptsIn C.Y.str (σ.comp e.toRingHom) (W y) →
      z ∈ ptsIn C.Y.str (σ.comp e.toRingHom) (W y') → z ∈ A →
      h (a y z) * ev C.Y.str (σ.comp e.toRingHom) _ ((r y)⁻¹).val z =
        h (a y' z) * ev C.Y.str (σ.comp e.toRingHom) _ ((r y')⁻¹).val z := fun y y' z hy hy' hz => by
    obtain ⟨t, ht⟩ := exists_unit_fnOf_eq (U := W y ⊓ W y') (f := (δ y : C.Y.Fn) / (δ y' : C.Y.Fn))
      fun x hx => (hδ y' x hx.2).iff_unitAt.1 (hδ y x hx.1)
    have hyy := mem_ptsIn_inf.2 ⟨hy, hy'⟩
    obtain ⟨M, N, hM, hN, hM0, hMN⟩ := hc y y' (W y ⊓ W y') (gen_mem (mem_ptsIn.1 hyy)) t.val (ht _) z
      (mem_ptsIn_inf.2 ⟨hyy, hyy⟩)
    have hin := (GlobalTheory.ShFam.Hor.Sec.inner_iff (ha y' z hy')).2 hz
    have e4 := hh.2.1 _ _ M N hin hM hN
    have e5 : h (a y z) = h (a y' z) * ev C.Y.str (σ.comp e.toRingHom) _ t.val z := by
      refine mul_right_cancel₀ hM0 ?_
      rw [e4, ← hMN]
      ring
    have e3 := GlobalTheory.ShFam.Hor.Sec.ev_mul_eq (a := (r y').val) (b := t.val) (c := (r y).val) hy' hyy hy (fun _ _ _ => by
      rw [hr, hr, ht]
      have := (δ y').ne_zero
      field_simp)
    have e1 := evu y z hy
    have e2 := evu y' z hy'
    rw [e5]
    generalize ev C.Y.str (σ.comp e.toRingHom) _ t.val z = T at *
    generalize ev C.Y.str (σ.comp e.toRingHom) _ ((r y)⁻¹).val z = I at *
    generalize ev C.Y.str (σ.comp e.toRingHom) _ ((r y')⁻¹).val z = I' at *
    generalize ev C.Y.str (σ.comp e.toRingHom) _ (r y).val z = A₀ at *
    generalize ev C.Y.str (σ.comp e.toRingHom) _ (r y').val z = A₁ at *
    generalize h (a y' z) = h' at *
    linear_combination h' * ((-(T * I)) * e2 + (I' * I) * e3 + I' * e1)
  let pt (z : CxPts C.Y.str (σ.comp e.toRingHom)) : C.Y.X := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : CxPts C.Y.str (σ.comp e.toRingHom)) : z ∈ ptsIn C.Y.str (σ.comp e.toRingHom) (W (pt z)) := mem_ptsIn.2 (hW _)
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.ShFam.Hor.Sec.exists_holoOn_of_local (R := R) hA (S := Set.univ)
    (u := fun z => h (a (pt z) z) * ev C.Y.str (σ.comp e.toRingHom) _ ((r (pt z))⁻¹).val z) fun z _ =>
    ⟨ptsIn C.Y.str (σ.comp e.toRingHom) (W (pt z)), fun w => u (pt z) w * ev C.Y.str (σ.comp e.toRingHom) _ ((r (pt z))⁻¹).val w,
      isOpen_ptsIn _, hpt z, (hu _).mul (R.holoOn_ev _ _), fun w hw => by
        show u (pt z) w * _ = h (a (pt w) w) * _
        rw [he (pt z) hw]
        exact tr _ _ w hw.1 (hpt w) hw.2⟩
  obtain ⟨b, hb⟩ := GlobalTheory.T.holomorphic_on_projective_const F C.Y (σ.comp e.toRingHom) R q hq
  refine ⟨b, ?_⟩
  rintro ⟨x₀, g⟩ p v hin hx hcoord
  have hp := hpt p
  have hpA : p ∈ A := (GlobalTheory.ShFam.Hor.Sec.inner_iff hx).1 hin
  have e0 : (a (pt p) p).1 = x₀ := Subtype.ext ((ha _ p hp).trans hx.symm)
  subst e0
  obtain ⟨M, N, hM, hN, hM0, hMv⟩ := hco (pt p) (W (pt p)) (gen_mem (mem_ptsIn.1 hp)) (r (pt p)).val s (hr _ _) p
    (mem_ptsIn_inf.2 ⟨hp, hp⟩) g v hcoord
  have e4 := hh.2.1 (a (pt p) p) ⟨_, g⟩ M N hin hM hN
  have e6 : h (a (pt p) p) * ev C.Y.str (σ.comp e.toRingHom) _ ((r (pt p))⁻¹).val p = b :=
    (hqe ⟨trivial, hpA⟩).symm.trans (hb p)
  have e1 := evu _ p hp
  refine mul_right_cancel₀ hM0 ?_
  rw [e4]
  generalize ev C.Y.str (σ.comp e.toRingHom) _ ((r (pt p))⁻¹).val p = I at *
  generalize ev C.Y.str (σ.comp e.toRingHom) _ (r (pt p)).val p = A₀ at *
  generalize h (a (pt p) p) = h' at *
  linear_combination (N.det * A₀) * e6 - (h' * N.det) * e1 - b * hMv

end GlobalTheory.ShFam.Horiz

namespace GlobalTheory.ShFam.Horiz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem neg_exOf_flatWt (τ : GlobalTheory.AllWt.Psi H) (z : Letter Dw) :
    -GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.flatWt Dw τ) 0 (some z) = expo Dw (detSym Dw (fun _ => false) none τ.1) z := by
  rw [GlobalTheory.ShFam.HolFrames.expo_detSym Dw _ _ τ.2]
  obtain ⟨ρ, i⟩ := z
  show -(GlobalTheory.AllWt.wtOf Dw (GlobalTheory.FlatLine.flatWt Dw τ) 0).1 (ρ, (i : ℕ)) = _
  by_cases h : ρ (H.rt : E) = H.rt0
  · have hm : Dw.mult ρ = Dw.p := if_pos h
    have h1 : ρ ≠ conjEmb τ.1 := fun e => GlobalTheory.AllWt.conj_not_mem τ (e ▸ h)
    rw [GlobalTheory.AllWt.wtOf_big (GlobalTheory.FlatLine.flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)]
    by_cases e : ρ = τ.1
    · simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, Subtype.ext_iff, e, Ne.symm (e ▸ h1)]
    · simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, Subtype.ext_iff, e, h1, Ne.symm e, Ne.symm h1]
  · have hm : Dw.mult ρ = Dw.q := if_neg h
    have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
    have := GlobalTheory.AllWt.wtOf_small (GlobalTheory.FlatLine.flatWt Dw τ) 0 ⟨_, GlobalTheory.AllWt.conj_mem h⟩ i (hm ▸ i.2)
    simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at this
    rw [this]
    by_cases e : ρ = conjEmb τ.1
    · have h2 : conjEmb ρ = τ.1 := by rw [e, GlobalTheory.AllWt.conjEmb_conjEmb]
      have h3 : (⟨conjEmb ρ, GlobalTheory.AllWt.conj_mem h⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext h2
      simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, h3, Ne.symm h1, e.symm]
    · have h2 : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', GlobalTheory.AllWt.conjEmb_conjEmb])
      simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, Subtype.ext_iff, Ne.symm h1, Ne.symm e, h2]

end GlobalTheory.ShFam.Horiz

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad in

theorem GlobalTheory.ShFam.Horiz.rdU_eq_horizGen : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (τ : GlobalTheory.AllWt.Psi A.H) (hτ : τ.1 ∈ ((s.U κ.σ₀).X k).Ψ), ∀ f ∈ GlobalTheory.AllWt.secZ s.Xo κ.c (GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw τ) 0), IsFlat (Φ.C k) τ.1 ((Φ.C k).val f) → ∃ b : ℂˣ, ∀ x ∈ ((s.U κ.σ₀).X k).dom, Formalism.L2.PjFree.rdU (s.U κ.σ₀) f k x = b * GlobalTheory.FlatLine.horizGen ⟨τ.1, hτ⟩ x := by
  intro D A N j S κ s Φ k τ hτ f hf hflat
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  obtain ⟨hU, -, -, -⟩ := s.unf κ.σ₀ hσ
  obtain ⟨g, e, Fu, ik, φ, hEF, hun⟩ := hU.2.2.2.2.2
  choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ A.H S.Dw (Fu.Di i) τ.1 (Fu.sig i)
  have hr : 1 ≤ S.Dw.p + S.Dw.q := by have := S.two_le; have := S.rank_eq; omega
  have hh := GlobalTheory.ShFam.Hor.horFn_horOf (Fu := Fu) (τ := τ.1) (x := x) (hm := hm) s.T hσ hr κ.good hx
  obtain ⟨b, hb⟩ := GlobalTheory.ShFam.Horiz.rigid (Φ.C k) τ.2 hh hflat
  have hΨ : ∀ ρ : D.host.E →+* ℂ, Formalism.L2.PjFree.relab κ.c κ.σ₀ ρ ∈ ((s.U κ.σ₀).X k).Ψ ↔ ρ (A.H.rt : D.host.E) = A.H.rt0 :=
    fun ρ => ((hU.2.1 k).2 _).trans (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt κ.c κ.σ₀ hσ ρ)
  have hrel : Formalism.L2.PjFree.relab κ.c κ.σ₀ τ.1 = τ.1 := GlobalTheory.LettersCheck.relab_val κ.c τ.1
  have hτ' := (hΨ τ.1).2 τ.2
  obtain ⟨c₀, hc₀, hper⟩ := GlobalTheory.T.period_relabel_matrix _ A.H S.Dw κ.l κ.c κ.σ₀ N ((s.U κ.σ₀).X k) (Fu.Di (ik k)) τ.1 hτ' (φ k)
    (x (ik k)) (hm (ik k)) hU.1 (hU.2.1 k).1 τ.2 hΨ (hEF k) (hx (ik k))
  have key : ∀ y (hy : y ∈ ((s.U κ.σ₀).X k).dom), c₀ * GlobalTheory.FlatLine.horizGen ⟨_, hτ'⟩ y =
      b * Formalism.L2.PjFree.rdU (s.U κ.σ₀) f k y := by
    intro y hy
    obtain ⟨Pm, h1, h2, h3, h4, -⟩ := hun k ⟨y, hy⟩
    let Q : (Fu.Di (ik k)).La →+ (Letter S.Dw → ℂ) :=
      { toFun := fun v z => Pm v (e.symm z)
        map_zero' := by funext z; simp
        map_add' := fun a b => by funext z; simp }
    have hQ : ∀ v z, Q v z = Formalism.L2.PjFree.perFr ((s.U κ.σ₀).X k) y (φ k v : Fin N → D.host.E)
        (Formalism.L2.PjFree.relab κ.c κ.σ₀ z.1) z.2 := fun v z => by
      have := h1 v (e.symm z)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hP := GlobalTheory.T.period_unfolded_family_point _ A.H S.Dw κ.l s.Xo κ.c _ _ s.T.Z κ.σ₀ N g (s.U κ.σ₀) e Fu k (ik k) ⟨y, hy⟩ Pm h2 h3 h4 Q
      (fun _ _ => rfl)
    have e1 := GlobalTheory.ShFam.Hor.horOf_eq κ.good hx _ (ik k) Q hP
    rw [← hper y hy Q hQ, ← e1]
    have hc := GlobalTheory.T.flag_torus_algebraically_closed _ A.H S.Dw κ.l s.Xo κ.c _ _ s.T.Z _ κ.e κ.σ₀ N (s.U κ.σ₀) Φ hσ hU s.geo k ⟨y, hy⟩
    letI : Field (CAt κ.σ₀) := inferInstanceAs (Field ℂ)
    obtain ⟨p, hp1, hp2⟩ := (GlobalTheory.T.coordinate_sections_of_weight _ A.H S.Dw κ.l s.Xo κ.c _ _ s.T.Z _ κ.e (Φ.C k) (CAt κ.σ₀) ((s.U κ.σ₀).un k ⟨y, hy⟩)
      (GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw τ) 0) rfl f hf _).2 ⟨hc, rfl⟩
    have hn : (fun z => -GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw τ) 0 (some z)) =
        expo S.Dw (detSym S.Dw (fun _ => false) none τ.1) := funext (GlobalTheory.ShFam.Horiz.neg_exOf_flatWt τ)
    rw [hn] at hp2
    have hstr : p ≫ (Φ.C k).Y.str = spMap (κ.σ₀.comp κ.e.toRingHom) := by
      rw [← (Φ.C k).π_str, ← Category.assoc, hp1, ← Category.assoc]
      exact (congrArg (· ≫ spMap κ.e.toRingHom) (GlobalTheory.ShFam.Horiz.ptF_jQ_over s.T.Z _)).trans (GlobalTheory.ShFam.HolFrames.spMap_comp₂ _ _).symm
    have hin : GlobalTheory.ShFam.Hor.Inner (GlobalTheory.ShFam.Horiz.cxOf s.T.Z ((s.U κ.σ₀).un k ⟨y, hy⟩)).1 := fun hb' =>
      hb' ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have := hb (GlobalTheory.ShFam.Horiz.cxOf s.T.Z ((s.U κ.σ₀).un k ⟨y, hy⟩)) ⟨p, hstr⟩ _ hin hp1.symm
      (GlobalTheory.ShFam.Horiz.isCoord_frameCast _ hp2)
    rw [this]
    congr 1
    have hrd : Formalism.L2.PjFree.rdU (s.U κ.σ₀) f k y = Formalism.L2.PjFree.toC (evR s.Xo κ.c f ((s.U κ.σ₀).un k ⟨y, hy⟩)) := dif_pos hy
    exact hrd.symm
  have ee : (⟨_, hτ'⟩ : ((s.U κ.σ₀).X k).Ψ) = ⟨τ.1, hτ⟩ := Subtype.ext hrel
  rw [ee] at key
  have hg : ∀ y ∈ ((s.U κ.σ₀).X k).dom, GlobalTheory.FlatLine.horizGen ⟨τ.1, hτ⟩ y ≠ 0 := fun y hy =>
    inv_ne_zero (hy _).1
  by_cases hne : ((s.U κ.σ₀).X k).dom.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hb0 : b ≠ 0 := fun h0 => mul_ne_zero hc₀ (hg y₀ hy₀) (by rw [key y₀ hy₀, h0, zero_mul])
    refine ⟨Units.mk0 (c₀ / b) (div_ne_zero hc₀ hb0), fun y hy => ?_⟩
    have := key y hy
    rw [Units.val_mk0, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ hb0]
  · exact ⟨1, fun y hy => (hne ⟨y, hy⟩).elim⟩
