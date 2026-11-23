import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuliStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantComponentFunctionComplexValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantFunctionNormalCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfRankZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingDetLineSectionOfHorizontalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulHorizontalDetLieCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlatOfConstMulPeriodDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConjStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem good_or (c : Coeff l) (e : c.F →+* ℂ) :
    Formalism.L2.PjFree.GoodEmb c e ∨ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp e) := by
  set z := (e.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hz
  have h1 : z ^ 2 = H.rt0 ^ 2 := by rw [hz, ← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact .inl h
  · refine .inr (show starRingEnd ℂ z = H.rt0 from ?_)
    have h4 := H.sqrt_neg_disc_sq
    have h5 := congrArg Complex.im h4
    have h6 := congrArg Complex.re h4
    have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two] at h5 h6
    have h8 : H.rt0.re = 0 := by
      by_contra h0
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h0
      rw [this] at h6
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [h]
    exact Complex.ext (by simp [h8]) (by simp)

section Unique

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {τ : E →+* ℂ} {p q : ℕ}

theorem existsUnique_multiple {V : X.Opens} (hne : (V : Set X).Nonempty)
    (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {σ σ' : Rule t π p q} (hz : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (a : c.F) (h : ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V (Geo.Tor.constFn s V a) * σ R x v w) :
    ∃! a : c.F, IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := by
  have h1 : IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := fun R _ j x v w hf => by
    rw [h R j x v w hf, GlobalTheory.Points.valR_constFn_of_over s j x hf.1 V (fun z _ => hf.2.1 ⟨z, rfl⟩)]
  refine ⟨a, h1, fun b hb => ?_⟩
  obtain ⟨z, hzV⟩ := hne
  obtain ⟨W, hW, j, v, w, hzW, hf⟩ := hc z hzV
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  exact j.injective ((hz _ j _ v w hf).mul_right_cancel ((hb _ j _ v w hf).symm.trans (h1 _ j _ v w hf)))

end Unique

variable {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_of_geomConn {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) :
    (U : Set (Xo.XF c)).Nonempty := by
  have := GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli E H D l Xo c U hG
  exact ⟨_, (genericPoint U.toScheme).2⟩

theorem flat_unique {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (e : c.F →+* ℂ) (hT : HasTransport Xo c U e) {σ σ' : RuleU Xo c}
    (hs : SecU Xo c U τ σ) (hz : NzU Xo c U τ σ) (hf : IsFlatAt Xo c U τ σ e) (hs' : SecU Xo c U τ σ')
    (hf' : IsFlatAt Xo c U τ σ' e) :
    ∃! a : c.F, IsMultiple Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ' a σ := by
  have hc := GlobalTheory.T.moduliScheme_affineFrameCover_two_eigenParts E H D l Xo c U τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ U σ σ' hc hs hz hs'
  have fr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → Set.range y ⊆ U → ∃ v w, FrU Xo c U τ e y v w :=
    fun y hy hU => by
      obtain ⟨W, hW, j, v, w, hzW, h⟩ := hc _ (hU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)
      have hle : ⊤ ≤ y ⁻¹ᵁ W := (GlobalTheory.Points.le_preimage_iff y W).2 hzW
      have hy' := (GlobalTheory.Points.specMap_valMap_fromSpec hW y hle).symm
      obtain ⟨v', w', h', -⟩ := exists_pull (GlobalTheory.Points.valMap y W hle).hom h hy'
      obtain rfl : e = (GlobalTheory.Points.valMap y W hle).hom.comp j :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans h'.1))
      exact ⟨v', w', h'⟩
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_constant_component_function_complexValues E H D l Xo c U e f hG fun y y' hy hy' hU hU' => by
    obtain ⟨v, w, h⟩ := fr y hy hU
    obtain ⟨v', w', h'⟩ := fr y' hy' hU'
    obtain ⟨o, m, g, u, Hm, κ, V, W, hA, hV, hW, iV, iW⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y v w h
    obtain ⟨o', m', g', u', Hm', κ', V', W', hA', hV', hW', -⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y' v' w' h'
    obtain ⟨φ, hφ⟩ := hT y y' hy hy' hU hU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm' κ κ' hA hA'
    obtain ⟨x, Δ, hΔ, hx⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g _ _ Hm V W hA.1 hA.2.1).2 iV iW
    obtain ⟨Δ', hx'⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g' _ _ Hm' V' W' hA'.1 hA'.2.1).1 fun k => φ (x k)
    have e1 := hf y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    have e2 := hf' y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    rw [hr ℂ e y v w h, hr ℂ e y' v' w' h', _root_.mul_assoc, _root_.mul_assoc, e1] at e2
    exact mul_right_cancel₀ (mul_ne_zero (hz ℂ e y' v' w' h').ne_zero hΔ) e2
  exact existsUnique_multiple (nonempty_of_geomConn hG) hc hz a hr

theorem cpt_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {U : (Xo.XF c).Opens}
    (hN : Geo.Tor.IsNormalScheme (gen Y)) (hU : IsClosed (U : Set (Xo.XF c)))
    (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {σ σ' : RuleY Y}
    (hs : SecY Y (compactOf Y U) τ σ) (hz : NzY Y (compactOf Y U) τ σ) (hs' : SecY Y (compactOf Y U) τ σ') :
    ∃! a : c.F, IsMultiple Y.t (genι Y) (genStr Y) (compactOf Y U) (HermitianCompactForm.chi c τ) σ' a σ := by
  obtain ⟨V, hV, -⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hN hU hG
  have hne : (V : Set (gen Y)).Nonempty := hV ▸ ((nonempty_of_geomConn hG).image _).closure
  have hk := GlobalTheory.T.exists_constant_function_normal_compactification E H D l Xo c O β Y U V hN hU hG hV
  rw [← hV] at hs hz hs' ⊢
  have hc := GlobalTheory.T.toroidalGenericFibre_affineFrameCover E H D l Xo c O β Y V τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ V σ σ' hc hs hz hs'
  obtain ⟨a, rfl⟩ := hk f
  exact existsUnique_multiple hne hc hz a hr

def HasFlatSection (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) : Prop :=
  (∀ e : c.F →+* ℂ, HasTransport Xo c U e) ∧ ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ NzU Xo c U τ σ ∧
    (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ e) ∧
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Geo.Tor.IsNormalScheme (gen Y) →
      ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ

theorem exists_of_rank_zero (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (h : D.p + D.q = 0) : HasFlatSection Xo c U τ := by
  have : IsEmpty (Fin D.p) := ⟨fun i => by have := i.2; omega⟩
  have : IsEmpty (Fin D.q) := ⟨fun i => by have := i.2; omega⟩
  refine ⟨fun e => GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero E H D l Xo c U e h, fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun e => ?_, fun O _ β Y _ => ⟨fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩⟩
  intro y y' v w v' w' _ _ o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' _ _ _ _ _ _ _ ⟨a, _, ha⟩ ⟨a', _, ha'⟩
  rw [ha, ha', Matrix.det_isEmpty, Matrix.det_isEmpty]

theorem exists_of_snc {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z))
    {U : (Xo.XF c).Opens} (hU : IsClosed (U : Set (Xo.XF c))) (hG : GeometricallyConnected (U.ι ≫ toF Xo c))
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (hr : 1 ≤ D.p + D.q) : HasFlatSection Xo c U τ := by
  obtain ⟨B, io, h1, h2, h3⟩ := GlobalTheory.T.exists_variety_compactifying_connected_component E H D l Xo c O β Z U hsm hU hG
  have fam : ∀ e : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c e → ∃ (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en)
      (x : ∀ i, Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx D τ) (Idx D τ) E),
      ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i) := fun e he => by
    let en : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
    obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
      (fun j => Formalism.L2.PjFree.relab c e (en j).1) hr he ((GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ en)
    choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ H D (Fu.Di i) τ (Fu.sig i)
    exact ⟨_, en, Fu, x, hm, hx⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀, Formalism.L2.PjFree.GoodEmb c e₀ := (good_or c c.F.val.toRingHom).elim (⟨_, ·⟩) (⟨_, ·⟩)
  obtain ⟨g₀, en₀, Fu₀, x₀, hm₀, hx₀⟩ := fam e₀ he₀
  obtain ⟨σZ, hsZ, hzZ⟩ := GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal E H D l Xo c O β Z τ e₀ _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he₀ hr hx₀)
  obtain ⟨σ, hs, hres, hz⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Z U τ σZ hsZ
  have hflat : ∀ e, Formalism.L2.PjFree.GoodEmb c e → IsFlatAt Xo c U τ σ e := fun e he => by
    obtain ⟨g, en, Fu, x, hm, hx⟩ := fam e he
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate E H D l Xo c O β Z τ e _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he hr hx) σZ hsZ
    refine GlobalTheory.T.isFlat_of_const_mul_periodDeterminant E H D l Xo c O β Z U τ e g en Fu x hm σZ σ κ B io hU h1 h2 h3 hτ hx hres
      fun a v w i Q hP hf hM => ?_
    rw [← horOf_eq_perVal hx a i Q hP]
    refine hκ a v w ?_ hf hM
    obtain ⟨P, W, y, -, -, hy, -⟩ := hP
    exact fun h => h ⟨y (IsLocalRing.closedPoint ℂ), by rw [← hy]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨fun e => ?_, σ, hs, hz hzZ, fun e => ?_, fun O' _ β' Y hN =>
    GlobalTheory.T.exists_nonvanishing_extension_normal_compactification E H D l Xo c O' β' Y O β Z U τ σZ σ hN hU hG hτ hsZ hzZ hs hres⟩
  · rcases good_or c e with he | he
    · exact GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U e B io hU h1 h2 h3 hr he
    · exact GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding E H D l Xo c U e (GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U _ B io hU h1 h2 h3 hr he)
  · rcases good_or c e with he | he
    · exact hflat e he
    · exact GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj E H D l Xo c U τ σ e hs (hflat _ he)

theorem detLineTrivial_of_toroidal (hT : GlobalTheory.Published.ToroidalCompactification) : DetLineTrivial := by
  intro E _ _ _ H D l Xo c U hU hG τ hτ
  have hex : HasFlatSection Xo c U τ := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
    · exact exists_of_rank_zero U τ h
    · obtain ⟨Z, hsm, hsnc, -⟩ := hT E H D h l Xo c
      exact exists_of_snc Z
        ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm)
        (GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary hsnc) hU hG hτ h
  obtain ⟨htr, σ, hs, hz, hf, hY⟩ := hex
  refine ⟨htr, σ, hs, hz, hf, fun σ' hs' hf' => ?_, fun O _ β Y hN => ?_⟩
  · exact flat_unique hG hτ c.F.val.toRingHom (htr _) hs hz (hf _) hs' (hf' _)
  · obtain ⟨σb, h1, h2, h3⟩ := hY O β Y hN
    exact ⟨σb, h1, h2, h3, fun σ' h' => cpt_unique Y hN hU hG hτ h1 h2 h'⟩

end GlobalTheory.DetLine
