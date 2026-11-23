import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleGluingCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightThirdStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat.GrGlue

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

theorem norm_le_one {C : Type} [NormedField C] {φ : c.F →+* C} {x : Sp C ⟶ Z.X} {τ : E →+* ℂ} {r : ℕ}
    {u u' : Fin r → (Sp (DualNumber C) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) (hu' : IsEigBasis Z φ x τ u')
    {P : (Sp (DualNumber C) ⟶ Z.t.G.left) → Prop}
    (h : ∀ w, IsEigTan Z φ x τ w → ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u a w) ↔ P w))
    (h' : ∀ w, IsEigTan Z φ x τ w → ((∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u' a w) ↔ P w))
    {i : Fin r} {a : Fin r → C} (ha : IsCombAtG Z.t x u a (u' i)) (b : Fin r) : ‖a b‖ ≤ 1 := by
  have h1 : P (u' i) := by
    refine (h' _ (hu'.1 i)).1 ⟨Pi.single i 1, fun k => ?_, isCombAtG_single Z.t x (fun j => (hu'.1 j).1) i⟩
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  obtain ⟨a', ha', hc⟩ := (h _ (hu'.1 i)).2 h1
  rw [(hu.2 _ (hu'.1 i)).unique ha hc]
  exact ha' b

theorem exists_isTrans {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) [IsAffineHom jB] (hI : IntCrit (πB ≫ genStr Z ≫ spMap e.toRingHom) jB) {r : ℕ} {τ : E →+* ℂ}
    {U U' : X.Opens} {u : LocAssign Z r jB U} {u' : LocAssign Z r jB U'} (hV : IsAffineOpen (U ⊓ U'))
    (hu : IsLocFrame Z e jB πB r τ U u) (hu' : IsLocFrame Z e jB πB r τ U' u')
    (hL : IsLocGrLat Z e jB πB r τ U u) (hL' : IsLocGrLat Z e jB πB r τ U' u') :
    ∃ A : Matrix (Fin r) (Fin r) Γ(X, U ⊓ U'), IsTrans Z jB πB u u' A := by
  obtain ⟨T, hT⟩ := Trans.exists_generic Z e jB πB (hV.preimage jB) hu hu'
  have key : ∀ b i, ∃ f₀ : Γ(X, U ⊓ U'), jB.app (U ⊓ U') f₀ = T b i := fun b i => by
    refine hI _ hV _ fun v ε xg xt h1 h2 h3 hx => ?_
    obtain ⟨hp, hio, -⟩ := ioOf_spec F v ε
    haveI : Fact (resP v).Prime := ⟨hp⟩
    have hxU : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U := fun p hp => (hx hp).1
    have hxU' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U' := fun p hp => (hx hp).2
    have hd := hL v hp ε xg xt h1 h2 (fun p hp => (h3 hp).1) hxU
    have hd' := hL' v hp ε xg xt h1 h2 (fun p hp => (h3 hp).2) hxU'
    have h4 : (spMap (ioOf (resP v) ε) ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
        spMap ((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))) := by
      rw [Category.assoc, h1, sp_comp]
    have hy : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U := fun p _ => hxU (Set.mem_univ _)
    have hy' : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U' := fun p _ => hxU' (Set.mem_univ _)
    have b1 := hu.1 _ _ hy _ h4
    have b2 := hu'.1 _ _ hy' _ h4
    rw [show u _ _ hy = _ from funext fun k => hu.2 _ _ _ xg hxU hy k, Category.assoc] at b1
    rw [show u' _ _ hy' = _ from funext fun k => hu'.2 _ _ _ xg hxU' hy' k, Category.assoc] at b2
    exact (hio _).1 (norm_le_one Z b1 b2 hd hd'
      (GlobalTheory.LatDRFree.comb_map Z.t (ioOf (resP v) ε) (hT _ xg hxU hxU' hx i)) b)
  choose A hA using key
  refine ⟨Matrix.of A, fun K _ x hx hx' hxx i => ?_⟩
  have h := hT K x hx hx' hxx i
  simp only [← hA] at h
  simp only [Matrix.of_apply, Trans.evalPt_app]
  exact h

theorem span_mono {C : Type} [NormedField C] [IsUltrametricDist C] {x : Sp C ⟶ Z.X} {r : ℕ}
    {u u' : Fin r → (Sp (DualNumber C) ⟶ Z.t.G.left)} (hu : ∀ i, IsTanAtG Z.t x (u i)) (hu' : ∀ i, IsTanAtG Z.t x (u' i))
    (A : Matrix (Fin r) (Fin r) C) (hA : ∀ a i, ‖A a i‖ ≤ 1) (h : ∀ i, IsCombAtG Z.t x u (fun a => A a i) (u' i))
    {w : Sp (DualNumber C) ⟶ Z.t.G.left} (hw : IsTanAtG Z.t x w)
    (hb : ∃ b : Fin r → C, (∀ i, ‖b i‖ ≤ 1) ∧ IsCombAtG Z.t x u' b w) :
    ∃ a : Fin r → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t x u a w := by
  obtain ⟨b, hb, hc⟩ := hb
  refine ⟨_, fun a => ?_, isCombAtG_mul Z.t x hu hu' hw A b h hc⟩
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA a i) (norm_nonneg _) (hb i)

theorem frame_span_le {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {uu : FrAssign Z M r jB}
    (huu : IsLieFrames Z e jB πB M r τ false uu) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [Fact (resP v).Prime] (ε : TrueGeo.Ext v) (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X)
    (h1 : xg ≫ πB ≫ genStr Z ≫ spMap e.toRingHom = spMap (algebraMap F (AlgebraicClosure F)))
    (h2 : spMap ε.O.subtype ≫ xt = xg ≫ jB) {U U' : X.Opens} {f : Fin r → Γ(M, U)} {f' : Fin r → Γ(M, U')}
    (hf : VB.IsFrame f) (hf' : VB.IsFrame f') (ht : ⊤ ≤ xt ⁻¹ᵁ U) (ht' : ⊤ ≤ xt ⁻¹ᵁ U')
    (hx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U) (hx' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ U') {w : Sp (DualNumber ℂ_[resP v]) ⟶ Z.t.G.left}
    (hw : IsTanAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z) w)
    (hb : ∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
      (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ uu U' f' hf' _ xg hx' i) a w) :
    ∃ a : Fin r → ℂ_[resP v], (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap (ioOf (resP v) ε) ≫ xg ≫ πB ≫ genι Z)
      (fun i => spMap (dualMap (ioOf (resP v) ε)) ≫ uu U f hf _ xg hx i) a w := by
  obtain ⟨hp, hio, -⟩ := ioOf_spec F v ε
  have h4 : (spMap (ioOf (resP v) ε) ≫ xg) ≫ πB ≫ genStr Z ≫ spMap e.toRingHom =
      spMap ((ioOf (resP v) ε).comp (algebraMap F (AlgebraicClosure F))) := by
    rw [Category.assoc, h1, sp_comp]
  have hy : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U := fun p _ => hx (Set.mem_univ _)
  have hy' : ⊤ ≤ ((spMap (ioOf (resP v) ε) ≫ xg) ≫ jB) ⁻¹ᵁ U' := fun p _ => hx' (Set.mem_univ _)
  have b1 := huu.1 U f hf _ _ hy _ h4
  have b2 := huu.1 U' f' hf' _ _ hy' _ h4
  rw [show uu U f hf _ _ hy = _ from funext fun k => huu.2.2 U f hf _ _ _ xg hx hy k, Category.assoc] at b1
  rw [show uu U' f' hf' _ _ hy' = _ from funext fun k => huu.2.2 U' f' hf' _ _ _ xg hx' hy' k, Category.assoc] at b2
  have hxx : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ (U ⊓ U') := fun p hp => ⟨hx hp, hx' hp⟩
  have htt : ⊤ ≤ xt ⁻¹ᵁ (U ⊓ U') := fun p hp => ⟨ht hp, ht' hp⟩
  refine span_mono Z (fun i => (b1.1 i).1) (fun i => (b2.1 i).1)
    (Matrix.of fun a i => ioOf (resP v) ε (evalPt (xg ≫ jB) (U ⊓ U') hxx (trCo hf f' a i))) (fun a i => ?_)
    (fun i => GlobalTheory.LatDRFree.comb_map Z.t (ioOf (resP v) ε) (huu.2.1 U U' f f' hf hf' _ xg hx hx' hxx i)) hw hb
  refine (hio _).2 ?_
  generalize xg ≫ jB = y at h2 hxx
  subst h2
  rw [evalPt_spMap_comp _ xt _ htt hxx]
  exact SetLike.coe_mem _

theorem exists_le_of_cover {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (xt : Sp R ⟶ X) {ι : Type}
    (V : ι → X.Opens) (hcov : ∀ x : X, ∃ i, x ∈ V i) : ∃ i, ⊤ ≤ xt ⁻¹ᵁ V i := by
  obtain ⟨i, hi⟩ := hcov (xt (IsLocalRing.closedPoint R))
  exact ⟨i, (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) xt hi).ge⟩

theorem comp_le_of_le {S T X : Scheme.{0}} (a : S ⟶ T) (b : T ⟶ X) {c : S ⟶ X} (h : a ≫ b = c) {V : X.Opens}
    (hb : ⊤ ≤ b ⁻¹ᵁ V) : ⊤ ≤ c ⁻¹ᵁ V := by
  subst h
  exact fun p _ => hb (Set.mem_univ _)

theorem isGrLat_of_loc {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {uu : FrAssign Z M r jB}
    (h : ∀ (U : X.Opens) (f : Fin r → Γ(M, U)) (hf : VB.IsFrame f), IsLocGrLat Z e jB πB r τ U (uu U f hf)) :
    IsGrLat Z e jB πB M r τ uu :=
  fun v hp ε xg xt h1 h2 U f hf ht hx => h U f hf v hp ε xg xt h1 h2 ht hx

theorem isGrLat_of_cover {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F) {X W : Scheme.{0}} (jB : W ⟶ X)
    (πB : W ⟶ gen Z) {M : X.Modules} {r : ℕ} {τ : E →+* ℂ} {uu : FrAssign Z M r jB}
    (huu : IsLieFrames Z e jB πB M r τ false uu) {ι : Type} (V : ι → X.Opens) (g : ∀ i, Fin r → Γ(M, V i))
    (hg : ∀ i, VB.IsFrame (g i)) (hcov : ∀ x : X, ∃ i, x ∈ V i)
    (hL : ∀ i, IsLocGrLat Z e jB πB r τ (V i) (uu (V i) (g i) (hg i))) : IsGrLat Z e jB πB M r τ uu := by
  refine isGrLat_of_loc Z e jB πB fun U f hf => ?_
  intro v hp ε xg xt h1 h2 ht hx w hw
  obtain ⟨i, ht'⟩ := exists_le_of_cover xt V hcov
  have hx' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V i := comp_le_of_le _ _ h2 ht'
  refine Iff.trans (Iff.intro ?_ ?_) (hL i v hp ε xg xt h1 h2 ht' hx' w hw)
  · exact @frame_span_le _ _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ e _ _ jB πB _ _ _ _ huu v (_) ε xg xt h1 h2 _ _ _ _
      (hg i) hf ht' ht hx' hx w hw.1
  · exact @frame_span_le _ _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ e _ _ jB πB _ _ _ _ huu v (_) ε xg xt h1 h2 _ _ _ _
      hf (hg i) ht ht' hx hx' w hw.1

end GlobalTheory.TwoLat.GrGlue

namespace GlobalTheory.TwoLat

theorem exists_grBundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → ∀ (r : ℕ) (τ : E →+* ℂ),
    (∀ x : X, ∃ (U : X.Opens) (u : LocAssign Z r jB U), x ∈ U ∧ IsAffineOpen U ∧ IsLocFrame Z e jB πB r τ U u ∧
      GlobalTheory.TwoLat.IsLocGrLat Z e jB πB r τ U u) →
    ∃ (M : X.Modules) (uu : FrAssign Z M r jB), IsVB M r ∧ IsLieFrames Z e jB πB M r τ false uu ∧
      GlobalTheory.TwoLat.IsGrLat Z e jB πB M r τ uu := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ _ e X W q jB πB d hq hn hpb r τ h
  choose U u hx hU hfr hlat using h
  have hcov : ∀ x : X, ∃ i, x ∈ U i := fun x => ⟨x, hx x⟩
  have haff : IsAffineHom jB := MorphismProperty.of_isPullback hpb.flip (isAffineHom_of_isAffine _)
  have hsep : X.IsSeparated := by
    have : IsProper q := projProper _ _ _ hq.isProjOver
    exact ⟨by rw [← Limits.terminal.comp_from q]; infer_instance⟩
  have hc := IntCritPf.intCrit F X W q _ jB d hq hn hpb
  choose A hA using fun i j => GrGlue.exists_isTrans Z e jB πB hc ((hU i).inf (hU j)) (hfr i) (hfr j) (hlat i) (hlat j)
  obtain ⟨h1, h2⟩ := isTrans_cocycle E H Dw l Xo c Oz β Z F e X W q jB πB d hq hpb r τ X U u A hfr hA
  obtain ⟨M, f, hf, hm⟩ := GlobalTheory.MatrixCocycle.exists_frames X r X U A hcov h1 h2
  obtain ⟨uu, huu, hag⟩ := GlobalTheory.T.arithmetic_model_flag_height_third E H Dw l Xo c Oz β Z F e X W jB πB M r τ false X U f hf u hcov hfr
    fun i j K _ x h₁ h₂ h₃ a => by
      simp only [cond_false, hm]
      exact hA i j K x h₁ h₂ h₃ a
  refine ⟨M, uu, fun x => ⟨U x, f x, hx x, hf x⟩, huu, GrGlue.isGrLat_of_cover Z e jB πB huu U f hf hcov fun i => ?_⟩
  rw [hag]
  exact hlat i

end GlobalTheory.TwoLat

end

theorem _root_.GlobalTheory.T.model_change_of_field_points_a : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {F : Type} [Field F] [NumberField F] (e : F ≃+* c.F)
    {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {jB : W ⟶ X} {πB : W ⟶ gen Z} {d : ℕ}, IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsPullback jB (πB ≫ genStr Z ≫ spMap e.toRingHom) q (spMap (algebraMap (𝓞 F) F)) → ∀ (r : ℕ) (τ : E →+* ℂ),
    (∀ x : X, ∃ (U : X.Opens) (u : LocAssign Z r jB U), x ∈ U ∧ IsAffineOpen U ∧ IsLocFrame Z e jB πB r τ U u ∧
      GlobalTheory.TwoLat.IsLocGrLat Z e jB πB r τ U u) →
    ∃ (M : X.Modules) (uu : FrAssign Z M r jB), IsVB M r ∧ IsLieFrames Z e jB πB M r τ false uu ∧
      GlobalTheory.TwoLat.IsGrLat Z e jB πB M r τ uu :=
  @GlobalTheory.TwoLat.exists_grBundle
