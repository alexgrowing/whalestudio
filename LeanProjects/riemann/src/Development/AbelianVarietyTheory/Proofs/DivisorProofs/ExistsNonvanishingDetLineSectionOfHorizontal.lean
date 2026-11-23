import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHolFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.DetLine.FromGeneric GlobalTheory.ShFam.Hor.Sec

namespace GlobalTheory.DetLine.FromHorizontal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_renumber {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {m n : ℕ} (h : m = n)
    {x x' : Sp R ⟶ S} (hx : x = x') {v v' : Fin n → (Sp (DualNumber R) ⟶ t.G.left)}
    {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hu : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v i = u k)
    (hu' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → v' i = u' k) {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i, IsCombAtG t x v (M i) (v' i)) :
    ∃ M' : Matrix (Fin m) (Fin m) R, M'.det = M.det ∧ ∀ i, IsCombAtG t x' u (M' i) (u' i) := by
  subst h hx
  obtain rfl : v = u := funext fun i => hu i i rfl
  obtain rfl : v' = u' := funext fun i => hu' i i rfl
  exact ⟨M, rfl, hM⟩

theorem comb_left {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {n : ℕ} {a : Fin n → R}
    {u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} {z : epsAt x ⟶ t.G} (h : FramedFlatCoordinates.IsCombination x a u z) :
    IsCombAtG t x u a z.left :=
  have ⟨u', h₁, h₂⟩ := h
  ⟨u', h₁, congrArg CommaMorphism.left h₂.symm⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {V : Set (gen Y)} {τ : E →+* ℂ} {e : c.F →+* ℂ}

variable (Y V τ) in

abbrev Fr (R : Type) [CommRing R] : Type := Framed c Y.t (genι Y) (genStr Y) V τ D.p D.q R

def Agree {R : Type} [CommRing R] (f : Fr Y V τ R)
    (u : ∀ ρ : E →+* ℂ, Fin (D.mult ρ) → (Sp (DualNumber R) ⟶ Y.t.G.left)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (f.2.1 i).left = u τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (f.2.2.1 i).left = u (conjEmb τ) k

theorem exists_pullFr {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : Fr Y V τ R)
    {x' : Sp R' ⟶ gen Y} (hx : x' = spMap g ≫ b.1) :
    ∃ v w hf, factor g b (⟨x', v, w, hf⟩ : Fr Y V τ R') = 1 ∧
      ∀ u u', Agree b u → (∀ ρ i, u' ρ i = spMap (Chart.dualMapR g) ≫ u ρ i) →
        Agree (⟨x', v, w, hf⟩ : Fr Y V τ R') u' := by
  obtain ⟨j, h⟩ := b.2.2.2
  obtain ⟨v, w, h', a, a'⟩ := exists_pull g h hx
  refine ⟨v, w, ⟨_, h'⟩, ?_, fun u u' hu hu' => ⟨fun i k e => ?_, fun i k e => ?_⟩⟩
  · have h1 : IsChg Y.t (genι Y) g b.1 b.2.1 b.2.2.1 x' v w 1 1 := by
      refine ⟨hx, fun i => ?_, fun i => ?_⟩
      · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
      · simp only [← a']; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
    have := (factor_spec g b ⟨x', v, w, _, h'⟩ hx).2 1 1 h1
    rw [Matrix.det_one, Matrix.det_one, _root_.mul_one] at this
    exact this.symm
  · rw [hu', ← hu.1 i k e]; exact a i
  · rw [hu', ← hu.2 i k e]; exact a' i

theorem hor_factor (hτ : τ (H.rt : E) = H.rt0) {h : CxFr Y e → ℂ} (hh : HorFn τ h) {a a' : CxFr Y e} (hi : Inner a.1)
    (ha : a.1 = a'.1) {f f' : Fr Y V τ ℂ} (hf : f.1 = a.1.1) (hf' : f'.1 = a'.1.1) (hm : Agree f a.2.v)
    (hm' : Agree f' a'.2.v) : h a' = factor (RingHom.id ℂ) f f' * h a := by
  have hx : f'.1 = spMap (RingHom.id ℂ) ≫ f.1 := by rw [DetExtendZero.spMap_id, Category.id_comp, hf, hf', ha]
  obtain ⟨j, k⟩ := f.2.2.2
  obtain ⟨j', k'⟩ := f'.2.2.2
  obtain ⟨-, M, N, hc⟩ := exists_chg _ k k' hx
  have h1 := (factor_spec _ f f' hx).2 M N hc
  have h2 := (chg_isUnit k k' hc).1
  obtain ⟨-, hM, hN⟩ := hc
  simp only [DetExtendZero.dual_id, Category.id_comp] at hM hN
  obtain ⟨M', eM, hM'⟩ := exists_renumber (GlobalTheory.Harm.mult_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.1 hm'.1
    fun i => comb_left (hM i)
  obtain ⟨N', eN, hN'⟩ := exists_renumber (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) (congrArg (· ≫ genι Y) hf') hm.2 hm'.2
    fun i => comb_left (hN i)
  have := hh.2.1 a a' M' N' hi ⟨ha, hM'⟩ ⟨ha, hN'⟩
  rw [eM, eN, h1] at this
  exact h2.mul_right_cancel (by rw [this]; ring)

theorem exists_section_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∃ σb : RuleY Y, SecY Y V τ σb ∧ NzY Y V τ σb := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hs hτ hh
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hs
  let sp (y : B.X) : Sp Γ(B.X, W y) ⟶ B.X := (hW y).fromSpec
  have hr {T : Scheme.{0}} (x : T ⟶ B.X) : Set.range (x ≫ io) ⊆ V := by
    rintro _ ⟨z, rfl⟩
    rw [← hV, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  choose bv bw hb hm using fun y =>
    (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) (sp y ≫ io) (hφ y) (hr _) (fr y)).1
  let b (y : B.X) : Fr Y V τ Γ(B.X, W y) := ⟨sp y ≫ io, bv y, bw y, _, hb y⟩
  let gm {U : B.X.Opens} {z : B.X} (hz : z ∈ U) : Γ(B.X, U) →+* B.X.presheaf.stalk z := (B.X.presheaf.germ U z hz).hom
  have hloc {y z : B.X} (hz : z ∈ W y) : locPt B.X z ≫ io = spMap (gm hz) ≫ (b y).1 := by
    rw [← Category.assoc]
    exact congrArg (· ≫ io) ((hW y).fromSpecStalk_eq_fromSpecStalk hz).symm
  choose ev ew he _ using fun z => exists_pullFr (gm (hy z)) (b z) (hloc (hy z))
  let fz (z : B.X) : Fr Y V τ (B.X.presheaf.stalk z) := ⟨locPt B.X z ≫ io, ev z, ew z, he z⟩
  have hgen (z : B.X) : genPt B.X ≫ io = spMap (algebraMap _ B.X.functionField) ≫ (fz z).1 := by
    rw [genPt_eq z, Category.assoc]
  obtain ⟨v₀, w₀, ⟨j₀, h₀⟩, -⟩ := exists_pullFr _ (fz (genericPoint B.X)) (hgen _)
  let a₀ : Fr Y V τ B.X.functionField := ⟨genPt B.X ≫ io, v₀, w₀, j₀, h₀⟩
  choose ε hε using fun z => (factor_spec _ (fz z) a₀ (hgen z)).1
  have hu {y z : B.X} (hz : z ∈ W y) : IsUnit (factor (gm hz) (b y) (fz z)) := (factor_spec _ _ _ (hloc hz)).1
  have hk (y : B.X) : a₀.1 = spMap (fnOf (W y) (gen_mem (hy y))) ≫ (b y).1 := hloc (gen_mem (hy y))
  choose δ hδ using fun y => (factor_spec _ (b y) a₀ (hk y)).1
  have hδε {y z : B.X} (hz : z ∈ W y) : (δ y : B.X.functionField) =
      ε z * algebraMap _ B.X.functionField (factor (gm hz) (b y) (fz z)) := by
    rw [hδ, hε, ← factor_comp _ _ _ _ _ (hloc hz) (hgen z)]
    congr 1
    exact (RingHom.ext fun r => algebraMap_germ hz r).symm
  have hg {y z : B.X} (hz : z ∈ W y) : germOf z (ε z)⁻¹ = germOf z (δ y)⁻¹ := by
    rw [germOf_eq_iff, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv, ← inv_div, hδε hz,
      mul_div_cancel_left₀ _ (ε z).ne_zero]
    exact UnitAt.inv ⟨_, hu hz, rfl⟩
  let Dv : B.Dv := show cartierGroup B.X from ⟨fun z => germOf z (ε z)⁻¹, fun y => ⟨W y, hy y, (δ y)⁻¹, fun z hz => hg hz⟩⟩
  have hD (y : B.X) (z : B.X) (hz : z ∈ W y) : Dv.IsEqn z (δ y)⁻¹ := hg hz
  obtain ⟨hne, hd⟩ := GlobalTheory.T.complexPoints_nonempty_dense_variety c.F B e
  have hA := hd (io ⁻¹ᵁ (genBd Y).compl) (by
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      ⟨_, genericPoint B.X, rfl⟩
    exact ⟨z, fun hb => hb hz⟩)
  let R := AnRead.all B.str e B.dim
  choose u hu₁ he₁ using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y) hh.2.2.1 hh.2.2.2
  choose u' hu' he' using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  have h0 (y) (z) (hz : z ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y z) ≠ 0 :=
    hh.1 _ ((inner_iff (ha y z)).2 hz)
  have htr (y y') (U : B.X.Opens) (r : Γ(B.X, U))
      (hr : ∀ hU, fnOf U hU r = (δ y' : B.X.functionField) / (δ y : B.X.functionField)) (p : CxPts B.str e)
      (h₁ : p ∈ ptsIn _ _ (W y)) (h₂ : p ∈ ptsIn _ _ (W y')) (h₃ : p ∈ ptsIn _ _ U)
      (hz : p ∈ ptsIn _ _ (io ⁻¹ᵁ (genBd Y).compl)) : h (a y p) = CxPts.ev _ _ U r p * h (a y' p) := by
    let z : B.X := p.1 (IsLocalRing.closedPoint ℂ)
    let χ : B.X.presheaf.stalk z →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
    have hχ {U : B.X.Opens} (h : p ∈ ptsIn _ _ U) : χ.comp (gm (mem_ptsIn.1 h)) = evHom h :=
      (congrArg CommRingCat.Hom.hom (HolFrames.valR_eq_germ p.1 U h)).symm
    have hp : p.1 ≫ io = spMap χ ≫ (fz z).1 := by
      rw [← Category.assoc]
      exact congrArg (· ≫ io) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of ℂ) p.1).symm
    have hq {y : B.X} (h : p ∈ ptsIn _ _ (W y)) : p.1 ≫ io = spMap (evHom h) ≫ (b y).1 := by
      rw [← hχ, DetExtendZero.spMap_comp, Category.assoc, ← hloc, hp]
    obtain ⟨v, w, k, e₁, m⟩ := exists_pullFr _ (b y) (hq h₁)
    obtain ⟨v', w', k', e₂, m'⟩ := exists_pullFr _ (b y') (hq h₂)
    rw [hor_factor hτ hh ((inner_iff (ha y' p)).2 hz) (Subtype.ext ((ha y' p).trans (ha y p).symm))
      (f := ⟨_, v', w', k'⟩) (f' := ⟨_, v, w, k⟩) (ha y' p).symm (ha y p).symm
      (m' _ _ (hm y') (hv y' p h₂)) (m _ _ (hm y) (hv y p h₁))]
    congr 1
    have e₃ := factor_comp (evHom h₂) (RingHom.id ℂ) (b y') ⟨_, v', w', k'⟩ ⟨_, v, w, k⟩ (hq h₂)
      (by rw [DetExtendZero.spMap_id, Category.id_comp])
    rw [e₂, map_one, _root_.mul_one, RingHom.id_comp, ← hχ,
      factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₂)) hp] at e₃
    rw [← hχ, factor_comp _ χ _ (fz z) ⟨_, v, w, k⟩ (hloc (mem_ptsIn.1 h₁)) hp] at e₁
    have e₄ : factor (gm (mem_ptsIn.1 h₂)) (b y') (fz z) =
        factor (gm (mem_ptsIn.1 h₁)) (b y) (fz z) * gm (mem_ptsIn.1 h₃) r := by
      refine IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField (mul_left_cancel₀ (ε z).ne_zero ?_)
      rw [map_mul, ← _root_.mul_assoc, ← hδε, ← hδε]
      erw [algebraMap_germ]
      rw [hr, mul_div_cancel₀ _ (δ y).ne_zero]
    rw [← e₃, e₄, map_mul, ← _root_.mul_assoc, e₁, _root_.one_mul, ev_eq h₃, ← hχ]
    rfl
  obtain ⟨s, hs⟩ := exists_generates B Dv
    (GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W (fun y => (δ y)⁻¹) hy hD u hu₁
      (fun y z hz => by rw [he₁ y hz]; exact h0 y z hz.2) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he₁ y ⟨hz'.1, hz.2⟩, he₁ y' ⟨hz'.2, hz.2⟩]
        exact htr y y' _ r (fun hU => by
          rw [hr', Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_div_inv]) z hz'.1 hz'.2 hz.1 hz.2))
    (GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot c.F B _ R _ (holSec_ne_bot hA _ W δ hy (fun y y' hy => inv_inv (δ y) ▸ (hD y y' hy).neg) u' hu'
      (fun y z hz => by rw [he' y hz]; exact inv_ne_zero (h0 y z hz.2)) fun y y' r hr' z hz => by
        have hz' := mem_ptsIn_inf.1 hz.1
        rw [he' y ⟨hz'.1, hz.2⟩, he' y' ⟨hz'.2, hz.2⟩]
        rw [eq_mul_inv_iff_mul_eq₀ (h0 y' z hz.2), htr y' y _ r hr' z hz'.2 hz'.1 hz.1 hz.2, _root_.mul_comm,
          mul_inv_cancel_right₀ (h0 y z hz.2)]))
  obtain ⟨σ, h1, h2, -⟩ := exists_section E H l c _ _ Y.t (genι Y) (genStr Y) τ D.p D.q B.X io V hio hV
    (hV ▸ frameCover_gen E H D l Xo c O β Y io.opensRange τ hτ) j₀ v₀ w₀ s h₀ fun z => by
      obtain ⟨j, hj⟩ := he z
      obtain ⟨-, M, N, hc⟩ := exists_chg _ hj h₀ (hgen z)
      obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (show Dv.IsEqn z (ε z)⁻¹ from rfl).generatesAt_iff.1 (hs z)
      refine ⟨j, ev z, ew z, M, N, t, hj, hc, ?_⟩
      rw [(factor_spec _ (fz z) a₀ (hgen z)).2 M N hc, ← hε, ht, Units.val_inv_eq_inv_val]
      have := (ε z).ne_zero
      field_simp
  exact ⟨σ, h1, h2⟩

end GlobalTheory.DetLine.FromHorizontal
