import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem top_le_fromSpecStalk {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens) (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem val_fromSpecStalk {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B ⊤)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y (memTop y) hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  have hV : y ∈ (⊤ : Y.Opens) ⊓ B.U i := memInf (memTop y) hi
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ ((⊤ : Y.Opens) ⊓ B.U i) := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open (IsOpen.inter isOpen_univ (B.U i).isOpen) hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_congr' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr'' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

set_option maxHeartbeats 1000000 in

theorem evI_ofSpace_eq_prod_mul_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (x₀ : Sp T.Fr ⟶ Y₀ X Z), (X.ptY y'.1 = x₀ ≫ inc₀ X Z) → ∀ (j' : (L₀ X Z la).ι) (hO : ⊤ ≤ x₀ ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)) (hj : ⊤ ≤ x₀ ⁻¹ᵁ (L₀ X Z la).U j') (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit)) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr (j' PUnit.unit) (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) = (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix).val * H0.val x₀ j' hO hj w.1 := by
  intro E _ _ _ H Dw l Xo c Y X Z r U la w T io y' x₀ hx j' hO hj hz Q t hQ ht
  letI := io.toAlgebra
  let fS : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0) := ⟨_, cusp_le_secZ Z U la (ofSpace X Z U la w).2⟩
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf fS hOf hQ ht
  show evR Xo c fS.1 y'.1 = _
  rw [a]
  congr 1
  have hx' : X.pt y'.1 ≫ X.inc = x₀ ≫ inc₀ X Z := (X.pt_inc _).trans hx
  have hU₀ : ⊤ ≤ x₀ ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  have hk' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (j' PUnit.unit) := hx' ▸ hz
  have hO' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hx' ▸ hOf
  rw [val_congr' hx' _ hOf hO' hz hk']
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) x₀ j' hU₀ hj hO' hk' (secOf X _ fS)
  rw [← b1]
  have hs : H0.pull (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X _ fS) = H0.restr le_top w.1 := cuspSec_ofSpace X Z U la w
  rw [hs, val_restr'' le_top x₀ j' hO hU₀ hj]

set_option maxHeartbeats 1000000 in

theorem germ_eq_unit_mul_evI_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (y : Y₀ X Z) (T : CDVR)
    (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z)
    (j' : (L₀ X Z la).ι) (hj' : y ∈ (L₀ X Z la).U j') :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) =
      algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) := by
  letI := io.toAlgebra
  have hk : inc₀ X Z y ∈ X.F.U (j' PUnit.unit) := mem_pull.1 hj'
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hO := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ⊤ (memTop y)
  have hj := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ((L₀ X Z la).U j') hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j' PUnit.unit) := by
    have := top_le_fromSpecStalk y g (inc₀ X Z ⁻¹ᵁ X.F.U (j' PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j' PUnit.unit) hz
  have e2 := evI_ofSpace_eq_prod_mul_val X Z U la w T io y' _ hx₀ j' hO hj hz Q t hQ ht
  have e1 := val_fromSpecStalk y j' hj' ((algebraMap T.V T.Fr).comp g) w.1 hO hj
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j' PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ GlobalTheory.AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, e1, Units.coe_map, RingHom.comp_apply, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one,
    one_mul]

theorem germ_eq_unit_mul_evI : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  exact ⟨C, hC, x0, fun x hx' hle ι p hp i hi Y hY Z TF la w y T io y' g _ hpt j' hj' =>
    germ_eq_unit_mul_evI_core TF.X Z Y.U la w y T io y' g hpt j' hj'⟩

end GlobalTheory.HSApp
