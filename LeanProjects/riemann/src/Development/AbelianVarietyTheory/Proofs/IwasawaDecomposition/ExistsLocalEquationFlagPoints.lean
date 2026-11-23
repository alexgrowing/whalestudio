import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlagStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HolFrames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq GlobalTheory.Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem comb_trans {X : Scheme.{0}} (t : SAB H X) {L : Type} [CommRing L] [IsLocalRing L] (x : Sp L ⟶ X) {m : ℕ}
    {a b : Fin m → (Sp (DualNumber L) ⟶ t.G.left)} {w : Sp (DualNumber L) ⟶ t.G.left}
    (ha : ∀ j, IsTanAtG t x (a j)) (hb : ∀ j, IsTanAtG t x (b j)) (hw : IsTanAtG t x w)
    {P : Matrix (Fin m) (Fin m) L} {T : Fin m → L}
    (h₁ : ∀ k, IsCombAtG t x a (P k) (b k)) (h₂ : IsCombAtG t x b T w) :
    IsCombAtG t x a (T ᵥ* P) w := by
  obtain ⟨n, xc, hx⟩ := EigLoc.exists_chart t x
  choose ea hea using fun j => vec_exists hx _ (ha j)
  choose eb heb using fun j => vec_exists hx _ (hb j)
  obtain ⟨ew, hew⟩ := vec_exists hx _ hw
  obtain rfl : a = fun j => vec t x xc (ea j) := funext hea
  obtain rfl : b = fun j => vec t x xc (eb j) := funext heb
  subst hew
  have e₁ : ∀ k, eb k = ∑ j, P k j • ea j := fun k => (comb_iff hx _ _ _).1 (h₁ k)
  have e₂ : ew = ∑ k, T k • eb k := (comb_iff hx _ _ _).1 h₂
  refine (comb_iff hx _ _ _).2 ?_
  rw [e₂]
  simp only [e₁, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem exists_tri_chg {A L : Type} [CommRing A] [CommRing L] [IsLocalRing L] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    (f : EigFrame Z φ x) (ψ : A →+* L) {φ' : c.F →+* L} {x' : Sp L ⟶ Z.X} (g a : EigFrame Z φ' x')
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ} (h : f.Tri ψ g t) (τ : E →+* ℂ)
    {P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L}
    (hP : ∀ i, IsCombAtG Z.t x' (a.v τ) (P i) (spMap (dualMap ψ) ≫ f.v τ i)) :
    ∃ M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L, (∀ i, IsCombAtG Z.t x' (a.v τ) (M i) (g.v τ i)) ∧
      M.det = (∏ i, t τ i : Lˣ) * P.det := by
  obtain ⟨rfl, rfl, h⟩ := h
  obtain ⟨gb, hgb⟩ := exists_bc f ψ rfl rfl
  choose T a₁ b₁ c₁ using h τ
  refine ⟨Matrix.of T * P, fun i => ?_, ?_⟩
  · rw [Matrix.mul_apply_eq_vecMul]
    exact comb_trans Z.t _ (a.tan τ) (fun k => hgb τ k ▸ gb.tan τ k) (g.tan τ i) hP (c₁ i)
  · rw [Matrix.det_mul, Matrix.det_of_lowerTriangular (Matrix.of T) (fun i k hk => b₁ i k hk)]
    simp only [Matrix.of_apply, a₁, Units.coe_prod]

theorem exists_coord_chg {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e) {σ : c.F →+* ℂ}
    {U₀ : C.Y.X.Opens} (hU₀ : IsAffineOpen U₀) (hgen : genericPoint C.Y.X ∈ U₀) {φ₀ : c.F →+* Γ(C.Y.X, U₀)}
    (fr₀ : EigFrame Z φ₀ (((show Sp Γ(C.Y.X, U₀) ⟶ C.Y.X from hU₀.fromSpec) ≫ C.π) ≫ genι Z))
    {t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ} (hT : fr₀.Tri (fnOf U₀ hgen) C.f0 t₀)
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (p : CxPts C.Y.str (σ.comp e.toRingHom))
    (h₀ : p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) U₀) (a : EigFrame Z σ ((p.1 ≫ C.π) ≫ genι Z))
    (ha : ∀ ρ i, a.v ρ i = spMap (dualMap (CxPts.evHom h₀)) ≫ fr₀.v ρ i)
    {W : C.Y.X.Opens} (hW : genericPoint C.Y.X ∈ W) (r : Γ(C.Y.X, W))
    (hpW : p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) W) (s : C.Y.Fn)
    (hr : fnOf W hW r = s * ((∏ z : Pad.Letter Dw, t₀ z.1 z.2 ^ expo Dw (detSym Dw (fun _ => false) none τ) z : C.Y.Fnˣ) : C.Y.Fn))
    (g : EigFrame Z σ ((p.1 ≫ C.π) ≫ genι Z)) (v : ℂ)
    (hc : IsCoord C p.1 g (expo Dw (detSym Dw (fun _ => false) none τ)) s v) :
    ∃ (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
      (N : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) ℂ),
      (∀ i, IsCombAtG Z.t ((p.1 ≫ C.π) ≫ genι Z) (a.v τ) (M i) (g.v τ i)) ∧
      (∀ i, IsCombAtG Z.t ((p.1 ≫ C.π) ≫ genι Z) (a.v (conjEmb τ)) (N i) (g.v (conjEmb τ) i)) ∧
      M.det ≠ 0 ∧ M.det * v = CxPts.ev C.Y.str (σ.comp e.toRingHom) W r p * N.det := by
  obtain ⟨y₁, ψ, φ₁, f, t₁, t', r₁, hp, hT₁, hT', hr₁, hv⟩ := hc
  let z : C.Y.X := p.1 (IsLocalRing.closedPoint ℂ)
  let R : Type := C.Y.X.presheaf.stalk z
  let χ : R →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
  let gm : ∀ {W : C.Y.X.Opens}, p ∈ CxPts.ptsIn _ _ W → (Γ(C.Y.X, W) →+* R) := fun {W} h =>
    (C.Y.X.presheaf.germ W z (CxPts.mem_ptsIn.1 h)).hom
  have hχ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W), χ.comp (gm h) = CxPts.evHom h := fun {W} h =>
    (congrArg CommRingCat.Hom.hom (valR_eq_germ p.1 W h)).symm
  have hκ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W) (h' : genericPoint C.Y.X ∈ W),
      (algebraMap R C.Y.X.functionField).comp (gm h) = fnOf W h' := fun {W} h h' =>
    RingHom.ext fun a => algebraMap_germ _ a
  have hs : spMap (gm h₀) ≫ (show Sp Γ(C.Y.X, U₀) ⟶ C.Y.X from hU₀.fromSpec) = C.Y.X.fromSpecStalk z :=
    hU₀.fromSpecStalk_eq_fromSpecStalk (CxPts.mem_ptsIn.1 h₀)
  have inj := IsFractionRing.injective R C.Y.X.functionField
  have hsp : z ⤳ y₁ := by
    have : z ∈ Set.range (C.Y.X.fromSpecStalk y₁) :=
      ⟨spMap ψ (IsLocalRing.closedPoint ℂ), by
        show (spMap ψ ≫ stalkPt C.Y y₁) _ = _
        rw [← hp]⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let ρ : C.Y.X.presheaf.stalk y₁ →+* R := (C.Y.X.presheaf.stalkSpecializes hsp).hom
  have hρ : spMap ρ ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk z :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hψ : χ.comp ρ = ψ := by
    refine spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    rw [spMap_comp₂, Category.assoc, hρ]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of ℂ) p.1).trans hp
  have hκρ : (algebraMap R C.Y.X.functionField).comp ρ = algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField :=
    congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkSpecializes_comp C.Y.X.presheaf _ hsp)
  have tr := exists_transition f fr₀ ρ (gm h₀) (by
      show spMap ρ ≫ C.Y.X.fromSpecStalk y₁ ≫ C.π ≫ genι Z = _
      simp only [← Category.assoc]
      rw [hρ, hs]) inj (hκρ.symm ▸ hT₁) (hκ h₀ _ ▸ hT) χ
  simp only [hχ, hψ, ← funext (ha _)] at tr
  obtain ⟨M₀, uM, dM, cM⟩ := tr τ
  obtain ⟨N₀, uN, dN, cN⟩ := tr (conjEmb τ)
  have hx' : (p.1 ≫ C.π) ≫ genι Z = spMap ψ ≫ stalkPt C.Y y₁ ≫ C.π ≫ genι Z := hT'.1
  rw [← hx'] at cM cN
  obtain ⟨M, hM, eM⟩ := exists_tri_chg f ψ g a hT' τ cM
  obtain ⟨N, hN, eN⟩ := exists_tri_chg f ψ g a hT' (conjEmb τ) cN
  have key : M₀.det * ρ r₁ = gm hpW r * N₀.det := by
    refine inj ?_
    have hM0 := (uM.map (algebraMap R C.Y.X.functionField)).ne_zero
    have hN0 := (uN.map (algebraMap R C.Y.X.functionField)).ne_zero
    rw [map_mul, map_mul, ← RingHom.comp_apply _ (gm hpW), hκ hpW hW, hr, ← RingHom.comp_apply _ ρ, hκρ, hr₁]
    simp only [prod_expo_detSym Dw _ _ hτ, Units.val_div_eq_div_val]
    rw [dM, dN]
    have := (∏ i, t₁ τ i).ne_zero
    have := (∏ i, t₁ (conjEmb τ) i).ne_zero
    field_simp
  refine ⟨M, N, hM, hN, ?_, ?_⟩
  · rw [eM, ← RingHom.map_det]
    exact mul_ne_zero (Units.ne_zero _) (uM.map χ).ne_zero
  · have hA := (∏ i, t' τ i).ne_zero
    have hB := (∏ i, t' (conjEmb τ) i).ne_zero
    have hinv : (∏ z : Pad.Letter Dw, t' z.1 z.2 ^ (-expo Dw (detSym Dw (fun _ => false) none τ) z)) =
        (∏ i, t' (conjEmb τ) i) / ∏ i, t' τ i := by
      simp only [zpow_neg, Finset.prod_inv_distrib, prod_expo_detSym Dw _ _ hτ, inv_div]
    have hk := congrArg χ key
    rw [map_mul, map_mul] at hk
    rw [eM, eN, ← RingHom.map_det, ← RingHom.map_det, hv, hinv, CxPts.ev_eq hpW, ← hχ, ← hψ, Units.val_div_eq_div_val]
    have e : ∀ A B m n x y : ℂ, A ≠ 0 → m * x = y * n → (A * m) * (x * (B / A)) = y * (B * n) :=
      fun A B m n x y hA h => by field_simp; linear_combination B * h
    exact e _ _ _ _ _ _ hA hk

theorem exists_holFrames_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∃ (W : C.Y.X → C.Y.X.Opens) (δ : C.Y.X → C.Y.Fnˣ) (a : C.Y.X → CxPts C.Y.str (σ.comp e.toRingHom) → CxFr Z σ), (∀ y, y ∈ W y) ∧ (∀ y, ∀ y' ∈ W y, (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))).IsEqn y' (δ y)) ∧ (∀ y, ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y), (a y p).1.1 = p.1 ≫ C.π) ∧ (∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (x : V → CxPts C.Y.str (σ.comp e.toRingHom)), IsOpen B → IsHolTo B (fun b => (x b).1) → Set.MapsTo x B (CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y)) → HolFam B (fun b => a y (x b))) ∧ (∀ y y' (U : C.Y.X.Opens) (hU : genericPoint C.Y.X ∈ U) (r : Γ(C.Y.X, U)), fnOf U hU r = (δ y : C.Y.Fn) / (δ y' : C.Y.Fn) → ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y ⊓ W y' ⊓ U), ∃ M N, Chg (a y' p) (a y p) τ M ∧ Chg (a y' p) (a y p) (conjEmb τ) N ∧ M.det ≠ 0 ∧ M.det * CxPts.ev C.Y.str (σ.comp e.toRingHom) U r p = N.det) ∧ ∀ y (U : C.Y.X.Opens) (hU : genericPoint C.Y.X ∈ U) (r : Γ(C.Y.X, U)) (s : C.Y.Fn), fnOf U hU r = s * (δ y : C.Y.Fn) → ∀ p ∈ CxPts.ptsIn C.Y.str (σ.comp e.toRingHom) (W y ⊓ U), ∀ (g : EigFrame Z σ ((a y p).1.1 ≫ genι Z)) (v : ℂ), IsCoord C p.1 g (expo Dw (detSym Dw (fun _ => false) none τ)) s v → ∃ M N, Chg (a y p) ⟨(a y p).1, g⟩ τ M ∧ Chg (a y p) ⟨(a y p).1, g⟩ (conjEmb τ) N ∧ M.det ≠ 0 ∧ M.det * v = CxPts.ev C.Y.str (σ.comp e.toRingHom) U r p * N.det := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ _ e C τ hτ
  choose U hU hy φ fr t _ hφ hT ht using fun y => GlobalTheory.T.exists_affine_eigenframe_flag E H Dw l Xo c O β Z F e C y ⊤ trivial
  have hov : ∀ p : CxPts C.Y.str (σ.comp e.toRingHom), (p.1 ≫ C.π) ≫ genStr Z = spMap σ := fun p => by
    have h1 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      rw [← spMap_comp₂, RingEquiv.toRingHom_comp_symm_toRingHom]
      exact Spec.map_id _
    have h2 : ((p.1 ≫ C.π) ≫ genStr Z) ≫ spMap e.toRingHom = spMap σ ≫ spMap e.toRingHom := by
      rw [Category.assoc, Category.assoc, C.π_str, p.2, spMap_comp₂]
    rw [← Category.comp_id (_ ≫ genStr Z), ← h1, ← Category.assoc, h2, Category.assoc, h1, Category.comp_id]
  have hp : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)) (h : p ∈ CxPts.ptsIn _ _ (U y)),
      spMap (CxPts.evHom h) ≫ (show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)) (h : p ∈ CxPts.ptsIn _ _ (U y)), (p.1 ≫ C.π) ≫ genι Z =
      spMap (CxPts.evHom h) ≫ ((show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) ≫ C.π) ≫ genι Z := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : CxPts C.Y.str (σ.comp e.toRingHom)), ∃ g : EigFrame Z σ ((p.1 ≫ C.π) ≫ genι Z),
      ∀ h : p ∈ CxPts.ptsIn _ _ (U y), ∀ ρ i, g.v ρ i = spMap (dualMap (CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (CxPts.evHom h) (φ' := σ) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H Dw l Xo c O β Z ℂ σ _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, fun y => ∏ z : Pad.Letter Dw, t y z.1 z.2 ^ expo Dw (detSym Dw (fun _ => false) none τ) z,
    fun y p => ⟨⟨p.1 ≫ C.π, hov p⟩, g y p⟩, hy, fun y y' hy' => ?_, fun _ _ _ => rfl,
    fun y V _ _ _ B x hB hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (C.π ⁻¹ᵁ W) ((C.π.app W).hom f), fun ρ i => ?_⟩,
    fun y y' W hW r hr p hpm => ?_, fun y W hW r s hr p hpm g' v hc => ?_⟩
  · have hE : ∀ s : Finset (Pad.Letter Dw), (∑ z ∈ s, expo Dw (detSym Dw (fun _ => false) none τ) z • C.gr z.1 z.2).IsEqn y'
        (∏ z ∈ s, t y z.1 z.2 ^ expo Dw (detSym Dw (fun _ => false) none τ) z) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using CartierDiv.isEqn_zero y'
      | insert z s hz ih =>
        rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht y y' hy' _ _).zsmul _).add ih
    exact hE Finset.univ
  · refine holTan_dualMap hB ((fr y).v ρ i) (fun b hb => CxPts.evHom (hm hb)) (fun a => ⟨_,
      (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (CxPts.ev_eq (hm hb) a).symm⟩) fun b hb => hg y _ (hm hb) ρ i
  · obtain ⟨h₁₂, h₃⟩ := CxPts.mem_ptsIn_inf.1 hpm
    obtain ⟨h₁, h₂⟩ := CxPts.mem_ptsIn_inf.1 h₁₂
    let z : C.Y.X := p.1 (IsLocalRing.closedPoint ℂ)
    let R : Type := C.Y.X.presheaf.stalk z
    let χ : R →+* ℂ := (Scheme.stalkClosedPointTo (R := .of ℂ) p.1).hom
    let gm : ∀ {W : C.Y.X.Opens}, p ∈ CxPts.ptsIn _ _ W → (Γ(C.Y.X, W) →+* R) := fun {W} h =>
      (C.Y.X.presheaf.germ W z (CxPts.mem_ptsIn.1 h)).hom
    have hχ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W), χ.comp (gm h) = CxPts.evHom h := fun {W} h =>
      (congrArg CommRingCat.Hom.hom (valR_eq_germ p.1 W h)).symm
    have hκ : ∀ {W : C.Y.X.Opens} (h : p ∈ CxPts.ptsIn _ _ W) (h' : genericPoint C.Y.X ∈ W),
        (algebraMap R C.Y.X.functionField).comp (gm h) = fnOf W h' := fun {W} h h' =>
      RingHom.ext fun a => algebraMap_germ _ a
    have hs : ∀ y (h : p ∈ CxPts.ptsIn _ _ (U y)),
        spMap (gm h) ≫ (show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) = C.Y.X.fromSpecStalk z := fun y h =>
      (hU y).fromSpecStalk_eq_fromSpecStalk (CxPts.mem_ptsIn.1 h)
    have inj := IsFractionRing.injective R C.Y.X.functionField
    have tr := exists_transition (fr y) (fr y') (gm h₁) (gm h₂) (by
      simp only [← Category.assoc]
      rw [hs y h₁, hs y' h₂]) inj (hκ h₁ _ ▸ hT y) (hκ h₂ _ ▸ hT y') χ
    simp only [hχ] at tr
    have chg : ∀ ρ (M : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) ℂ), (∀ i, IsCombAtG Z.t
        (spMap (CxPts.evHom h₁) ≫ ((show Sp Γ(C.Y.X, U y) ⟶ C.Y.X from (hU y).fromSpec) ≫ C.π) ≫ genι Z)
        (fun j => spMap (dualMap (CxPts.evHom h₂)) ≫ (fr y').v ρ j) (M i)
        (spMap (dualMap (CxPts.evHom h₁)) ≫ (fr y).v ρ i)) →
        Chg (Z := Z) (σ := σ) ⟨⟨p.1 ≫ C.π, hov p⟩, g y' p⟩ ⟨⟨p.1 ≫ C.π, hov p⟩, g y p⟩ ρ M := fun ρ M hM =>
      ⟨rfl, fun i => by
        have := hM i
        rw [← hx y p h₁, ← hg y p h₁, ← funext (hg y' p h₂ ρ)] at this
        exact this⟩
    obtain ⟨M, uM, dM, cM⟩ := tr τ
    obtain ⟨N, -, dN, cN⟩ := tr (conjEmb τ)
    refine ⟨_, _, chg _ _ cM, chg _ _ cN, ?_, ?_⟩
    · rw [← RingHom.map_det]
      exact (uM.map χ).ne_zero
    · rw [← RingHom.map_det, ← RingHom.map_det, CxPts.ev_eq h₃, ← hχ, RingHom.comp_apply, ← map_mul]
      refine congrArg χ (inj ?_)
      have hM0 := (uM.map (algebraMap R C.Y.X.functionField)).ne_zero
      rw [map_mul, ← RingHom.comp_apply _ (gm h₃), hκ h₃ hW, hr]
      simp only [prod_expo_detSym Dw _ _ hτ, Units.val_div_eq_div_val]
      rw [dM, dN]
      have := (∏ i, t y τ i).ne_zero
      have := (∏ i, t y (conjEmb τ) i).ne_zero
      field_simp
  · obtain ⟨h₁, h₃⟩ := CxPts.mem_ptsIn_inf.1 hpm
    obtain ⟨M, N, cM, cN, h0, he⟩ := exists_coord_chg C (hU y) (gen_mem (hy y)) (fr y) (hT y) hτ p h₁ (g y p) (hg y p h₁)
      hW r h₃ s hr g' v hc
    exact ⟨M, N, ⟨rfl, cM⟩, ⟨rfl, cN⟩, h0, he⟩

end GlobalTheory.ShFam.HolFrames
