import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueAtPolarizedFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartAppLEEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanBasisPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpMulTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMap
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.LocRegCmp
open GlobalTheory.FlagMod (ev)

theorem leibniz_ext_of_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) {C : Type} [CommRing C]
    (ψ : Γ(X, W.1) →+* C) (d : C → C) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ Γ(X, W.1) Γ(X, W.1))
    (h : ∀ r, d (ψ ((X.presheaf.map (homOfLE hW).op).hom r)) = ψ (D ((X.presheaf.map (homOfLE hW).op).hom r)))
    (b : Γ(X, W.1)) : d (ψ b) = ψ (D b) := by
  have d0 : d 0 = 0 := by simpa using hadd 0 0
  have d1 : d 1 = 0 := by simpa using hd 1 1
  let g₁ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (d (ψ r))
      map_one' := by ext <;> simp [d1]
      map_zero' := by ext <;> simp [d0]
      map_add' := fun a b => by ext <;> simp [hadd]
      map_mul' := fun a b => by ext <;> simp [hd, mul_comm] }
  let g₂ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (ψ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, mul_comm] }
  have e : g₁.comp (X.presheaf.map (homOfLE hW).op).hom = g₂.comp (X.presheaf.map (homOfLE hW).op).hom := by
    refine RingHom.ext fun r => ?_
    ext
    · simp [g₁, g₂]
    · simpa [g₁, g₂] using h r
  have : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e2 : spMap g₁ ≫ chart W = spMap g₂ ≫ chart W := by
    rw [← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp',
      GlobalTheory.LogKSLoc.spMap_comp', e]
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 ((cancel_mono (chart W)).1 e2))
  have e4 : g₁ b = g₂ b := congrArg (fun k => k b) e3
  simpa [g₁, g₂] using congrArg TrivSqZeroExt.snd e4

theorem isKS_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))
    (hD : ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r))
    (hKS : IsKS t V U v D Θ) :
    IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW
      ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  obtain ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    refine leibniz_ext_of_res U W hW _ _ ((hfld i).1 _ inf_le_left) ((hfld i).2.1 _ inf_le_left) DW (fun r => ?_) b
    rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']

theorem ks_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm U W hW n v hv hb D DW Θ hDW hKS k _ _ m d ξ hx t φ hEt hbd vR hvR hvRφ D' hD' ΘR hKSR h hh hρh a b s N hs
  let ι0 : ChartRing k m d →+* FractionRing (ChartRing k m d) := algebraMap _ _
  let g : Sp (ChartRing k m d) ⟶ Y.X := ξ ≫ genι Y
  have hι0 : Function.Injective ι0 := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_ringHom (f := ι0.comp (algebraMap k (ChartRing k m d))) (hι0.comp (algebraMap k _).injective)
  obtain ⟨hg, hgρ⟩ := GlobalTheory.LocReg.chart_appLE_eq E H Dw l Xo c Y U k m d ξ hx
  have eR : ∀ x : ChartRing k m d, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv_hom_id_apply x
  have hgx : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r) =
      GlobalTheory.LocReg.chartHom Y U ξ hx r := by
    intro r; rw [hgρ]; exact eR _
  obtain ⟨hUW, D'', hDtop, hDW'⟩ := GlobalTheory.LocReg.deriv_ext_basicOpen Y.X U W (hW.le.trans inf_le_left) D.1 DW hDW h hh _ g hg D'
    (fun r => by rw [hgx, hgx]; exact hD' r)
  let U' : (Sp (ChartRing k m d)).affineOpens :=
    (Sp (ChartRing k m d)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)
  have hU'U : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (g.preimage_mono (hW.le.trans inf_le_left))
  let v' : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), U'.1)) ⟶ t.G.left) := fun i =>
    spMap (dualMap ((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom) ≫ vR i
  have hv' : ∀ i, IsTanAtG t (chart U') (v' i) := fun i =>
    GlobalTheory.KSAgree.tan_res E H _ t ⟨⊤, isAffineOpen_top _⟩ U' le_top (vR i) (hvR i)
  have hcompU : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU'U).hom) ≫ v i := by
    intro i
    show (spMap _ ≫ vR i) ≫ φ.φ = _
    rw [Category.assoc, hvRφ i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap, ← hgρ,
      ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have hcompW : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE W.1 U'.1 hUW).hom) ≫
      (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) := by
    intro i
    rw [hcompU i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  let V' : (Sp (ChartRing k m d)).Opens := (Sp (ChartRing k m d)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))
  have hUV' : U'.1 ⊓ V' ≤ g ⁻¹ᵁ interior Y := by
    intro p hp
    have hp2 : p ∈ V' := hp.2
    have hnp : ∏ i, bdParam k m d i ∉ p.asIdeal := by
      have := hp2
      simp only [V'] at this
      rw [basicOpen_eq_of_affine] at this
      exact this
    have hnb : ξ p ∉ genBd Y := fun h' => hnp ((hbd p).1 h')
    obtain ⟨y, hy⟩ : ξ p ∈ Set.range Y.jQ := by
      by_contra h'
      exact hnb (mem_genBd.2 h')
    show g p ∈ (interior Y : Set Y.X)
    rw [GlobalTheory.LogKS.interior, Scheme.Hom.coe_opensRange]
    refine ⟨y, ?_⟩
    show (Y.jQ ≫ pullback.fst _ _) y = (ξ ≫ genι Y) p
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
  have hprod : ∏ i, bdParam k m d i ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  let x0 : Sp (FractionRing (ChartRing k m d)) ⟶ Y.X := spMap ι0 ≫ g
  have hevtop : ∀ (hK : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens)) r,
      ev (spMap ι0) ⊤ hK r = ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r) := by
    intro hK r
    unfold ev
    have : (spMap ι0).appLE ⊤ ⊤ hK = (spMap ι0).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, Scheme.ΓSpecIso_naturality]
    rfl
  have hx0U : ⊤ ≤ x0 ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp (spMap ι0) hg
  have hevU : ∀ r, ev x0 U.1 hx0U r = ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx r) := by
    intro r
    rw [GlobalTheory.FlagMod.ev_spMap ι0 g U.1 hg hx0U]
    show ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = _
    rw [hgx]
  have htop : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens) := fun _ _ => trivial
  have hx0h : ⊤ ≤ x0 ⁻¹ᵁ Y.X.basicOpen h := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev x0 U.1 hx0U h
      (by rw [hevU]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hx0W : ⊤ ≤ x0 ⁻¹ᵁ W.1 := fun p hp => hh (hx0h hp)
  have hKU' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ U'.1 := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop ((g.appLE U.1 ⊤ hg).hom h)
      (by rw [hevtop, hgx]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hKV' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ V' := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop _
      (by rw [hevtop, eR]; exact ((map_ne_zero_iff ι0 hι0).2 hprod).isUnit) p
  have hint : ⊤ ≤ x0 ⁻¹ᵁ interior Y := fun p hp => hUV' ⟨hKU' hp, hKV' hp⟩
  obtain ⟨P₀, θ0, hpb, hiso⟩ := GlobalTheory.KSUniq.exists_polAV_interior Y x0 hint
  obtain ⟨mm, hmm, hiso'⟩ := GlobalTheory.PolAVPull.polAV_pull E H Y.X _ Y.t t g φ _ (spMap ι0) P₀ θ0 hpb hiso
  let φK := ev (spMap ι0) U'.1 hKU'
  have hpt : spMap φK ≫ chart U' = spMap ι0 := GlobalTheory.FlagMod.spMap_ev (spMap ι0) U'.2 hKU'
  have hvW : ∀ i, IsTanAtG Y.t (chart W) (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) :=
    fun i => GlobalTheory.KSAgree.tan_res E H Y.X Y.t U W _ (v i) (hv i)
  have hks1 := GlobalTheory.KSBaseChange.isKS_pull E H Y.X _ Y.t t g φ (interior Y) V' W U' hUW hUV' n _ v' hvW hv' hcompW DW D'' hDW' Θ hKS
  have hks2 := isKS_restrict t V' ⟨⊤, isAffineOpen_top _⟩ U' le_top vR _ D'' ΘR hDtop hKSR
  have hb' := GlobalTheory.BasisPull.tanBasis_pull E H Y.X _ Y.t t g φ U U' hU'U n v v' hv hb hv' hcompU
  have huniq := GlobalTheory.KSPtUniq.isKS_unique_at_point E H _ t V' U' n v' hv' hb' _ φK P₀ mm
    (by rw [hpt]; exact hKV') (by rw [hpt]; exact hmm) hiso' _ _ _ hks1 hks2
  have hab := congrFun (congrFun huniq a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  have e1 : φK ((g.appLE W.1 U'.1 hUW).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_appLE (spMap ι0) g hUW hKU' hx0W (Θ a b)
  have e2 : φK (((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom (ΘR a b)) =
      ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b)) :=
    (GlobalTheory.FlagMod.ev_res (spMap ι0) le_top hKU' htop (ΘR a b)).trans (hevtop _ _)
  have r1 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx s) :=
    (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U s).trans (hevU s)
  have r2 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N)) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx h) ^ N := by
    rw [← map_pow, ← map_pow]
    exact (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U (h ^ N)).trans (hevU _)
  have r3 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_res x0 hh hx0h hx0W _
  have hsx := congrArg (ev x0 (Y.X.basicOpen h) hx0h) hs
  rw [map_mul, r1, r2, r3, ← e1, hab, e2] at hsx
  apply hι0
  rw [map_mul, map_pow]
  exact hsx

end GlobalTheory.LocRegCmp
