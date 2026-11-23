import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorFrHolo

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)

theorem isDerivAt0_of_cart {g : ℕ} {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) (pt : Sp ℂ ⟶ X') {e : (Fin g → ℂ) → (Sp ℂ ⟶ G')} (he : ∀ z, e z ≫ h' = pt)
    (hol : IsHolTo Set.univ fun z => e z ≫ φ) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'}
    (hv : v ≫ h' = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ pt) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  have H := (IsPullback.of_hasPullback h' pt).paste_horiz hc
  have key := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp]))
    (fun z => pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hol)
    (v := pullback.lift v _ hv) (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using isDerivAt0_comp_hom key (pullback.fst h' pt)

theorem isHolTo_lift {G' G X' X : Scheme.{0}} {φ : G' ⟶ G} {h' : G' ⟶ X'} {h : G ⟶ X} {f : X' ⟶ X}
    (hc : IsPullback φ h' h f) {n g : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (a : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X'))
    (ha : IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => a bz.1 bz.2) (hp : IsHolTo B p)
    (w : ∀ b z, a b z ≫ h = p b ≫ f) :
    IsHolTo (B ×ˢ Set.univ) fun bz : (Fin n → ℂ) × (Fin g → ℂ) => hc.lift (a bz.1 bz.2) (p bz.1) (w _ _) := by
  let L : (Fin (n + g) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin g → ℂ) :=
    ((LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin g) ℂ ℂ)).toContinuousLinearEquiv
  have hC : IsOpen (L ⁻¹' (B ×ˢ Set.univ)) := (hB.prod isOpen_univ).preimage L.continuous
  have h1 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => a (L c).1 (L c).2 :=
    LocLift.isHolTo_comp ha hC L.differentiableOn fun _ h => h
  have h2 : IsHolTo (L ⁻¹' (B ×ˢ Set.univ)) fun c => p (L c).1 :=
    LocLift.isHolTo_comp hp hC (β := fun c => (L c).1) (by fun_prop) fun _ h => h.1
  have h3 := holPair _ _ _ h f _ _ _ _ (fun c => w (L c).1 (L c).2) hC h1 h2
  have h4 := isHolTo_comp h3 hc.isoPullback.inv
  have key : ∀ c, pullback.lift (a (L c).1 (L c).2) (p (L c).1) (w _ _) ≫ hc.isoPullback.inv =
      hc.lift _ _ (w (L c).1 (L c).2) := fun c => hc.hom_ext
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.lift_fst]
      exact pullback.lift_fst _ _ _)
    (by
      simp only [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.lift_snd]
      exact pullback.lift_snd _ _ _)
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h4 ((hB.prod isOpen_univ)) (β := L.symm)
    L.symm.differentiableOn fun q hq => by simpa using hq) fun q _ => ?_
  refine Eq.trans ?_ (key (L.symm q)).symm
  simp only [L.apply_symm_apply]

section Family

open GlobalTheory.TrueCx.TorHolo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

theorem exists_family (hU : IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    ∃ (g : ℕ) (q : Fin g ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))
      (Ft : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ft bz.1 bz.2) ∧
      ∀ b ∈ B, ∀ cf : Fin g → ℂ, IsDerivAt0 (Ft b) cf (tv (∑ i, cf i • torBasis Y (U.un k (x b)) (q i))).left := by
  classical
  obtain ⟨-, -, -, -, -, g, q, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hxu hder _ using hun k
  have h1 := F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩
  have hc := Y.m0.toSABMap.cart.1
  have hw : ∀ b z, (F.ex (ik k) (P (x b)) z).left ≫ Xo.univ.t.G.hom =
      ptC (U.un k (x b)) ≫ pullback.fst _ _ := fun b z => by
    rw [ptC_fst, xC, hxu]
    exact Over.w (F.ex (ik k) (P (x b)) z)
  have hp : IsHolTo B fun b => ptC (U.un k (x b)) := by
    refine isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_
    simp only [ptC_fst]
    exact LocLift.isHolTo_congr h1.1 fun b _ => hxu _
  have h2 := isHolTo_lift hc hB (fun b z => (F.ex (ik k) (P (x b)) z).left) _ h1.2 hp hw
  refine ⟨g, q, fun b z => hc.lift _ _ (hw b z) ≫ Y.m.φ, isHolTo_comp h2 _, fun b hb cf => ?_⟩
  set y := U.un k (x b) with hy
  have hne : IsHolTo Set.univ fun z => (F.ex (ik k) (P (x b)) z).left :=
    LocLift.isHolTo_comp h1.2 isOpen_univ (β := fun z => (b, z)) (by fun_prop) fun _ _ => ⟨hb, trivial⟩
  have hT : ∀ (u : TanM (xC y) Xo.univ.t.G) (w : Fin g → ℂ),
      IsDerivAt0 (fun z => (F.ex (ik k) (P (x b)) z).left) w (tv u).left →
      IsDerivAt0 (fun z => hc.lift _ _ (hw b z) ≫ Y.m.φ) w (tv (lieEquiv Y y u)).left := fun u w h => by
    set u' := (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm u with hu'
    have h3 : (tv u').left ≫ Y.m0.toSABMap.φ = (tv u).left := by
      rw [← left_pushE Y.m0.toSABMap (ptC y) (ptC_fst y), hu', LinearEquiv.apply_symm_apply]
    have h4 := isDerivAt0_of_cart hc (ptC y) (e := fun z => hc.lift _ _ (hw b z))
      (fun z => hc.lift_snd _ _ _) (by simpa only [IsPullback.lift_fst] using hne)
      (isTan_tv u').1 (by simpa only [IsPullback.lift_fst, h3] using h)
    exact isDerivAt0_comp_hom h4 Y.m.φ
  have hsum : ∑ i, cf i • torBasis Y y (q i) = lieEquiv Y y (∑ i, cf i • frVec y (q i)) := by
    simp only [map_sum, map_smul, torBasis, Module.Basis.map_apply, Module.Basis.mk_apply]
  rw [hsum]
  refine hT _ _ ?_
  have e0 : (F.ex (ik k) (P (x b)) 0).left = (1 : Over.mk (xC y) ⟶ Xo.univ.t.G).left := by
    have key : ∀ {a b' : Sp ℂ ⟶ Xo.X} (_ : a = b'), (1 : Over.mk a ⟶ Xo.univ.t.G).left =
        (1 : Over.mk b' ⟶ Xo.univ.t.G).left := by
      rintro _ _ rfl
      rfl
    rw [(F.ex_ker _ _ (hP' _) 0).2 (zero_mem _)]
    exact key (hxu _).symm
  have h5 := ShFam.Hor.ExpDirs.isDerivAt0_of_comb (t := Xo.univ.t) (x := xC y) e0
    (v := fun i => (tv (frVec y (q i))).left) (w := fun i => Pi.single i 1) (fun i => isTan_tv _)
    (fun i => by
      have h := hder (x b) (q i).1 (q i).2
      rw [Sigma.eta, Equiv.symm_apply_apply] at h
      exact h) (a := cf) (isTan_tv _) ((isComb_iff (fun i => frVec y (q i)) cf _).2 rfl)
  have h6 : ∑ i, cf i • (Pi.single i 1 : Fin g → ℂ) = cf := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [h6] at h5

end Family

theorem coord_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ) (r j : ℕ) (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (Tau : Type) [Fintype Tau] (T : Tau ≃ Psi H) (k : U.Comp) (V : (torC Y σ).affineOpens) (v : TanM (LogKS.chart V ≫ torPr Y σ) Y.t.G) (i : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ∃ g : Pt Tau j (r - j) → ℂ, ∀ z ∈ DomI Tau j (r - j), ∀ hy : domTor Y U hU e T k z ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1, DifferentiableAt ℂ (fun w => g (unflat w)) (flat z) ∧ g z = (torBasis Y (domFr U hU e T k z)).repr (valAt (torPr Y σ) v hy) i := by
  intro E _ _ _ H Dw l Xo c Y σ r j U hU e hσ Tau _ T k V v i
  classical
  let L : (Tau × Fin j × Fin (r - j) → ℂ) ≃L[ℂ] (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat Tau j (r - j)) := ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) := L.symm ⁻¹' DomFlat Tau j (r - j) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) (first_index_eq_of_unfolded U hU e k) (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B := fun τ a c =>
    ((TorHolo.differentiable_stdMat (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  obtain ⟨g, q, Ft, hFt, hD⟩ := exists_family Y hU k hB x hd
  have hY : IsHolTo B fun b => (domTor Y U hU e T k (unflat (L.symm b))).1 := TorHolo.isHolTo_torPt Y hU k hB x hd
  let Wz : Pt Tau j (r - j) → Fin g → ℂ := fun z =>
    if h : domTor Y U hU e T k z ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 then
      fun m => (torBasis Y (domFr U hU e T k z)).repr (valAt (torPr Y σ) v h) (q m) else 0
  set W : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → Fin g → ℂ := fun b => Wz (unflat (L.symm b)) with hWdef
  set B' := {b ∈ B | ⊤ ≤ (domTor Y U hU e T k (unflat (L.symm b))).1 ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  have hsum : ∀ b (hb : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1),
      ∑ m, W b m • torBasis Y (U.un k (x b)) (q m) = valAt (torPr Y σ) v hb := fun b hb => by
    have h1 : W b = fun m => (torBasis Y (domFr U hU e T k (unflat (L.symm b)))).repr (valAt (torPr Y σ) v hb) (q m) :=
      dif_pos hb
    rw [h1]
    exact (q.sum_comp fun a => (torBasis Y (domFr U hU e T k (unflat (L.symm b)))).repr (valAt (torPr Y σ) v hb) a •
      torBasis Y (domFr U hU e T k (unflat (L.symm b))) a).trans ((torBasis Y _).sum_repr _)
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : domTor Y U hU e T k (unflat (L.symm b₀)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 := hb₀.2
    let ev : (Fin (Fintype.card (Tau × Fin j × Fin (r - j))) → ℂ) → (Γ(torC Y σ, V.1) →+* ℂ) := fun b =>
      if h : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1 then evHom h else evHom h₀
    have hevb : ∀ b (h : domTor Y U hU e T k (unflat (L.symm b)) ∈ ptsIn (torStr Y σ) (RingHom.id ℂ) V.1),
        ev b = evHom h := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom hb.2).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (Ft b) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ (tv v).left) := fun b hb => by
      have h1 := hD b hb.1 (W b)
      rw [hsum b hb.2, hevb b hb.2] at *
      exact h1
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, O)), ⊤ ≤ Ft b₀ 0 ⁻¹ᵁ O →
        fderiv ℂ (fun z => valAt' (Ft b₀ z) O f) 0 w = 0 := by
      intro O f hO
      refine hw (fun b => fderiv ℂ (fun z => valAt' (Ft b z) O f) 0)
        (HolLieFrame.differentiableAt_fderiv (e := Ft) hFt hb₀.1 O f hO) ?_
      obtain ⟨Fn, hF, hF'⟩ := HolLieFrame.exists_hol_snd (tv v).left ev b₀ hev O f
        ((TangentOrigin.top_le_preimage_iff _ O).2 (by rw [(hder b₀ hb₀).1]; exact hO))
      refine hF.congr_of_eventuallyEq ?_
      filter_upwards [hF', hB'.mem_nhds hb₀] with b ⟨h, e'⟩ hb
      exact ((hder b hb).2 O h f).symm.trans e'
    have d₁ := LocalLift.isDerivAt0_const (Ft b₀) w hw'
    have d₀ := LocalLift.isDerivAt0_const (Ft b₀) 0 fun _ _ _ => map_zero _
    have e3 := tan_ext ((isDerivAt0_unique (hD b₀ hb₀.1 w) d₁).trans (isDerivAt0_unique (hD b₀ hb₀.1 0) d₀).symm)
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e3
    exact funext (Fintype.linearIndependent_iff.1 ((torBasis Y (U.un k (x b₀))).linearIndependent.comp q q.injective) w e3)
  refine ⟨fun z => Wz z (q.symm i), fun z hz hy => ⟨?_, ?_⟩⟩
  · have e1 : L.symm (L (flat z)) = flat z := L.symm_apply_apply _
    have hb : L (flat z) ∈ B' := by
      refine ⟨?_, ?_⟩
      · show L.symm (L (flat z)) ∈ DomFlat Tau j (r - j)
        rw [e1]
        exact hz
      · rw [e1]
        exact hy
    have h1 := (differentiableAt_pi.1 (hdiff _ hb) (q.symm i)).comp (flat z) L.differentiableAt
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    simp [hWdef]
  · show (dite _ _ _ : Fin g → ℂ) (q.symm i) = _
    rw [dif_pos hy]
    simp

end GlobalTheory.TrueCx.TorFrHolo
