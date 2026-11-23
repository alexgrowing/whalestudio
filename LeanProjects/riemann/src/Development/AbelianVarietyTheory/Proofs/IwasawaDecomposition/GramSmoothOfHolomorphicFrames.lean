import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.TrueCx.TorHolo GlobalTheory.TrueCx.TorFrHolo
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open Filter Topology
open scoped ContDiff CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramFamily

section Pull

variable {K : Type} [CommRing K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {D : ℕ}

theorem contDiffOn_comp (R : AnRead p σ D) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (y : (Fin n → ℂ) → CxPts p σ) (hy : IsHolTo B fun b => (y b).1) (V : Y.Opens) (φ : CxPts p σ → ℝ)
    (hφ : R.SmoothOn (ptsIn p σ V) φ) :
    ContDiffOn ℝ ∞ (fun b => φ (y b)) {b ∈ B | y b ∈ ptsIn p σ V} := by
  have hOU : ∀ U : Y.Opens, IsOpen {b ∈ B | y b ∈ ptsIn p σ U} := fun U => (hy U 0).1
  have hdU : ∀ (U : Y.Opens) (f : Γ(Y, U)), DifferentiableOn ℂ (fun b => ev p σ U f (y b))
      {b ∈ B | y b ∈ ptsIn p σ U} := fun U f => (hy U f).2
  have hcont : ContinuousOn y B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · have := (hOU U).preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin n → ℂ) ∈ {b ∈ B | y b ∈ ptsIn p σ U} := ⟨v.2, hv⟩
      have hca := ((hdU U f).differentiableAt ((hOU U).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hOc : ∀ c : AlgChart p σ D, IsOpen {b ∈ B | y b ∈ c.e.source} := fun c =>
    hcont.isOpen_inter_preimage hB c.e.open_source
  have hdiff : ∀ c : AlgChart p σ D, DifferentiableOn ℂ (fun b => c.e (y b)) {b ∈ B | y b ∈ c.e.source} := fun c =>
    differentiableOn_euclidean.2 fun a => ((hdU c.U (c.x a)).mono
      fun v hv => ⟨hv.1, c.source_subset hv.2⟩).congr fun v hv => c.apply_eq _ hv.2 a
  intro b hb
  obtain ⟨i, hc⟩ := R.cover (y b)
  set c := R.chart i with hcdef
  have hb' : b ∈ {b ∈ B | y b ∈ c.e.source} := ⟨hb.1, hc⟩
  have h1 : ContDiffOn ℂ ∞ (fun b => c.e (y b)) {b ∈ B | y b ∈ c.e.source} :=
    GlobalTheory.SCV.contDiffOn_of_differentiableOn (hOc c) (hdiff c) ∞
  have hF : ContDiffAt ℝ ∞ (fun b => c.e (y b)) b := (h1.restrict_scalars ℝ).contDiffAt ((hOc c).mem_nhds hb')
  have hφc : ContDiffAt ℝ ∞ (φ ∘ c.e.symm) (c.e (y b)) :=
    (hφ.chart (isOpen_ptsIn _) c).contDiffAt ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn _)).mem_nhds
      (GlobalTheory.ChartGlue.mem_over c.e hc hb.2))
  refine ((hφc.comp b hF).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(hOc c).mem_nhds hb'] with w hw
  simp only [Function.comp_apply, c.e.left_inv hw.2]

end Pull

theorem form_sum₂ {M : Type} [AddCommGroup M] [Module ℂ M] (h : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) {J : Type} [Fintype J]
    (u : J → M) (c d : J → ℂ) : h (∑ a, c a • u a) (∑ a, d a • u a) =
      ∑ a, ∑ a', (c a * starRingEnd ℂ (d a')) * h (u a) (u a') := by
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  ring

section LocalBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}}

theorem exists_affine_basis (t : SAB H X) (f : Y ⟶ X) (y₀ : Y) :
    ∃ (V : Y.affineOpens) (n : ℕ) (v : Fin n → TanM (LogKS.chart V ≫ f) t.G), y₀ ∈ V.1 ∧ LocM.FrameBC.Full v := by
  have := t.semi.smooth
  have hs : Smooth ((Over.pullback f).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  obtain ⟨U, hU, hy, -, n, v₀, hb⟩ := exists_affine_lieBasis_baseChange Y ((Over.pullback f).obj t.G) y₀ ⊤ trivial
  have hp := isGrpPullback_pullback ((Over.pullback f).obj t.G) (spMap (RingHom.id Γ(Y, U)) ≫ hU.fromSpec)
  obtain ⟨v', -, hv'⟩ := hb Γ(Y, U) (RingHom.id _) _ _ hp
  have hc := IsGrpPullback.comp hp (isGrpPullback_pullback t.G f)
  have key : ∀ x : Sp Γ(Y, U) ⟶ X, x = (spMap (RingHom.id Γ(Y, U)) ≫ hU.fromSpec) ≫ f →
      ∃ v : Fin n → TanM x t.G, LocM.FrameBC.Full v := by
    rintro _ rfl
    have ht := fun i => (isTangent_iff hc (v' i)).1 (hv'.1 i)
    exact ⟨fun i => mkT _ (ht i), (LocM.FrameBC.full_iff hc fun _ => rfl).1 hv'⟩
  obtain ⟨v, hv⟩ := key (LogKS.chart ⟨U, hU⟩ ≫ f) (by
    rw [show spMap (RingHom.id Γ(Y, U)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    rfl)
  exact ⟨⟨U, hU⟩, n, v, hy, hv⟩

variable {K : Type} [CommRing K] {p : Y ⟶ Sp K} {σ : K →+* ℂ}

theorem full_valAt {t : SAB H X} {f : Y ⟶ X} {V : Y.affineOpens} {n : ℕ} {v : Fin n → TanM (LogKS.chart V ≫ f) t.G}
    (hv : LocM.FrameBC.Full v) {y : CxPts p σ} (hy : y ∈ ptsIn p σ V.1) :
    LocM.FrameBC.Full fun i => valAt f (v i) hy := by
  have key : ∀ (x' : Sp ℂ ⟶ X) (e : spMap (evHom hy) ≫ LogKS.chart V ≫ f = x'),
      LocM.FrameBC.Full fun i => tanOf (isTan_map (evHom hy) e (isTan_tv (v i))) := by
    rintro _ rfl
    exact LocM.FrameBC.full_bc _ hv
  exact key _ (by rw [← Category.assoc, spMap_evHom])

def basisOfFull {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {n : ℕ} {v : Fin n → TanM x t.G}
    (hv : LocM.FrameBC.Full v) : Module.Basis (Fin n) ℂ (TanM x t.G) :=
  Module.Basis.mk (v := v)
    (Fintype.linearIndependent_iff.2 fun a ha => congrFun ((hv 0).unique (y₁ := a) (y₂ := 0) ha.symm (by simp)))
    (fun w _ => by
      obtain ⟨a, ha, -⟩ := hv w
      exact ha ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i, rfl⟩))

end LocalBasis

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

def lieC (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] TanM ((cxPt Z y).1 ≫ genι Z) Z.t.G :=
  (pushE Z.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Z.m (ptC y) (Category.assoc _ _ _).symm)

def frB (y : FrPt Xo c (CAt σ)) :
    Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ℂ (TanM ((cxPt Z y).1 ≫ genι Z) Z.t.G) :=
  (Module.Basis.mk (R := ℂ) (v := frVec y)
    (Fintype.linearIndependent_iff.2 fun a ha => congrFun
      ((fullB_basis y 0).unique (y₁ := a) (y₂ := 0) ha.symm (by simp)))
    (fun w _ => by
      obtain ⟨a, ha, -⟩ := fullB_basis y w
      exact ha ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (show ℂ from a i)
        (Submodule.subset_span ⟨i, rfl⟩))).map (lieC Z y)

theorem frB_apply (y : FrPt Xo c (CAt σ)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    frB Z y ⟨τ, i⟩ = (cxFrame Z y).vec τ i := by
  exact (Module.Basis.map_apply _ _ _).trans ((congrArg _ (Module.Basis.mk_apply _ _ _)).trans (tan_ext rfl))

theorem isHolTo_cxPt {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  refine isHolTo_comp (isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_) Z.jQ
  simp only [ptC_fst]
  exact LocLift.isHolTo_congr h1 fun b _ => hx _

theorem exists_family {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    ∃ (g : ℕ) (q : Fin g ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))
      (Ft : (Fin n → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ft bz.1 bz.2) ∧
      ∀ b ∈ B, ∀ cf : Fin g → ℂ, IsDerivAt0 (Ft b) cf (tv (∑ i, cf i • frB Z (U.un k (x b)) (q i))).left := by
  classical
  have hpt := isHolTo_cxPt Z hU k hB x hd
  obtain ⟨-, -, -, -, -, g, q, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hxu hder _ using hun k
  have h1 := F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩
  have hc := Z.m0.toSABMap.cart.1
  have hw : ∀ b z, (F.ex (ik k) (P (x b)) z).left ≫ Xo.univ.t.G.hom =
      ptC (U.un k (x b)) ≫ pullback.fst _ _ := fun b z => by
    rw [ptC_fst, xC, hxu]
    exact Over.w (F.ex (ik k) (P (x b)) z)
  have hp : IsHolTo B fun b => ptC (U.un k (x b)) := by
    refine isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_
    simp only [ptC_fst]
    exact LocLift.isHolTo_congr h1.1 fun b _ => hxu _
  have h2 := isHolTo_lift hc hB (fun b z => (F.ex (ik k) (P (x b)) z).left) _ h1.2 hp hw
  refine ⟨g, q, fun b z => hc.lift _ _ (hw b z) ≫ Z.m.φ, isHolTo_comp h2 _, fun b hb cf => ?_⟩
  set y := U.un k (x b) with hy
  have hne : IsHolTo Set.univ fun z => (F.ex (ik k) (P (x b)) z).left :=
    LocLift.isHolTo_comp h1.2 isOpen_univ (β := fun z => (b, z)) (by fun_prop) fun _ _ => ⟨hb, trivial⟩
  have hT : ∀ (u : TanM (xC y) Xo.univ.t.G) (w : Fin g → ℂ),
      IsDerivAt0 (fun z => (F.ex (ik k) (P (x b)) z).left) w (tv u).left →
      IsDerivAt0 (fun z => hc.lift _ _ (hw b z) ≫ Z.m.φ) w
        (tv (lieC Z y u)).left := fun u w h => by
    set u' := (pushE Z.m0.toSABMap (ptC y) (ptC_fst y)).symm u with hu'
    have h3 : (tv u').left ≫ Z.m0.toSABMap.φ = (tv u).left := by
      rw [← left_pushE Z.m0.toSABMap (ptC y) (ptC_fst y), hu', LinearEquiv.apply_symm_apply]
    have h4 := isDerivAt0_of_cart hc (ptC y) (e := fun z => hc.lift _ _ (hw b z))
      (fun z => hc.lift_snd _ _ _) (by simpa only [IsPullback.lift_fst] using hne)
      (isTan_tv u').1 (by simpa only [IsPullback.lift_fst, h3] using h)
    exact isDerivAt0_comp_hom h4 Z.m.φ
  have hsum : ∑ i, cf i • frB Z y (q i) =
      lieC Z y (∑ i, cf i • frVec y (q i)) := by
    simp only [map_sum, map_smul, frB, Module.Basis.map_apply, Module.Basis.mk_apply]
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

theorem coord_holomorphic {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) (x : (Fin n → ℂ) → (U.X k).dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) (V : (gen Z).affineOpens)
    (v : TanM (LogKS.chart V ≫ genι Z) Z.t.G) (i : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g {b ∈ B | cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1} ∧
      ∀ b (hy : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1),
        g b = (frB Z (U.un k (x b))).repr (valAt (genι Z) v hy) i := by
  classical
  obtain ⟨g, q, Ft, hFt, hD⟩ := exists_family Z hU k hB x hd
  have hY : IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := isHolTo_cxPt Z hU k hB x hd
  let W : (Fin n → ℂ) → Fin g → ℂ := fun b =>
    if h : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1 then
      fun m => (frB Z (U.un k (x b))).repr (valAt (genι Z) v h) (q m) else 0
  set B' := {b ∈ B | ⊤ ≤ (cxPt Z (U.un k (x b))).1 ⁻¹ᵁ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  have hsum : ∀ b (hb : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1),
      ∑ m, W b m • frB Z (U.un k (x b)) (q m) = valAt (genι Z) v hb := fun b hb => by
    have h1 : W b = fun m => (frB Z (U.un k (x b))).repr (valAt (genι Z) v hb) (q m) := dif_pos hb
    rw [h1]
    exact (q.sum_comp fun a => (frB Z (U.un k (x b))).repr (valAt (genι Z) v hb) a •
      frB Z (U.un k (x b)) a).trans ((frB Z _).sum_repr _)
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hdiff : ∀ b₀ ∈ B', DifferentiableAt ℂ W b₀ := fun b₀ hb₀ => by
    have h₀ : cxPt Z (U.un k (x b₀)) ∈ ptsIn (genStr Z) σ V.1 := hb₀.2
    let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
      if h : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1 then evHom h else evHom h₀
    have hevb : ∀ b (h : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1), ev b = evHom h := fun b h => dif_pos h
    have hev : ∀ cc, DifferentiableAt ℂ (fun b => ev b cc) b₀ :=
      HolLieFrame.differentiableAt_ev (B := B') (LocLift.isHolTo_mono hY hB' fun b hb => hb.1) (LogKS.chart V) ev
        (fun b hb => by rw [hevb b hb.2]; exact (spMap_evHom hb.2).symm) hb₀
    have hder : ∀ b ∈ B', IsDerivAt0 (Ft b) (W b)
        (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (ev b)) ≫ (tv v).left) := fun b hb => by
      have h1 := hD b hb.1 (W b)
      rw [hsum b hb.2, hevb b hb.2] at *
      exact h1
    refine HolLieFrame.differentiableAt_of_forms W b₀ fun w hw => ?_
    have hw' : ∀ (O : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, O)), ⊤ ≤ Ft b₀ 0 ⁻¹ᵁ O →
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
    exact funext (Fintype.linearIndependent_iff.1 ((frB Z (U.un k (x b₀))).linearIndependent.comp q q.injective) w e3)
  refine ⟨fun b => W b (q.symm i), fun b hb =>
    ((differentiableAt_pi.1 (hdiff b hb) (q.symm i))).differentiableWithinAt, fun b hy => ?_⟩
  show (dite _ _ _ : Fin g → ℂ) (q.symm i) = _
  rw [dif_pos hy]
  simp

theorem met_family {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (Fin n → ℂ)} (hB : IsOpen B) (x : (Fin n → ℂ) → (U.X k).dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) {D : ℕ} (R : AnRead (genStr Z) σ D)
    (h : ∀ y : CxPts (genStr Z) σ, TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ)
    (hh : IsLieMetric Z.t (genι Z) R h) (i i' : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ContDiffOn ℝ ∞ (fun b => h (cxPt Z (U.un k (x b))) (frB Z (U.un k (x b)) i) (frB Z (U.un k (x b)) i')) B := by
  classical
  intro b₀ hb₀
  have hY := isHolTo_cxPt Z hU k hB x hd
  obtain ⟨V, n', v, hy₀, hv⟩ := exists_affine_basis Z.t (genι Z)
    ((cxPt Z (U.un k (x b₀))).1 (IsLocalRing.closedPoint ℂ))
  have hm₀ : cxPt Z (U.un k (x b₀)) ∈ ptsIn (genStr Z) σ V.1 := mem_ptsIn.2 hy₀
  set B' := {b ∈ B | cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1} with hB'def
  have hB' : IsOpen B' := (hY V.1 0).1
  have hb' : b₀ ∈ B' := ⟨hb₀, hm₀⟩
  let bs : ∀ b, cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1 → Module.Basis (Fin n') ℂ _ :=
    fun b hb => basisOfFull (full_valAt hv hb)
  let e : Fin n' ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) := (bs b₀ hm₀).indexEquiv (frB Z (U.un k (x b₀)))
  choose g hg hg' using fun (a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) =>
    coord_holomorphic Z hU k hB x hd V (v (e.symm a.2)) a.1
  let M : (Fin n → ℂ) → Matrix (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ℂ :=
    fun b => Matrix.of fun a a' => g (a, a') b
  have hbs : ∀ b hb a, (bs b hb).reindex e a = valAt (genι Z) (v (e.symm a)) hb := fun b hb a => by
    rw [Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  have hM : ∀ b (hb : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1),
      M b = (frB Z (U.un k (x b))).toMatrix ((bs b hb).reindex e) := fun b hb => by
    ext a a'
    rw [Module.Basis.toMatrix_apply, hbs]
    exact hg' (a, a') b hb
  have hinv : ∀ b (hb : cxPt Z (U.un k (x b)) ∈ ptsIn (genStr Z) σ V.1),
      (M b)⁻¹ = ((bs b hb).reindex e).toMatrix (frB Z (U.un k (x b))) := fun b hb => by
    rw [hM b hb]
    exact Matrix.inv_eq_right_inv (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  have hdet : ∀ b ∈ B', (M b).det ≠ 0 := fun b hb => by
    have h1 : M b * ((bs b hb.2).reindex e).toMatrix (frB Z (U.un k (x b))) = 1 := by
      rw [hM b hb.2]
      exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ h1)).ne_zero
  have hCd : ∀ a a', DifferentiableOn ℂ (fun b => (M b)⁻¹ a a') B' :=
    GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv M B' (fun a a' => hg (a, a')) hdet
  have hCs : ∀ a a', ContDiffOn ℝ ∞ (fun b => (M b)⁻¹ a a') B' := fun a a' =>
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn hB' (hCd a a') ∞).restrict_scalars ℝ
  have hCc : ∀ a a', ContDiffOn ℝ ∞ (fun b => starRingEnd ℂ ((M b)⁻¹ a a')) B' := fun a a' =>
    Complex.conjCLE.contDiff.comp_contDiffOn (hCs a a')
  choose G hG1 hG2 hG3 using fun (a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) =>
    hh.2 V (v (e.symm a.1)) (v (e.symm a.2))
  have hGs : ∀ a, ContDiffOn ℝ ∞ (fun b => G a (cxPt Z (U.un k (x b)))) B' := fun a => by
    have h1 := contDiffOn_comp R hB _ hY V.1 _ (hG1 a)
    have h2 := contDiffOn_comp R hB _ hY V.1 _ (hG2 a)
    refine ((Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul (contDiffOn_const (c := Complex.I)))).congr fun b _ => ?_
    simp [Complex.re_add_im]
  have hsum : ContDiffOn ℝ ∞ (fun b => ∑ a, ∑ a', ((M b)⁻¹ a i * starRingEnd ℂ ((M b)⁻¹ a' i')) *
      G (a, a') (cxPt Z (U.un k (x b)))) B' :=
    ContDiffOn.sum fun a _ => ContDiffOn.sum fun a' _ => ((hCs a i).mul (hCc a' i')).mul (hGs _)
  have heq : ∀ b ∈ B', h (cxPt Z (U.un k (x b))) (frB Z (U.un k (x b)) i) (frB Z (U.un k (x b)) i') =
      ∑ a, ∑ a', ((M b)⁻¹ a i * starRingEnd ℂ ((M b)⁻¹ a' i')) * G (a, a') (cxPt Z (U.un k (x b))) := fun b hb => by
    have hrep : ∀ w, frB Z (U.un k (x b)) w = ∑ a, (M b)⁻¹ a w • valAt (genι Z) (v (e.symm a)) hb.2 := fun w => by
      conv_lhs => rw [← ((bs b hb.2).reindex e).sum_repr (frB Z (U.un k (x b)) w)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hinv b hb.2, Module.Basis.toMatrix_apply, hbs]
    rw [hrep i, hrep i', form_sum₂]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [hG3 (a, a') _ hb.2]
  exact (((hsum.congr heq).contDiffAt (hB'.mem_nhds hb')).contDiffWithinAt)

theorem gram_family [SmoothOfRelativeDimension Dw.dim (genStr Z)] (A : OddPrimesWithRootsOfUnity Z) {U : Formalism.L2.PjFree.Unf Xo c σ r}
    (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B)
    (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)) :
    ContDiffOn ℝ ∞ (fun v => A.gram (cxPt Z (U.un k (x v))) (cxFrame Z (U.un k (x v))) τ a b) B := by
  refine (met_family Z hU k hB x hd (manifold Z σ) (A.met σ) (A.met_smooth σ) ⟨τ, b⟩ ⟨τ, a⟩).congr fun v _ => ?_
  rw [frB_apply, frB_apply]
  rfl

end Family

theorem gram_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (m : ℕ) (B : Set (Fin m → ℂ)) (f : (Fin m → ℂ) → (s.fd k).dom), IsOpen B → (∀ τ a b, DifferentiableOn ℂ (fun v => ReciprocityTheory.ChartRestriction.G.FD.mat (f v).1 τ a b) B) → ∀ τ a b, ContDiffOn ℝ ∞ (fun v => x.gram (s.framePt k (f v)) (s.lieFrame k (f v)) τ a b) B := by
  intro D A N j S κ s L k x m B f hB hd τ a b
  exact gram_family s.T.Z x s.isUnf k hB f hd τ a b

end GlobalTheory.GramFamily
