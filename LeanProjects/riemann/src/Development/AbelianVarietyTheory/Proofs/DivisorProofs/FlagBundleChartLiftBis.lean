import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CellChart (algX_eq map_mem ev_appLE cellPt cellPt_mem map_cellPt ev_n_cellPt cellPt_self cellPt_congr)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCellDim

open MvPolynomial in

theorem etale_eval₂Hom_sum {k A R M N J : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : M → A)
    (f : A →+* R) (n : N → R) (e : J ≃ M ⊕ N) (hg : (eval₂Hom α t).Etale)
    (hΦ : Function.Bijective (eval₂Hom f n)) :
    (eval₂Hom (f.comp α) (fun j => Sum.elim (fun a => f (t a)) n (e j))).Etale := by
  let ι : MvPolynomial J k →+* MvPolynomial N (MvPolynomial M k) :=
    eval₂Hom (C.comp C) (fun j => Sum.elim (fun a => C (X a)) X (e j))
  let κ : MvPolynomial N (MvPolynomial M k) →+* MvPolynomial J k :=
    eval₂Hom (eval₂Hom C (fun a => X (e.symm (.inl a)))) (fun i => X (e.symm (.inr i)))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j; simp [ι, κ]
    · intro j
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : eval₂Hom (f.comp α) (fun j => Sum.elim (fun a => f (t a)) n (e j)) =
      (eval₂Hom f n).comp ((MvPolynomial.map (eval₂Hom α t)).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι)
      (GlobalTheory.etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

theorem exists_chart_le {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} {σ : k →+* ℂ} {n : ℕ}
    (c₀ : AlgChart q σ n) {y : CxPts q σ} (hy : y ∈ c₀.e.source) (U : B.Opens) (hV : y ∈ ptsIn q σ U) :
    ∃ c : AlgChart q σ n, y ∈ c.e.source ∧ c.U ≤ U := by
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hV⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a))).Etale := by
    have e : MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a)) =
        (resG B hle).comp (MvPolynomial.eval₂Hom (algX q c₀.U) c₀.x) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG B hle).Etale := by
      letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
      haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ c₀.etale hR
  obtain ⟨c, hc, hU, -⟩ := AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)
  exact ⟨c, hc, hU ▸ hfV⟩

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {m r D : ℕ} (e : Fin D ≃ Fin m ⊕ Low r)

theorem differentiable_base : Differentiable ℂ (base e) := by
  refine differentiable_euclidean.2 fun i => ?_
  simp only [base]
  fun_prop

variable (c : AlgChart q σ m) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (n : Low r → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n))
  (y₀ : CxPts p σ)

def inv (v : V D) : CxPts p σ :=
  if h : base e v ∈ c.e.target then
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fib e v)
  else y₀

variable {e c hW hWa n hΦ}

theorem inv_eq {v : V D} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v =
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fib e v) := dif_pos h

theorem inv_mem {v : V D} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v ∈ ptsIn p σ W := by
  rw [inv_eq _ _ _ h]; exact cellPt_mem ..

theorem map_inv {v : V D} (h : base e v ∈ c.e.target) :
    PtsOver.map π w (spMap σ) (inv π w e c hW hWa n hΦ y₀ v) = c.e.symm (base e v) := by
  rw [inv_eq _ _ _ h]; exact map_cellPt _ _ _ _ _ _ c.affine _ _

theorem ev_n_inv {v : V D} (h : base e v ∈ c.e.target) (s : Low r) :
    ev p σ W (n s) (inv π w e c hW hWa n hΦ y₀ v) = fib e v s := by
  rw [inv_eq _ _ _ h]; exact ev_n_cellPt ..

theorem ev_appLE_inv {v : V D} (h : base e v ∈ c.e.target) (g : Γ(B, c.U)) :
    ev p σ W ((π.appLE c.U W hW).hom g) (inv π w e c hW hWa n hΦ y₀ v) = ev q σ c.U g (c.e.symm (base e v)) := by
  rw [ev_appLE π w hW (inv_mem π w y₀ h), map_inv π w y₀ h]

theorem holo_inv (g : Γ(Y, W)) :
    DifferentiableOn ℂ (fun v => ev p σ W g (inv π w e c hW hWa n hΦ y₀ v)) {v | base e v ∈ c.e.target} := by
  obtain ⟨P, rfl⟩ := hΦ.2 g
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hd : DifferentiableOn ℂ (fun v => ev q σ c.U a (c.e.symm (base e v))) {v | base e v ∈ c.e.target} :=
      (c.holo c.U a).comp (differentiable_base e).differentiableOn fun v hv =>
        ⟨hv, c.source_subset (c.e.map_target hv)⟩
    refine hd.congr fun v hv => ?_
    simp only [MvPolynomial.eval₂Hom_C]
    exact ev_appLE_inv π w y₀ hv a
  | add P Q hP hQ =>
    simp only [map_add, ev_add]
    exact hP.add hQ
  | mul_X P s hP =>
    have hd : DifferentiableOn ℂ (fun v : V D => v (e.symm (.inr s))) {v | base e v ∈ c.e.target} := by
      fun_prop
    simp only [map_mul, ev_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hd.congr fun v hv => ev_n_inv π w y₀ hv s)

variable (e c hW hWa n hΦ)

def toF (y : CxPts p σ) : V D :=
  pt e (c.e (PtsOver.map π w (spMap σ) y)) fun s => ev p σ W (n s) y

def chart : OpenPartialHomeomorph (CxPts p σ) (V D) where
  toFun := toF π w e c n
  invFun := inv π w e c hW hWa n hΦ y₀
  source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
  target := {v | base e v ∈ c.e.target}
  map_source' y hy := by
    show base e (toF π w e c n y) ∈ c.e.target
    rw [toF, base_pt]
    exact c.e.map_source hy.1
  map_target' v hv :=
    ⟨by rw [Set.mem_preimage, map_inv π w y₀ hv]; exact c.e.map_target hv, inv_mem π w y₀ hv⟩
  left_inv' y hy := by
    have hb : base e (toF π w e c n y) ∈ c.e.target := by
      rw [toF, base_pt]; exact c.e.map_source hy.1
    rw [inv_eq π w y₀ hb]
    refine (cellPt_congr π w hW hWa n hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa n hΦ hy.2)
    · rw [toF, base_pt, c.e.left_inv hy.1]
    · rw [toF, fib_pt]
  right_inv' v hv := by
    ext j
    simp only [toF, pt]
    rcases h : e j with a | s
    · have hj : e.symm (.inl a) = j := by rw [← h, Equiv.symm_apply_apply]
      simp only [Sum.elim_inl]
      rw [map_inv π w y₀ hv, c.e.right_inv hv]
      simp [base, hj]
    · simp only [Sum.elim_inr]
      rw [ev_n_inv π w y₀ hv, fib, ← h, Equiv.symm_apply_apply]
  open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)
  open_target := c.e.open_target.preimage (differentiable_base e).continuous
  continuousOn_toFun := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
    rcases h : e j with a | s
    · simp only [h, Sum.elim_inl]
      exact (PiLp.continuous_apply 2 _ a).comp_continuousOn
        (c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1)
    · simp only [h, Sum.elim_inr]
      exact (continuousOn_ev (n s)).mono Set.inter_subset_right
  continuousOn_invFun := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base e).continuous)
    (fun v hv => inv_mem π w y₀ hv) fun g => holo_inv π w y₀ g).1

def cellChart : AlgChart p σ D where
  e := chart π w e c hW hWa n hΦ y₀
  U := W
  affine := hWa
  x j := Sum.elim (fun a => (π.appLE c.U W hW).hom (c.x a)) n (e j)
  etale := by
    have h := etale_eval₂Hom_sum (algX q c.U) c.x (π.appLE c.U W hW).hom n e c.etale hΦ
    rwa [algX_eq π w hW] at h
  source_subset := Set.inter_subset_right
  apply_eq y hy j := by
    show toF π w e c n y j = _
    simp only [toF, pt]
    rcases h : e j with a | s
    · simp only [Sum.elim_inl]
      rw [c.apply_eq _ hy.1 a, ev_appLE π w hW hy.2]
    · rfl
  holo W' f := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base e).continuous)
    (fun v hv => inv_mem π w y₀ hv) fun g => holo_inv π w y₀ g).2 W' f

include hWa hΦ in

theorem exists_cell (hne : c.e.source.Nonempty) : ∃ c' : AlgChart p σ D, IsCell e π w c c' ∧
    c'.e.source ⊆ ptsIn p σ W ∧ ∀ y ∈ c'.e.source, ∀ s, fib e (c'.e y) s = ev p σ W (n s) y := by
  obtain ⟨b₀, hb₀⟩ := hne
  refine ⟨cellChart π w e c hW hWa n hΦ (cellPt π w hW hWa n hΦ (c.source_subset hb₀) 0),
    ⟨rfl, rfl, fun y _ => ?_⟩, Set.inter_subset_right, fun y _ s => ?_⟩
  · exact base_pt e (c.e (PtsOver.map π w (spMap σ) y)) fun s => ev p σ W (n s) y
  · exact congrFun (fib_pt e (c.e (PtsOver.map π w (spMap σ) y)) fun s => ev p σ W (n s) y) s

end Chart

open GlobalTheory.FlagCell in

theorem exists_adapted_gram {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
    (w : π ≫ q = p) {r : ℕ} (σ : k →+* ℂ) {E : B.Modules} (h : VMetric q E r)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r) (cE : Chart E r) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U)
    (n : Low r → Γ(Y, W)) (H : Spans fl W (pullCol π cE.e hW (uniR n))) (i : Fin r) :
    ∃ ac : GlobalTheory.VBExt.AdaptedChart (VMetric.stepSeq fl i) i 1, ∀ y ∈ ptsIn p σ W, y ∈ ptsIn p σ ac.U ∧
      (((h.pull π w).stepMet fl i).met σ).gram ac.frame y =
        (chg (uni fun s => ev p σ W (n s) y) ((h.met σ).G cE (PtsOver.map π w (spMap σ) y))).submatrix
          (emb i) (emb i) := by
  obtain ⟨s, t, h₁, h₂, h₃⟩ := H.exists_adaptedChart i
  refine ⟨⟨W, s, t, h₁, h₂⟩, fun y hy => ⟨hy, ?_⟩⟩
  have hM : (uni fun s => ev p σ W (n s) y) = Matrix.of fun j l => ev p σ W (uniR n j l) y := by
    ext j l
    rw [← uniR_eq_uni, of_apply, uniR_apply, uniR_apply]
    split_ifs
    · rfl
    · rw [ev_eq hy]; exact (map_one _).symm
    · rw [ev_eq hy]; exact (map_zero _).symm
  ext j l
  rw [submatrix_apply, hM, ← form_pullCol π w (h.met σ) cE hW (uniR n) hy, ← h₃, ← h₃]
  exact Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy

theorem exists_cell_chart : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) (E : B.Modules) (h : VMetric q E r) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r), IsFlagBundle π (fun _ : Unit => E) (fun _ => r) (fun _ => fl) → ∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (cE : Chart E r) (c' : AlgChart p σ D), y ∈ c.e.source ∧ c.e.source ⊆ ptsIn q σ cE.U ∧ IsCell ε π w c c' ∧ ∀ y' ∈ c'.e.source, ∀ i : Fin r, chernMat ((VMetric.grLB fl i (H.pull π w)).φ σ) c' y' = cHess D (fun v => (rootWt ε (fun u => (h.met σ).G cE (c.e.symm u)) i v : ℂ)) (c'.e y') := by
  intro k _ B Y q p π w m r D ε σ E h H fl hfl c₀ y hy
  obtain ⟨U, f, hxU, hf⟩ : ∃ (U : B.Opens) (f : Fin r → Γ(E, U)),
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ IsFrame f := h.isVB _
  obtain ⟨c, hyc, hcV⟩ := exists_chart_le c₀ hy U (mem_ptsIn.2 hxU)
  let cE : Chart E r := ⟨c.U, fun l => GlobalTheory.Twist.resM E hcV (f l), hf.res hcV⟩
  obtain ⟨W, hW, hWa, n, hb, hs⟩ := GlobalTheory.CellScheme.cell_affine B Y π Unit (fun _ => r) (fun _ => E) (fun _ => fl) hfl
    (fun _ => h.isVB) c.U c.affine (fun _ => cE.e) fun _ => cE.isFrame
  have hb' : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom fun s : Low r => n ⟨(), s⟩) := by
    have e₁ : (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom fun s : Low r => n ⟨(), s⟩) =
        (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n).comp
          (MvPolynomial.renameEquiv _ (Equiv.uniqueSigma fun _ : Unit => Low r).symm).toRingEquiv.toRingHom :=
      MvPolynomial.ringHom_ext (fun a => by simp) fun s => by simp [Equiv.uniqueSigma]
    rw [e₁, RingHom.coe_comp]
    exact hb.comp (MvPolynomial.renameEquiv _ (Equiv.uniqueSigma fun _ : Unit => Low r).symm).bijective
  obtain ⟨c', hc, hsrc, hfib⟩ := exists_cell π w ε c hW hWa _ hb' ⟨y, hyc⟩
  refine ⟨c, cE, c', hyc, c.source_subset, hc, fun y' hy' i => ?_⟩
  obtain ⟨ac, hac⟩ := exists_adapted_gram π w σ h fl cE hW _ (hs ()) i
  have hU := (hac y' (hsrc hy')).1
  rw [chernMat, c'.hess_eq (((VMetric.grLB fl i (H.pull π w))).cInf σ) hy' (i := ac.quot) hU (mem_pick _ y')]
  unfold AlgChart.hess
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy')] with v hv
  have hz := c'.e.map_target hv
  have hbv : c.e.symm (base ε v) = PtsOver.map π w (spMap σ) (c'.e.symm v) := by
    have h1 := hc.2.2 _ hz
    rw [c'.e.right_inv hv] at h1
    have h2 := hz
    rw [hc.1] at h2
    rw [h1, c.e.left_inv h2.1]
  have hfv : fib ε v = fun s => ev p σ W (n ⟨(), s⟩) (c'.e.symm v) := by
    have h1 := funext (hfib _ hz)
    rwa [c'.e.right_inv hv] at h1
  congr 1
  show -Real.log _ = -Real.log _
  beta_reduce
  rw [hbv, hfv, ← (hac _ (hsrc hz)).2]
  exact congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => -Real.log M.det.re)
    (Met.quot_G _ (VMetric.stepSeq_shortExact _ _) (fl.isVB i.castSucc) (fl.isVB_gr i) ac (hac _ (hsrc hz)).1)

end GlobalTheory.FlagCellDim
