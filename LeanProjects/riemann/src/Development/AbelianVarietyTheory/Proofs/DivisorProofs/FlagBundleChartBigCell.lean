import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLift

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.MixDens (emb)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CellChart (cellPt cellPt_mem map_cellPt ev_n_cellPt ev_appLE cellPt_self cellPt_congr algX_eq map_mem)
open GlobalTheory.FlagCell (uniR uniR_eq_uni uniR_apply pullCol Spans form_pullCol Spans.exists_adaptedChart)
open Set
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.BigCell

theorem exists_chart_le_dim (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (σ : k →+* ℂ) {n : ℕ}
    (c₀ : AlgChart q σ n) (y : CxPts q σ) (hy : y ∈ c₀.e.source) (V : B.Opens) (hV : y ∈ ptsIn q σ V) :
    ∃ c : AlgChart q σ n, y ∈ c.e.source ∧ c.U ≤ V := by
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := V) ⟨_, mem_ptsIn.1 hV⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (MvPolynomial.eval₂Hom (algX q (B.basicOpen f))
      (fun a => resG B hle (c₀.x a))).Etale := by
    have e : MvPolynomial.eval₂Hom (algX q (B.basicOpen f))
        (fun a => resG B hle (c₀.x a)) =
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

open MvPolynomial in

theorem etale_eval₂Hom_sum_of_bijective {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A)
    {n : ℕ} (t : Fin n → A) (f : A →+* R) (m : N → R) {D : ℕ} (ε : Fin D ≃ Fin n ⊕ N)
    (hg : (MvPolynomial.eval₂Hom α t).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f m)) :
    (MvPolynomial.eval₂Hom (f.comp α) (fun j => Sum.elim (fun b => f (t b)) m (ε j))).Etale := by
  let ι : MvPolynomial (Fin D) k →+* MvPolynomial N (MvPolynomial (Fin n) k) :=
    eval₂Hom (C.comp C) (fun j => Sum.elim (fun b => C (X b)) X (ε j))
  let κ : MvPolynomial N (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin D) k :=
    eval₂Hom (eval₂Hom C (fun b => X (ε.symm (.inl b)))) (fun i => X (ε.symm (.inr i)))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      obtain ⟨o, rfl⟩ := ε.symm.surjective j
      cases o <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j
        simp [ι, κ]
    · intro j
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (fun j => Sum.elim (fun b => f (t b)) m (ε j)) =
      (MvPolynomial.eval₂Hom f m).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α t)).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      obtain ⟨o, rfl⟩ := ε.symm.surjective j
      cases o <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι)
      (GlobalTheory.etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

end GlobalTheory.BigCell

namespace GlobalTheory.BigCell

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {ι : Type} {r : ι → ℕ} {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a)))

omit [CommRing k] in

theorem differentiable_base : Differentiable ℂ (base ε) := (baseL ε).differentiable

variable (c : AlgChart q σ n) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (m : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom m))
  (y₀ : CxPts p σ)

def cellInv (v : V D) : CxPts p σ :=
  if h : base ε v ∈ c.e.target then
    cellPt π w hW hWa m hΦ (c.source_subset (c.e.map_target h)) (fun s => v (ε.symm (.inr s)))
  else y₀

variable {ε c hW hWa m hΦ}

theorem cellInv_eq {v : V D} (h : base ε v ∈ c.e.target) : cellInv π w ε c hW hWa m hΦ y₀ v =
    cellPt π w hW hWa m hΦ (c.source_subset (c.e.map_target h)) (fun s => v (ε.symm (.inr s))) := dif_pos h

theorem cellInv_mem {v : V D} (h : base ε v ∈ c.e.target) : cellInv π w ε c hW hWa m hΦ y₀ v ∈ ptsIn p σ W := by
  rw [cellInv_eq _ _ _ h]; exact cellPt_mem ..

theorem map_cellInv {v : V D} (h : base ε v ∈ c.e.target) :
    PtsOver.map π w (spMap σ) (cellInv π w ε c hW hWa m hΦ y₀ v) = c.e.symm (base ε v) := by
  rw [cellInv_eq _ _ _ h]; exact map_cellPt _ _ _ _ _ _ c.affine _ _

theorem ev_m_cellInv {v : V D} (h : base ε v ∈ c.e.target) (s : Σ a, Low (r a)) :
    ev p σ W (m s) (cellInv π w ε c hW hWa m hΦ y₀ v) = v (ε.symm (.inr s)) := by
  rw [cellInv_eq _ _ _ h]; exact ev_n_cellPt ..

theorem ev_appLE_cellInv {v : V D} (h : base ε v ∈ c.e.target) (g : Γ(B, c.U)) :
    ev p σ W ((π.appLE c.U W hW).hom g) (cellInv π w ε c hW hWa m hΦ y₀ v) =
      ev q σ c.U g (c.e.symm (base ε v)) := by
  rw [ev_appLE π w hW (cellInv_mem π w y₀ h), map_cellInv π w y₀ h]

theorem holo_cellInv (g : Γ(Y, W)) :
    DifferentiableOn ℂ (fun v => ev p σ W g (cellInv π w ε c hW hWa m hΦ y₀ v)) {v | base ε v ∈ c.e.target} := by
  obtain ⟨P, rfl⟩ := hΦ.2 g
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hd : DifferentiableOn ℂ (fun v => ev q σ c.U a (c.e.symm (base ε v))) {v | base ε v ∈ c.e.target} :=
      (c.holo c.U a).comp (differentiable_base ε).differentiableOn fun v hv =>
        ⟨hv, c.source_subset (c.e.map_target hv)⟩
    refine hd.congr fun v hv => ?_
    simp only [MvPolynomial.eval₂Hom_C]
    exact ev_appLE_cellInv π w y₀ hv a
  | add P Q hP hQ =>
    simp only [map_add, ev_add]
    exact hP.add hQ
  | mul_X P s hP =>
    have hd : DifferentiableOn ℂ (fun v : V D => v (ε.symm (.inr s))) {v | base ε v ∈ c.e.target} := by
      fun_prop
    simp only [map_mul, ev_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hd.congr fun v hv => ev_m_cellInv π w y₀ hv s)

end Chart

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {ι : Type} {r : ι → ℕ} {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a)))
  (c : AlgChart q σ n) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (m : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom m))
  (y₀ : CxPts p σ)

def cellToF (y : CxPts p σ) : V D :=
  pt ε (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (m ⟨a, s⟩) y

def cellE : OpenPartialHomeomorph (CxPts p σ) (V D) where
  toFun := cellToF π w ε c m
  invFun := cellInv π w ε c hW hWa m hΦ y₀
  source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
  target := {v | base ε v ∈ c.e.target}
  map_source' y hy := by
    show base ε (cellToF π w ε c m y) ∈ c.e.target
    rw [cellToF, base_pt]
    exact c.e.map_source hy.1
  map_target' v hv :=
    ⟨by rw [mem_preimage, map_cellInv π w y₀ hv]; exact c.e.map_target hv, cellInv_mem π w y₀ hv⟩
  left_inv' y hy := by
    have hb : base ε (cellToF π w ε c m y) ∈ c.e.target := by
      rw [cellToF, base_pt]; exact c.e.map_source hy.1
    rw [cellInv_eq π w y₀ hb]
    refine (cellPt_congr π w hW hWa m hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa m hΦ hy.2)
    · rw [cellToF, base_pt, c.e.left_inv hy.1]
    · funext s
      simp [cellToF, pt]
  right_inv' v hv := by
    ext j
    simp only [cellToF, pt, PiLp.toLp_apply]
    rcases h : ε j with b | s
    · have hj : ε.symm (.inl b) = j := by rw [← h, Equiv.symm_apply_apply]
      simp only [Sum.elim_inl]
      rw [map_cellInv π w y₀ hv, c.e.right_inv hv]
      simp [base, hj]
    · simp only [Sum.elim_inr]
      rw [ev_m_cellInv π w y₀ hv, ← h, Equiv.symm_apply_apply]
  open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)
  open_target := c.e.open_target.preimage (differentiable_base ε).continuous
  continuousOn_toFun := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
    rcases h : ε j with b | s
    · simp only [Sum.elim_inl]
      exact (PiLp.continuous_apply 2 _ b).comp_continuousOn
        (c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1)
    · simp only [Sum.elim_inr]
      exact (continuousOn_ev (m s)).mono inter_subset_right
  continuousOn_invFun := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base ε).continuous)
    (fun v hv => cellInv_mem π w y₀ hv) fun g => holo_cellInv π w y₀ g).1

def cellChart : AlgChart p σ D where
  e := cellE π w ε c hW hWa m hΦ y₀
  U := W
  affine := hWa
  x j := Sum.elim (fun b => (π.appLE c.U W hW).hom (c.x b)) m (ε j)
  etale := by
    have h := etale_eval₂Hom_sum_of_bijective (algX q c.U) c.x (π.appLE c.U W hW).hom m ε c.etale hΦ
    rwa [algX_eq π w hW] at h
  source_subset := inter_subset_right
  apply_eq y hy j := by
    show cellToF π w ε c m y j = _
    simp only [cellToF, pt, PiLp.toLp_apply]
    rcases h : ε j with b | s
    · simp only [Sum.elim_inl]
      rw [c.apply_eq _ hy.1 b, ev_appLE π w hW hy.2]
    · rfl
  holo W' f := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base ε).continuous)
    (fun v hv => cellInv_mem π w y₀ hv) fun g => holo_cellInv π w y₀ g).2 W' f

end Chart

theorem cell_chart (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B)
    (w : π ≫ q = p) (ι : Type) (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ)
    (c : AlgChart q σ n) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
    (m : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom m))
    (hne : c.e.source.Nonempty) :
    ∃ c' : AlgChart p σ D, IsCell ε π w c c' ∧ c'.e.source ⊆ ptsIn p σ W ∧
      ∀ y ∈ c'.e.source, ∀ a s, fib ε (c'.e y) a s = ev p σ W (m ⟨a, s⟩) y := by
  obtain ⟨b₀, hb₀⟩ := hne
  refine ⟨cellChart π w ε c hW hWa m hΦ (cellPt π w hW hWa m hΦ (c.source_subset hb₀) 0),
    ⟨rfl, rfl, fun y _ => ?_⟩, inter_subset_right, fun y _ a s => ?_⟩
  · exact base_pt ε (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (m ⟨a, s⟩) y
  · exact congrFun (congrFun (fib_pt ε (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (m ⟨a, s⟩) y) a) s

end GlobalTheory.BigCell

namespace GlobalTheory.BigCell

theorem isCellFrame_of_spans (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a)))
    (σ : k →+* ℂ) (a : ι) (E : B.Modules) (h : VMetric q E (r a))
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) (r a)) (cE : Chart E (r a)) (c' : AlgChart p σ D)
    (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ cE.U) (m : Low (r a) → Γ(Y, W)) (H : Spans fl W (pullCol π cE.e hW (uniR m)))
    (hs : c'.e.source ⊆ ptsIn p σ W) (hm : ∀ y ∈ c'.e.source, ∀ s, fib ε (c'.e y) a s = ev p σ W (m s) y) :
    IsCellFrame ε π w c' a h fl cE := by
  intro i
  obtain ⟨s, t, h₁, h₂, h₃⟩ := H.exists_adaptedChart i
  refine ⟨⟨W, s, t, h₁, h₂⟩, fun y hy => ⟨hs hy, ?_⟩⟩
  have hM : uni (fib ε (c'.e y) a) = Matrix.of fun j l => ev p σ W (uniR m j l) y := by
    ext j l
    rw [← uniR_eq_uni, of_apply, uniR_apply, uniR_apply, ev_eq (hs hy)]
    split_ifs
    · rw [hm y hy, ev_eq (hs hy)]
    · exact (map_one _).symm
    · exact (map_zero _).symm
  ext j l
  rw [submatrix_apply, hM, ← form_pullCol π w (h.met σ) cE hW (uniR m) (hs hy), ← h₃, ← h₃]
  exact Met.form_restrict _ (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ (hs hy)

end GlobalTheory.BigCell

open GlobalTheory.MixDens GlobalTheory.CovTest

theorem GlobalTheory.BigCell.exists_cell_charts : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (n D : ℕ) (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) (σ : k →+* ℂ) (E : ι → B.Modules) (h : ∀ a, VMetric q (E a) (r a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (cE : ∀ a, Chart (E a) (r a)) (c' : AlgChart p σ D), y ∈ c.e.source ∧ (∀ a, c.e.source ⊆ ptsIn q σ (cE a).U) ∧ BigCell.IsCell ε π w c c' ∧ ∀ a, BigCell.IsCellFrame ε π w c' a (h a) (fl a) (cE a) := by
  intro k _ B Y q p π w ι _ r n D ε σ E h fl hfl c₀ y hy
  have hx : ∀ a, ∃ (U : B.Opens) (f : Fin (r a) → Γ(E a, U)), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ IsFrame f :=
    fun a => (h a).isVB _
  choose U f hxU hf using hx
  let V : B.Opens := Finset.univ.inf U
  have hV (a : ι) : V ≤ U a := Finset.inf_le (Finset.mem_univ a)
  have hyV : y ∈ ptsIn q σ V := by
    rw [mem_ptsIn]
    show _ ∈ ((Finset.univ.inf U : B.Opens) : Set B)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simpa using hxU
  obtain ⟨c, hyc, hcV⟩ := GlobalTheory.BigCell.exists_chart_le_dim k B q σ c₀ y hy V hyV
  let cE : ∀ a, Chart (E a) (r a) := fun a => ⟨c.U, fun l => GlobalTheory.Twist.resM (E a) (hcV.trans (hV a)) (f a l),
    (hf a).res (hcV.trans (hV a))⟩
  obtain ⟨W, hW, hWa, m, hb, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π ι r E fl hfl (fun a => (h a).isVB) c.U c.affine
    (fun a => (cE a).e) fun a => (cE a).isFrame
  obtain ⟨c', hcell, hsrc, hfib⟩ := GlobalTheory.BigCell.cell_chart k B Y q p π w ι r n D ε σ c W hW hWa m hb ⟨y, hyc⟩
  refine ⟨c, cE, c', hyc, fun a => c.source_subset, hcell, fun a => ?_⟩
  exact GlobalTheory.BigCell.isCellFrame_of_spans k B Y q p π w ι r n D ε σ a (E a) (h a) (fl a) (cE a) c' W hW
    (fun s => m ⟨a, s⟩) (hs a) hsrc fun y hy s => hfib y hy a s
