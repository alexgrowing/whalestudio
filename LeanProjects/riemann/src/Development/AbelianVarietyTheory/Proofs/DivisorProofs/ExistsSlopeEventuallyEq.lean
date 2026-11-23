import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableProdPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelSubbundleIsVB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm GlobalTheory.CovTest GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CxForm
open GlobalTheory.FlagFibre (Low)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.FibTriv

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}
  (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (hE : IsVB E 2) (cE : Chart E 2)
  (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)

abbrev cols {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) : Fin 2 → Γ((Scheme.Modules.pullback π).obj E, W) :=
  pullCol π cE.e hW (uniR fun _ => n)

include w in

theorem crd_cols {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    (cE.pull hE π).crd p σ (cols π cE hW n 0) y = ![1, ev p σ W n y] ∧
      (cE.pull hE π).crd p σ (cols π cE hW n 1) y = ![0, 1] := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := ptsIn_mono hW hy
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have key (b : Fin 2) : (cE.pull hE π).crd p σ (cols π cE hW n b) y =
      fun a => ev p σ W (uniR (fun _ : Low 2 => n) a b) y := by
    funext a
    simp only [cols, pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull hE π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  constructor <;> rw [key] <;> funext a <;> fin_cases a <;> simp [uniR_apply, ev_eq hy]

include w in

theorem lineVec_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) : ∃ t : ℂ, t ≠ 0 ∧ lineVec π hE cE fl y = t • ![1, ev p σ W n y] := by
  obtain ⟨s, hs, es⟩ := h 1
  let cs : Chart (fl.F 1) 1 := ⟨W, s, hs⟩
  have ha := mem_frameAt fl y
  have hu := (isUnit_iff_isUnit_det _).1 (cs.isUnit_tr (frameAt fl y).sub hy ha)
  rw [det_unique] at hu
  refine ⟨_, hu.ne_zero, ?_⟩
  refine ((cE.pull hE π).crd_app cs (fl.ι 1) ((frameAt fl y).e 0) ha hy).trans ?_
  have e : (fl.ι 1).app W (cs.e 0) = cols π cE hW n 0 := es (0 : Fin 1)
  funext a
  simp only [mulVec, dotProduct, Fin.sum_univ_one, of_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm, ← (crd_cols π w hE cE hW n hy).1, ← e]
  rfl

theorem mem_finPart_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n))
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    y ∈ finPart π w hE cE fl σ ∧ slope π hE cE fl y = ev p σ W n y := by
  obtain ⟨t, ht, e⟩ := lineVec_of_spans π w hE cE fl hW n h hy
  refine ⟨⟨ptsIn_mono hW hy, by simpa [e] using ht⟩, ?_⟩
  simp [slope, e, ht]

theorem exists_spans {y : CxPts p σ} (hy : y ∈ finPart π w hE cE fl σ) :
    ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)), y ∈ ptsIn p σ W ∧ Spans fl W (cols π cE hW n) := by
  let a := frameAt fl y
  let c := cE.pull hE π
  have h₀ : y ∈ ptsIn p σ (a.U ⊓ c.U) := mem_ptsIn_inf.2 ⟨mem_frameAt fl y, hy.1⟩
  let α : Fin 2 → Γ(Y, a.U ⊓ c.U) := (c.isFrame.basis inf_le_right).repr (resM _ inf_le_left (a.frame (.inl 0)))
  have hα : resM _ inf_le_left (a.frame (.inl 0)) = ∑ i, α i • resM _ inf_le_right (c.e i) := by
    conv_lhs => rw [← (c.isFrame.basis inf_le_right).sum_repr (resM _ inf_le_left (a.frame (.inl 0)))]
    simp only [IsFrame.basis_apply]
    rfl
  have hle := Y.basicOpen_le (α 0)
  obtain ⟨u, hu⟩ : IsUnit (resG Y hle (α 0)) := Y.toRingedSpace.isUnit_res_basicOpen (α 0)
  refine ⟨Y.basicOpen (α 0), hle.trans inf_le_right, resG Y hle (α 1) * u⁻¹.val,
    (mem_ptsIn_basicOpen h₀ _).2 hy.2, fun l => ?_⟩
  fin_cases l
  · refine ⟨Fin.elim0, fun W h => ?_, fun j => j.elim0⟩
    have z := isVB_zero_iff.1 (fl.isVB 0)
    refine ⟨fun _ _ _ => funext fun j => j.elim0, fun s => ⟨0, ?_⟩⟩
    have e := congrArg (fun φ => Scheme.Modules.Hom.app φ W s) (z.eq_of_src (𝟙 _) 0)
    exact (map_zero _).trans e.symm
  · refine ⟨_, UniColFrame.isFrame_cols (a.he.res (hle.trans inf_le_left)) (Matrix.of fun _ _ => u⁻¹.val) (by simp), fun j => ?_⟩
    obtain rfl : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    have e := congrArg (resM _ hle) hα
    have e' (i : Fin 2) : resM _ (hle.trans inf_le_right) (c.e i) =
        pullbackSections π E (hle.trans inf_le_right) (cE.e i) := QCoh.res_pullbackSections π E _ _ _
    simp only [resM_resM, map_add, resM_smul, Fin.sum_univ_two, ← hu, e'] at e
    refine (congrArg _ (Fin.sum_univ_one _)).trans ((Scheme.Modules.Hom.app_smul _ _ _).trans ?_)
    refine (congrArg (_ • ·) ((app_resM _ _ _).trans e)).trans ?_
    change _ = cols π cE _ _ 0
    rw [of_apply, smul_add, smul_smul, smul_smul, Units.inv_mul, mul_comm]
    unfold cols pullCol
    rw [Fin.sum_univ_two]
    rfl
  · have hf := UniColFrame.isFrame_pullCol_uniR _ _ π E 2 hE _ cE.e cE.isFrame _ (hle.trans inf_le_right)
      fun _ => resG Y hle (α 1) * u⁻¹.val
    refine ⟨_, hf.map_iso (inv (fl.ι (Fin.last 2))), fun j => ?_⟩
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ _ _) (IsIso.inv_hom_id (fl.ι (Fin.last 2)))

theorem eq_of_slope_eq (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) {y y' : CxPts p σ}
    (hy : y ∈ finPart π w hE cE fl σ) (hy' : y' ∈ finPart π w hE cE fl σ)
    (e : PtsOver.map π w (spMap σ) y = PtsOver.map π w (spMap σ) y') (es : slope π hE cE fl y = slope π hE cE fl y') :
    y = y' := by
  obtain ⟨W, hW, n, hyW, hs⟩ := exists_spans π w hE cE fl hy
  obtain ⟨W', hW', n', hyW', hs'⟩ := exists_spans π w hE cE fl hy'
  rw [(mem_finPart_of_spans π w hE cE fl hW n hs hyW).2, (mem_finPart_of_spans π w hE cE fl hW' n' hs' hyW').2,
    ev_eq hyW, ev_eq hyW'] at es
  have e₁ : y'.1 ≫ π = y.1 ≫ π := (congrArg Subtype.val e).symm
  have k₁ := spans_pullCol_of_carries _ _ _ π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) y.1 (y.1 ≫ π) rfl _
    (carries_carried π _ _ _ y.1 _ rfl) cE.U () cE.e W hW _ ⊤ hyW hy.1 hs
  have k₂ := spans_pullCol_of_carries _ _ _ π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) y'.1 (y.1 ≫ π) e₁ _
    (carries_carried π _ _ _ y'.1 _ e₁) cE.U () cE.e W' hW' _ ⊤ hyW' hy.1 hs'
  rw [map_uniR] at k₁ k₂
  have e₂ : (y'.1.appLE W' ⊤ hyW').hom n' = (y.1.appLE W ⊤ hyW).hom n :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 es.symm
  rw [e₂] at k₂
  refine Subtype.ext ((hfl _ (y.1 ≫ π) (carried π _ _ (fun _ => fl) y.1 _ rfl)).unique
    ⟨rfl, carries_carried π _ _ _ y.1 _ rfl⟩ ⟨e₁, fun a i => ?_⟩)
  obtain ⟨e, he⟩ := steps_iso_of_spans_top _ _ _ _ _ _ k₂ k₁ i
  exact ⟨e, by simpa [carried, Vert.Flag.ofIso, Vert.Flag.pull] using he⟩

theorem exists_cell (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) {U : B.Opens} (hU : IsAffineOpen U)
    (h : U ≤ cE.U) : ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : Γ(Y, W)), IsAffineOpen W ∧
      Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n) ∧
      Spans fl W (cols π cE (hW.trans (π.preimage_mono h)) n) ∧
      ptsIn p σ W = PtsOver.map π w (spMap σ) ⁻¹' ptsIn q σ U ∩ finPart π w hE cE fl σ := by
  obtain ⟨W, hW, hWa, n, hn, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl (fun _ => hE) U hU
    (fun _ i => resM E h (cE.e i)) fun _ => cE.isFrame.res h
  let s₀ : Σ _ : Unit, Low 2 := ⟨(), ⟨(1, 0), by decide⟩⟩
  have hs₀ (s : Σ _ : Unit, Low 2) : s = s₀ := by revert s; decide
  have hb : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n s₀) := by
    let ε : Unit ≃ Σ _ : Unit, Low 2 := ⟨fun _ => s₀, fun _ => (), fun _ => rfl, fun s => (hs₀ s).symm⟩
    have e : (MvPolynomial.eval₂Hom (π.appLE U W hW).hom fun _ : Unit => n s₀) =
        (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n).comp (MvPolynomial.renameEquiv Γ(B, U) ε).toRingEquiv.toRingHom :=
      MvPolynomial.ringHom_ext (fun a => by simp) fun a => by simp [ε]
    rw [e]
    exact hn.comp (MvPolynomial.renameEquiv Γ(B, U) ε).bijective
  have hS : Spans fl W (cols π cE (hW.trans (π.preimage_mono h)) (n s₀)) := by
    have := hs ()
    simp only [hs₀ ⟨(), _⟩] at this
    convert this using 1
    funext j
    exact Finset.sum_congr rfl fun l _ => congrArg _ (QCoh.pullbackSections_res π E hW h (cE.e l)).symm
  refine ⟨W, hW, n s₀, hWa, hb, hS, Set.ext fun y => ⟨fun hy => ⟨CellChart.map_mem π w hW hy,
    (mem_finPart_of_spans π w hE cE fl _ _ hS hy).1⟩, fun hy => ?_⟩⟩
  have hm := CellChart.cellPt_mem π w hW hWa _ hb hy.1 fun _ => slope π hE cE fl y
  have h₁ := mem_finPart_of_spans π w hE cE fl _ _ hS hm
  rwa [eq_of_slope_eq π w hE cE fl hfl h₁.1 hy.2 (CellChart.map_cellPt π w hW hWa _ hb hU _ _)
    (h₁.2.trans (CellChart.ev_n_cellPt π w hW hWa _ hb _ _ ()))] at hm

def swapChart : Chart E 2 := ⟨cE.U, cE.e ∘ Equiv.swap 0 1, cE.isFrame.comp_equiv _⟩

include w in

theorem lineVec_swap {y : CxPts p σ} (hy : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U) :
    lineVec π hE (swapChart cE) fl y 0 = lineVec π hE cE fl y 1 ∧
      lineVec π hE (swapChart cE) fl y 1 = lineVec π hE cE fl y 0 := by
  have h := (cE.pull hE π).tr_mulVec ((swapChart cE).pull hE π) ((frameAt fl y).frame (.inl 0)) (mem_frameAt fl y) hy
  have e (b : Fin 2) : (cE.pull hE π).crd p σ (((swapChart cE).pull hE π).e b) y = Pi.single (Equiv.swap 0 1 b) 1 :=
    (cE.crd_pull hE π w _ le_rfl hy hy).trans (cE.crd_frame hy _)
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  simp [mulVec, dotProduct, Chart.tr, e] at h₀ h₁
  exact ⟨h₁, h₀⟩

include w in

theorem exists_adapted_of_spans {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Γ(Y, W)) (h : Spans fl W (cols π cE hW n)) :
    ∃ a : AdaptedChart (lineSC fl) 1 1, a.U = W ∧ ∀ y ∈ ptsIn p σ W,
      (cE.pull hE π).crd p σ (a.frame (.inl 0)) y = ![1, ev p σ W n y] ∧
      (cE.pull hE π).crd p σ (a.frame (.inr 0)) y = ![0, 1] := by
  obtain ⟨s, hs, es⟩ := h 1
  have hf := UniColFrame.isFrame_pullCol_uniR _ _ π E 2 hE _ cE.e cE.isFrame _ hW fun _ => n
  refine ⟨⟨W, s, fun j => cols π cE hW n (Fin.natAdd 1 j), hs,
    isFrame_cokernel_π (l := 1) (m := 1) (fl.ι 1) hf hs fun j => es j⟩, rfl, fun y hy => ⟨?_, ?_⟩⟩
  · exact (congrArg (fun t => (cE.pull hE π).crd p σ t y) (es (0 : Fin 1))).trans (crd_cols π w hE cE hW n hy).1
  · exact (crd_cols π w hE cE hW n hy).2

section

variable {d : ℕ}

theorem etale_snoc {k A R : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : Fin d → A) (f : A →+* R) (n : R)
    (hg : (MvPolynomial.eval₂Hom α t).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f fun _ : Unit => n)) :
    (MvPolynomial.eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun a => f (t a)) n)).Etale := by
  let ι : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial Unit (MvPolynomial (Fin d) k) :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
      (Fin.snoc (α := fun _ => _) (fun a => MvPolynomial.C (MvPolynomial.X a)) (MvPolynomial.X ()))
  let κ : MvPolynomial Unit (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d + 1)) k :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom MvPolynomial.C fun a => MvPolynomial.X a.castSucc)
      fun _ => MvPolynomial.X (Fin.last d)
  have h1 : κ.comp ι = RingHom.id _ := MvPolynomial.ringHom_ext (fun r => by simp [ι, κ]) fun j => by
    induction j using Fin.lastCases <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := MvPolynomial.ringHom_ext'
    (MvPolynomial.ringHom_ext (fun r => by simp [ι, κ]) fun j => by simp [ι, κ]) fun j => by simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun a => f (t a)) n) =
      (MvPolynomial.eval₂Hom f fun _ : Unit => n).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α t)).comp ι) :=
    MvPolynomial.ringHom_ext (fun r => by simp [ι]) fun j => by induction j using Fin.lastCases <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

theorem exists_chart_le (c : AlgChart q σ d) {b : CxPts q σ} (hb : b ∈ c.e.source) {U : B.Opens} (hU : b ∈ ptsIn q σ U) :
    ∃ c₁ : AlgChart q σ d, b ∈ c₁.e.source ∧ c₁.U ≤ U ∧ c₁.e = c.e.restrOpen (ptsIn q σ c₁.U) (isOpen_ptsIn _) := by
  obtain ⟨f, hfU, hf⟩ := c.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hU⟩ (mem_ptsIn.1 (c.source_subset hb))
  have hle : B.basicOpen f ≤ c.U := B.basicOpen_le f
  refine ⟨⟨c.e.restrOpen (ptsIn q σ (B.basicOpen f)) (isOpen_ptsIn _), B.basicOpen f, c.affine.basicOpen f,
    fun a => resG B hle (c.x a), ?_, inter_subset_right, fun y hy a => (c.apply_eq y hy.1 a).trans (ev_res hle hy.2 _).symm,
    fun W g => (c.holo W g).mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hb, mem_ptsIn.2 hf⟩, hfU, rfl⟩
  have e : MvPolynomial.eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c.x a)) =
      (resG B hle).comp (MvPolynomial.eval₂Hom (algX q c.U) c.x) := by
    rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
  rw [e]
  have hR : (resG B hle).Etale := by
    letI : Algebra Γ(B, c.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
    haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c.affine.isLocalization_basicOpen f
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
  exact RingHom.Etale.stableUnderComposition _ _ c.etale hR

theorem exists_prodChart (c : AlgChart q σ d) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W) (n : Γ(Y, W))
    (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom fun _ : Unit => n)) (y₀ : CxPts p σ) :
    ∃ c' : AlgChart p σ (d + 1), c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W ∧
      c'.e.target = basePt ⁻¹' c.e.target ∧
      ∀ y, c'.e y = prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W n y) := by
  classical
  let s (v : V (d + 1)) : CxPts p σ := if h : basePt v ∈ c.e.target then
    CellChart.cellPt π w hW hWa _ hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) else y₀
  have hs {v : V (d + 1)} (h : basePt v ∈ c.e.target) : s v =
    CellChart.cellPt π w hW hWa _ hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) := dif_pos h
  have s₁ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : s v ∈ ptsIn p σ W := by
    rw [hs h]; exact CellChart.cellPt_mem ..
  have s₂ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : PtsOver.map π w (spMap σ) (s v) = c.e.symm (basePt v) := by
    rw [hs h]; exact CellChart.map_cellPt _ _ _ _ _ _ c.affine _ _
  have s₃ (v : V (d + 1)) (h : basePt v ∈ c.e.target) : ev p σ W n (s v) = v (Fin.last d) := by
    rw [hs h]; exact CellChart.ev_n_cellPt π w hW hWa _ hΦ _ _ ()
  have hT : IsOpen (basePt ⁻¹' c.e.target : Set (V (d + 1))) := c.e.open_target.preimage differentiable_basePt.continuous
  have hol (g : Γ(Y, W)) : DifferentiableOn ℂ (fun v => ev p σ W g (s v)) (basePt ⁻¹' c.e.target) := by
    obtain ⟨P, rfl⟩ := hΦ.2 g
    induction P using MvPolynomial.induction_on with
    | C a =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => ev q σ c.U a (c.e.symm (basePt v))) (basePt ⁻¹' c.e.target) :=
        (c.holo c.U a).comp differentiable_basePt.differentiableOn fun v hv => ⟨hv, c.source_subset (c.e.map_target hv)⟩
      refine hd.congr fun v hv => ?_
      rw [MvPolynomial.eval₂Hom_C, CellChart.ev_appLE π w hW (s₁ v hv), s₂ v hv]
    | add P Q hP hQ =>
      simp only [map_add, ev_add]
      exact hP.add hQ
    | mul_X P i hP =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (Fin.last d)) (basePt ⁻¹' c.e.target) := by fun_prop
      simp only [map_mul, ev_mul, MvPolynomial.eval₂Hom_X']
      exact hP.mul (hd.congr s₃)
  obtain ⟨hc, hh⟩ := holo_of_affine hWa hT s₁ hol
  have hπ := PtsOver.continuous_map π w (spMap σ)
  let e : OpenPartialHomeomorph (CxPts p σ) (V (d + 1)) :=
    { toFun y := prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W n y)
      invFun := s
      source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
      target := basePt ⁻¹' c.e.target
      map_source' y hy := by simpa using c.e.map_source hy.1
      map_target' v hv := ⟨by rw [mem_preimage, s₂ v hv]; exact c.e.map_target hv, s₁ v hv⟩
      left_inv' y hy := by
        rw [hs (by simpa using c.e.map_source hy.1)]
        refine (CellChart.cellPt_congr π w hW hWa _ hΦ _ (CellChart.map_mem π w hW hy.2) ?_ ?_).trans
          (CellChart.cellPt_self π w hW hWa _ hΦ hy.2)
        · rw [basePt_prodPt, c.e.left_inv hy.1]
        · simp
      right_inv' v hv := by rw [s₂ v hv, s₃ v hv, c.e.right_inv hv, prodPt_basePt]
      open_source := (c.e.open_source.preimage hπ).inter (isOpen_ptsIn W)
      open_target := hT
      continuousOn_toFun := differentiable_prodPt.continuous.comp_continuousOn
        ((c.e.continuousOn.comp hπ.continuousOn fun y hy => hy.1).prodMk ((continuousOn_ev n).mono inter_subset_right))
      continuousOn_invFun := hc }
  refine ⟨⟨e, W, hWa, Fin.snoc (α := fun _ => _) (fun a => (π.appLE c.U W hW).hom (c.x a)) n, ?_, inter_subset_right,
    fun y hy a => ?_, hh⟩, rfl, rfl, fun _ => rfl⟩
  · have h := etale_snoc (algX q c.U) c.x (π.appLE c.U W hW).hom n c.etale hΦ
    rwa [CellChart.algX_eq π w hW] at h
  · change prodPt _ _ a = _
    induction a using Fin.lastCases with
    | last => rw [prodPt_last, Fin.snoc_last]
    | cast a => rw [prodPt_castSucc, Fin.snoc_castSucc, c.apply_eq _ hy.1, CellChart.ev_appLE π w hW hy.2]

end

variable {d : ℕ} (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl)

include hfl in

theorem exists_slope_eq {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    ∃ y ∈ finPart π w hE cE fl σ, PtsOver.map π w (spMap σ) y = b ∧ slope π hE cE fl y = x := by
  obtain ⟨U, hU, hbU, h⟩ := exists_isAffineOpen_le b.1 hb
  obtain ⟨W, hW, n, hWa, hΦ, hS, -⟩ := exists_cell (σ := σ) π w hE cE fl hfl hU h
  have h₁ := mem_finPart_of_spans π w hE cE fl _ _ hS (CellChart.cellPt_mem π w hW hWa _ hΦ (b := b) hbU fun _ => x)
  exact ⟨_, h₁.1, CellChart.map_cellPt π w hW hWa _ hΦ hU _ _, h₁.2.trans (CellChart.ev_n_cellPt π w hW hWa _ hΦ _ _ ())⟩

include hfl in

theorem exists_triv (b : CxPts q σ) (x : ℂ) : ∃ y : CxPts p σ, PtsOver.map π w (spMap σ) y = b ∧
    (b ∈ ptsIn q σ cE.U → y ∈ finPart π w hE cE fl σ ∧ slope π hE cE fl y = x) := by
  by_cases hb : b ∈ ptsIn q σ cE.U
  · obtain ⟨y, h₁, h₂, h₃⟩ := exists_slope_eq π w hE cE fl hfl hb x
    exact ⟨y, h₂, fun _ => ⟨h₁, h₃⟩⟩
  · obtain ⟨y, -, h₂, -⟩ := exists_slope_eq π w hE _ fl hfl (hE.mem_pick b) x
    exact ⟨y, h₂, fun h => (hb h).elim⟩

def triv (b : CxPts q σ) (x : ℂ) : CxPts p σ := (exists_triv π w hE cE fl hfl b x).choose

theorem map_triv (b : CxPts q σ) (x : ℂ) : PtsOver.map π w (spMap σ) (triv π w hE cE fl hfl b x) = b :=
  (exists_triv π w hE cE fl hfl b x).choose_spec.1

variable {cE}

theorem triv_mem {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    triv π w hE cE fl hfl b x ∈ finPart π w hE cE fl σ :=
  ((exists_triv π w hE cE fl hfl b x).choose_spec.2 hb).1

theorem slope_triv {b : CxPts q σ} (hb : b ∈ ptsIn q σ cE.U) (x : ℂ) :
    slope π hE cE fl (triv π w hE cE fl hfl b x) = x :=
  ((exists_triv π w hE cE fl hfl b x).choose_spec.2 hb).2

theorem triv_slope {y : CxPts p σ} (hy : y ∈ finPart π w hE cE fl σ) :
    triv π w hE cE fl hfl (PtsOver.map π w (spMap σ) y) (slope π hE cE fl y) = y :=
  eq_of_slope_eq π w hE cE fl hfl (triv_mem π w hE fl hfl hy.1 _) hy (map_triv ..) (slope_triv π w hE fl hfl hy.1 _)

omit hfl in

theorem mem_infPart_iff {y : CxPts p σ} : y ∈ infPart π w hE cE fl σ ↔
    y ∈ finPart π w hE (swapChart cE) fl σ ∧ slope π hE (swapChart cE) fl y = 0 := by
  refine ⟨fun h => ?_, fun h => ⟨h.1.1, ?_⟩⟩
  · obtain ⟨e₀, e₁⟩ := lineVec_swap π w hE cE fl h.1
    refine ⟨⟨h.1, fun h₀ => lineVec_ne_zero π w hE cE fl h.1 (funext fun a => ?_)⟩, by rw [slope, e₁, h.2, zero_div]⟩
    fin_cases a
    exacts [h.2, e₀.symm.trans h₀]
  · exact (lineVec_swap π w hE cE fl h.1.1).2.symm.trans ((div_eq_zero_iff.1 h.2).resolve_right h.1.2)

theorem exists_trivChart (c : AlgChart q σ d) {b : CxPts q σ} (hc : b ∈ c.e.source) (hb : b ∈ ptsIn q σ cE.U) :
    ∃ (c₁ : AlgChart q σ d) (c' : AlgChart p σ (d + 1)) (a : AdaptedChart (lineSC fl) 1 1),
      b ∈ c₁.e.source ∧ c₁.U ≤ cE.U ∧ c₁.e = c.e.restrOpen (ptsIn q σ c₁.U) (isOpen_ptsIn _) ∧
      c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source ∩ finPart π w hE cE fl σ ∧
      c'.e.target = basePt ⁻¹' c₁.e.target ∧
      (∀ y ∈ c'.e.source, c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (slope π hE cE fl y)) ∧
      (∀ v ∈ c'.e.target, c'.e.symm v = triv π w hE cE fl hfl (c₁.e.symm (basePt v)) (v (Fin.last d))) ∧
      ∀ y ∈ c'.e.source, y ∈ ptsIn p σ a.U ∧
        (cE.pull hE π).crd p σ (a.frame (.inl 0)) y = ![1, slope π hE cE fl y] ∧
        (cE.pull hE π).crd p σ (a.frame (.inr 0)) y = ![0, 1] := by
  obtain ⟨c₁, h₁, h₂, h₃⟩ := exists_chart_le c hc hb
  obtain ⟨W, hW, n, hWa, hΦ, hS, hP⟩ := exists_cell (σ := σ) π w hE cE fl hfl c₁.affine h₂
  obtain ⟨c', e₁, e₂, e₃⟩ := exists_prodChart π w c₁ hW hWa n hΦ (triv π w hE cE fl hfl b 0)
  obtain ⟨a, ha, ha'⟩ := exists_adapted_of_spans (σ := σ) π w hE cE fl _ n hS
  have hm (y) (hy : y ∈ c'.e.source) : y ∈ ptsIn p σ W := (e₁ ▸ hy).2
  have hs (y) (hy : y ∈ c'.e.source) := mem_finPart_of_spans π w hE cE fl _ n hS (hm y hy)
  have e₄ (y) (hy : y ∈ c'.e.source) : c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (slope π hE cE fl y) := by
    rw [e₃, (hs y hy).2]
  refine ⟨c₁, c', a, h₁, h₂, h₃, ?_, e₂, e₄, fun v hv => ?_, fun y hy => ⟨ha ▸ hm y hy, ?_⟩⟩
  · rw [e₁, hP]
    exact Set.ext fun y => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c₁.source_subset h.1, h.2⟩⟩
  · have hy := c'.e.map_target hv
    have e := (c'.e.right_inv hv).symm.trans (e₄ _ hy)
    conv_rhs => rw [e]
    rw [basePt_prodPt, prodPt_last, c₁.e.left_inv (e₁ ▸ hy).1, triv_slope π w hE fl hfl (hs _ hy).1]
  · rw [(hs y hy).2]
    exact ha' y (hm y hy)

include hfl in

theorem exists_chart_infPart (c : AlgChart q σ d) {y : CxPts p σ} (hc : PtsOver.map π w (spMap σ) y ∈ c.e.source)
    (hy : y ∈ infPart π w hE cE fl σ) : ∃ c' : AlgChart p σ (d + 1), y ∈ c'.e.source ∧
      ∀ z ∈ c'.e.source, z ∈ infPart π w hE cE fl σ ↔ c'.e z (Fin.last d) = 0 := by
  obtain ⟨c₁, c', -, h₁, -, -, e₁, -, e₃, -⟩ := exists_trivChart (cE := swapChart cE) π w hE fl hfl c hc hy.1
  refine ⟨c', e₁ ▸ ⟨h₁, ((mem_infPart_iff π w hE fl).1 hy).1⟩, fun z hz => ?_⟩
  rw [e₃ z hz, prodPt_last, mem_infPart_iff, and_iff_right (e₁ ▸ hz).2]

end GlobalTheory.FibTriv
