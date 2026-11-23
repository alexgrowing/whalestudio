import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTrace
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.BcUnique

variable {M : Type} [TopologicalSpace M] {n r s : ℕ} {A : HolAtlas M n}

def frmSet (T : HermSeq A r s) (a : T.κ) (i : A.ι) : Set (V n) := (A.e i).target ∩ (A.e i).symm ⁻¹' T.U a

def midRead (T : HermSeq A r s) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  T.mid a ((A.e i).symm v)

def chgRead (T : HermSeq A r s) (a b : T.κ) (i : A.ι) (v : V n) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
  T.g a b ((A.e i).symm v)

theorem isOpen_frmSet (T : HermSeq A r s) (a : T.κ) (i : A.ι) : IsOpen (frmSet T a i) :=
  (A.e i).isOpen_inter_preimage_symm (T.isOpen a)

theorem isPosFrame_midRead (T : HermSeq A r s) (a : T.κ) (i : A.ι) : IsPosFrame (frmSet T a i) (midRead T a i) :=
  ⟨isOpen_frmSet T a i, fun p q => (T.smooth a).2.1 p q i, fun _ hv => (T.posDef a _ hv.2).2.1⟩

theorem mContDiffAt_midRead (T : HermSeq A r s) (a : T.κ) (i : A.ι) {v : V n} (hv : v ∈ frmSet T a i) :
    MContDiffAt 1 (midRead T a i) v :=
  (isPosFrame_midRead T a i).isHermFrame.one hv

theorem posDef_midRead (T : HermSeq A r s) (a : T.κ) (i : A.ι) {v : V n} (hv : v ∈ frmSet T a i) :
    ∀ᶠ x in 𝓝 v, (midRead T a i x).PosDef :=
  mem_of_superset ((isOpen_frmSet T a i).mem_nhds hv) fun x hx => (isPosFrame_midRead T a i).posDef x hx

theorem holo_chgRead (T : HermSeq A r s) (a b : T.κ) (i : A.ι) {v : V n} (hv : v ∈ frmSet T a i ∩ frmSet T b i) :
    MContDiffAt ∞ (chgRead T a b i) v ∧ ∀ᶠ w in 𝓝 v, ∀ η, mdbar (chgRead T a b i) w η = 0 := by
  have hs : frmSet T a i ∩ frmSet T b i = (A.e i).target ∩ (A.e i).symm ⁻¹' (T.U a ∩ T.U b) := by
    ext w; simp only [frmSet, mem_inter_iff, mem_preimage]; tauto
  have ho : IsOpen (frmSet T a i ∩ frmSet T b i) := (isOpen_frmSet T a i).inter (isOpen_frmSet T b i)
  have hd : ∀ p q, DifferentiableOn ℂ (fun w => chgRead T a b i w p q) (frmSet T a i ∩ frmSet T b i) := by
    intro p q; rw [hs]; exact T.holo a b p q i
  refine ⟨fun p q => ?_, ?_⟩
  · have h1 : ContDiffOn ℂ ∞ (fun w => chgRead T a b i w p q) (frmSet T a i ∩ frmSet T b i) :=
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ ho (hd p q)
    exact (h1.restrict_scalars ℝ).contDiffAt (ho.mem_nhds hv)
  filter_upwards [ho.mem_nhds hv] with w hw η
  ext p q
  rw [mdbar_apply, dbar_eq_zero ((hd p q).differentiableAt (ho.mem_nhds hw))]
  rfl

theorem extTrace_midRead_indep (T : HermSeq A r s) (a b : T.κ) (i : A.ι) {v : V n}
    (hv : v ∈ frmSet T a i ∩ frmSet T b i) : extTrace (midRead T a i) v = extTrace (midRead T b i) v := by
  have ho : IsOpen (frmSet T a i ∩ frmSet T b i) := (isOpen_frmSet T a i).inter (isOpen_frmSet T b i)
  have e : midRead T b i =ᶠ[𝓝 v] fun w => chg (chgRead T a b i w) (midRead T a i w) := by
    filter_upwards [ho.mem_nhds hv] with w hw
    exact (T.trans a b _ ⟨hw.1.2, hw.2.2⟩).2.1
  have ht : ∀ᶠ x in 𝓝 v, (chgRead T a b i x).toBlocks₂₁ = 0 := by
    filter_upwards [ho.mem_nhds hv] with w hw
    exact T.tri a b _ ⟨hw.1.2, hw.2.2⟩
  have hg := holo_chgRead T a b i hv
  have hu : IsUnit (chgRead T a b i v).det := by
    have ha : (A.e i).symm v ∈ T.U a := hv.1.2
    have hb : (A.e i).symm v ∈ T.U b := hv.2.2
    have h1 : T.g a b ((A.e i).symm v) * T.g b a ((A.e i).symm v) = 1 := by
      rw [T.g_mul a b a _ ⟨⟨ha, hb⟩, ha⟩, T.g_self a _ ha]
    exact Matrix.isUnit_det_of_right_inverse h1
  rw [extTrace_congr e, extTrace_chg (mContDiffAt_midRead T a i hv.1) (posDef_midRead T a i hv.1)
    (hg.1.of_le (by norm_cast)) hu hg.2.self_of_nhds ht]

theorem crd_mem_frmSet (T : HermSeq A r s) (x : A.Pt) {a : T.κ} (ha : x.pt ∈ T.U a) : x.crd ∈ frmSet T a x.1.1 :=
  ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact ha⟩

theorem bcFld_apply (T : HermSeq A r s) (x : A.Pt) :
    bcFld T x = (ofValues (extTrace (midRead T (T.cover x.pt).choose x.1.1) x.crd) : Alt n) := rfl

theorem loc_bcFld (T : HermSeq A r s) {a : T.κ} {i : A.ι} {v : V n} (hv : v ∈ frmSet T a i) :
    A.loc (bcFld T) i v = (ofValues (extTrace (midRead T a i) v) : Alt n) := by
  rw [HolAtlas.loc, dif_pos hv.1]
  have hc : (A.e i) ((A.e i).symm v) = v := (A.e i).right_inv hv.1
  change (ofValues (extTrace (midRead T (T.cover ((A.e i).symm v)).choose i) ((A.e i) ((A.e i).symm v))) : Alt n) = _
  rw [hc, extTrace_midRead_indep T _ a i ⟨⟨hv.1, (T.cover _).choose_spec⟩, hv⟩]

theorem extTrace_midRead_chart (T : HermSeq A r s) (x x' : A.Pt) (hxx : x.pt = x'.pt) (a : T.κ) (ha : x.pt ∈ T.U a)
    (ξ η : V n) : extTrace (midRead T a x.1.1) x.crd ξ η = extTrace (midRead T a x'.1.1) x'.crd
      (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd ξ) (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd η) := by
  have hy : x.pt ∈ (A.e x.1.1).source := x.2
  have hy' : x.pt ∈ (A.e x'.1.1).source := hxx ▸ x'.2
  have hl : (A.e x.1.1).symm x.crd = x.pt := (A.e x.1.1).left_inv hy
  have e₂ : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
    simp only [Function.comp_apply, HolAtlas.Pt.ch, hl]; rw [hxx]
  have hSo : IsOpen ((A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (A.e x'.1.1).source) :=
    (A.e x.1.1).isOpen_inter_preimage_symm (A.e x'.1.1).open_source
  have hSm : (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (A.e x'.1.1).source ∈ 𝓝 x.crd :=
    hSo.mem_nhds ⟨(A.e x.1.1).map_source hy, by simp only [mem_preimage, hl, hy']⟩
  have hφ : ContDiffAt ℂ 1 (x'.ch ∘ x.ch.symm) x.crd :=
    contDiffAt_euclidean.2 fun k => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hSo
      (differentiableOn_euclidean.1 (A.holo x.1.1 x'.1.1) k)).contDiffAt hSm).of_le (by norm_cast)
  have hmid : midRead T a x.1.1 =ᶠ[𝓝 x.crd] fun v => midRead T a x'.1.1 ((x'.ch ∘ x.ch.symm) v) := by
    filter_upwards [hSm] with v hv
    simp only [midRead, Function.comp_apply, HolAtlas.Pt.ch]
    rw [(A.e x'.1.1).left_inv hv.2]
  have hz : x'.crd ∈ frmSet T a x'.1.1 := crd_mem_frmSet T x' (hxx ▸ ha)
  have hMd := mContDiffAt_midRead T a x'.1.1 hz
  have hMp := posDef_midRead T a x'.1.1 hz
  rw [← e₂] at hMd hMp
  rw [extTrace_congr hmid, extTrace_comp_holo hMd hMp hφ, e₂]

theorem isRealForm_bcFld : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s),
    A.IsRealForm 1 (bcFld T) := by
  intro M _ n r s A T
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, fun x => ⟨?_, ?_⟩⟩
  · refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
    refine ⟨frmSet T (T.cover ((A.e i).symm v)).choose i, isOpen_frmSet T _ i, ⟨hv, (T.cover _).choose_spec⟩, ?_⟩
    have hc : ContDiffOn ℝ ∞ (fun w => (bas n).repr (ofValues (extTrace (midRead T (T.cover ((A.e i).symm v)).choose i) w) : Alt n) S)
        (frmSet T (T.cover ((A.e i).symm v)).choose i) := by
      simp only [GlobalTheory.LineForm.OmReal.repr_ofValues]
      exact ContDiffOn.sum fun p _ => ContDiffOn.sum fun q _ =>
        (GlobalTheory.SecForm.contDiffOn_extTrace (isPosFrame_midRead T _ i) _ _).mul contDiffOn_const
    exact (hc.mono inter_subset_right).congr fun w hw => by rw [loc_bcFld T hw.2]
  · have hfr : (T.cover x.pt).choose = (T.cover x'.pt).choose := by rw [h]
    have ha : x.pt ∈ T.U (T.cover x.pt).choose := (T.cover x.pt).choose_spec
    have hz : x'.crd ∈ frmSet T (T.cover x.pt).choose x'.1.1 := crd_mem_frmSet T x' (h ▸ ha)
    rw [bcFld_apply, bcFld_apply, ← hfr, GlobalTheory.LineForm.OmReal.pull_ofValues _
      (GlobalTheory.LineForm.OmReal.isSesq_extTrace (mContDiffAt_midRead T _ _ hz) (posDef_midRead T _ _ hz))]
    exact congrArg (fun α => (ofValues α : Alt n)) (funext fun ξ => funext fun η =>
      extTrace_midRead_chart T x x' h _ ha ξ η)
  · exact GlobalTheory.LineForm.OmReal.isType_ofValues _
  · have hz := crd_mem_frmSet T x (T.cover x.pt).choose_spec
    rw [bcFld_apply]
    exact GlobalTheory.LineForm.OmReal.isReal_ofValues
      (GlobalTheory.LineForm.OmReal.conj_extTrace (mContDiffAt_midRead T _ _ hz) (posDef_midRead T _ _ hz))

end GlobalTheory.BcUnique
