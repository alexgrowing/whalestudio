import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntInvariantUnderConjugation

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.ConjChart GlobalTheory.ShFam
open scoped ComplexConjugate

namespace GlobalTheory.ChernConjForm

theorem swap_matForm_transpose {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    swap (matForm n Hᵀ : Alt n) = -(matForm n H : Alt n) := by
  rw [ChernPull.coe_matForm, ChernPull.coe_matForm, map_smul, ← smul_neg, Finset.sum_comm]
  congr 1
  simp only [map_sum, map_smul, map_mul, (swap_dz _).1, (swap_dz _).2, transpose_apply, ← Finset.sum_neg_distrib,
    ← smul_neg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg _ ?_
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem cHess_comp_conjV {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) :
    cHess n (g ∘ conjV n) (conjV n y) = (cHess n g y)ᵀ := by
  have h1 : ∀ k, wdb n k (g ∘ conjV n) = (wd n k g) ∘ conjV n := fun k =>
    funext fun w => wdb_comp_conjV n k g w
  ext j l
  simp only [cHess, of_apply, transpose_apply]
  rw [h1, wd_comp_conjV, ChernConj.conjV_conjV, ReciprocityTheory.L2DbarEstimates.comm_wd_wdb g y hg]

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ σ' : k →+* ℂ}

theorem hessL_conj (L : HermLB p) (c : AlgChart p σ D) (c' : AlgChart p σ' D) {y : CxPts p σ} {y' : CxPts p σ'}
    (hy : y ∈ c.e.source) (hy' : y' ∈ c'.e.source) (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (H : ∀ z ∈ c.e.source, ∀ z' ∈ c'.e.source, z'.1 = spMap (starRingEnd ℂ) ≫ z.1 → ∀ a, c'.e z' a = conj (c.e z a)) :
    hessL L c' y' = (hessL L c y)ᵀ := by
  have h := eq_conj_of_conj e
  set i := pick (L.φ σ).isLB y
  have hi : y ∈ ptsIn p σ (L.B.U i) := mem_pick _ y
  set J := conjPts p h
  have hJ : ∀ z, (J z).1 = spMap (starRingEnd ℂ) ≫ z.1 := fun _ => rfl
  have ey : J y = y' := Subtype.ext e.symm
  have HJ : ∀ z ∈ c.e.source, J z ∈ c'.e.source → c'.e (J z) = conjV D (c.e z) := fun z hz hz' => by
    ext a
    exact H z hz _ hz' (hJ z) a
  have e₁ : c'.e y' = conjV D (c.e y) := ey ▸ HJ y hy (ey ▸ hy')
  have ho : IsOpen (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (L.B.U i) ∩ J ⁻¹' c'.e.source)) :=
    isOpen_over c.e ((isOpen_ptsIn _).inter (c'.e.open_source.preimage J.continuous))
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (L.B.U i) ∩ J ⁻¹' c'.e.source) :=
    mem_over c.e hy ⟨hi, by rw [mem_preimage, ey]; exact hy'⟩
  have hm' : conjV D (c.e y) ∈
      conjV D ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (L.B.U i) ∩ J ⁻¹' c'.e.source)) := by
    rw [mem_preimage, ChernConj.conjV_conjV]
    exact hm
  have e₂ : (fun v => ((L.φ σ').φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (conjV D (c.e y))]
      (fun v => ((L.φ σ).φ i (c.e.symm v) : ℂ)) ∘ conjV D := by
    filter_upwards [(ho.preimage (conjV D).continuous).mem_nhds hm'] with v hv
    have h₁ := HJ _ (c.e.map_target hv.1) hv.2.2
    rw [c.e.right_inv hv.1, ChernConj.conjV_conjV] at h₁
    have h₂ : c'.e.symm v = J (c.e.symm (conjV D v)) := by
      conv_lhs => rw [← h₁]
      exact c'.e.left_inv hv.2.2
    rw [h₂, L.conj σ σ' i _ _ (hJ _) hv.2.1]
    rfl
  refine (c'.hess_eq (L.cInf σ') hy' (mem_ptsIn_of_conj e hi) (mem_pick _ y')).trans ?_
  rw [AlgChart.hess, e₁, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₂]
  exact cHess_comp_conjV (Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c hy hi))

theorem swap_c1F_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D)
    (L : HermLB p) (σ σ' : k →+* ℂ) (x : (h.atlas σ).Pt) (x' : (h.atlas σ').Pt),
    x'.pt.1 = spMap (starRingEnd ℂ) ≫ x.pt.1 →
    (∀ z ∈ x.ch.source, ∀ z' ∈ x'.ch.source, z'.1 = spMap (starRingEnd ℂ) ≫ z.1 → ∀ a, x'.ch z' a = conj (x.ch z a)) →
    swap (fld _ (c1F h σ' L) x') = (-1 : ℂ) ^ 1 • fld _ (c1F h σ L) x := by
  rintro k _ X p D h L σ σ' ⟨⟨c, y⟩, hy⟩ ⟨⟨c', y'⟩, hy'⟩ e H
  simp only [fld]
  rw [c1F_eq_matForm_hessL h L hy, c1F_eq_matForm_hessL h L hy', hessL_conj L c c' hy hy' e H, swap_matForm_transpose, pow_one, neg_one_smul]

end GlobalTheory.ChernConjForm
