import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

set_option autoImplicit false

noncomputable section

open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open Filter Topology
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

def ofValuesTwo {n : ℕ} (Ψ : V n → V n → V n → V n → ℂ) : Ev n :=
  (1 / 4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d,
    Ψ (coordVec a) (coordVec b) (coordVec c) (coordVec d) • (sym (a, b) * sym (c, d))

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n}

def midIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  T.mid a ((A.e i).symm v)

def subIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1) (Fin 1) ℂ :=
  T.sub a ((A.e i).symm v)

def quotIn (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v : V n) : Matrix (Fin 1) (Fin 1) ℂ :=
  T.quot a ((A.e i).symm v)

def potS (T : HermSeq A 1 1) (a : T.κ) (y : M) : ℝ :=
  Real.log ((T.sub a y 0 0).re / (T.mid a y (.inl 0) (.inl 0)).re)

def potQ (T : HermSeq A 1 1) (a : T.κ) (y : M) : ℝ :=
  Real.log ((T.quot a y 0 0).re / (quotGram (T.mid a y) 0 0).re)

def locForm (T : HermSeq A 1 1) (a : T.κ) (i : A.ι) (v ξ η : V n) : ℂ :=
  extTrace (midIn T a i) v ξ η + (potS T a ((A.e i).symm v) : ℂ) * chernOne (quotIn T a i) v ξ η +
    (potQ T a ((A.e i).symm v) : ℂ) * chernOne (fun w => subGram (midIn T a i w)) v ξ η

def frm (T : HermSeq A 1 1) (y : M) : T.κ := (T.cover y).choose

def secForm (T : HermSeq A 1 1) : A.Fld := fun x => (ofValues (locForm T (frm T x.pt) x.1.1 x.crd) : Alt n)

variable (T : HermSeq A 1 1) (a b : T.κ) (i : A.ι)

def chartSet : Set (V n) := (A.e i).target ∩ (A.e i).symm ⁻¹' T.U a

def gIn (v : V n) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := T.g a b ((A.e i).symm v)

theorem isOpen_chartSet : IsOpen (chartSet T a i) := (A.e i).isOpen_inter_preimage_symm (T.isOpen a)

theorem isPosFrame_midIn : IsPosFrame (chartSet T a i) (midIn T a i) :=
  ⟨isOpen_chartSet T a i, fun p q => (T.smooth a).2.1 p q i, fun _ hv => (T.posDef a _ hv.2).2.1⟩

theorem holo_gIn {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    MContDiffAt ∞ (gIn T a b i) v ∧ ∀ᶠ w in 𝓝 v, ∀ η, mdbar (gIn T a b i) w η = 0 := by
  have hs : chartSet T a i ∩ chartSet T b i = (A.e i).target ∩ (A.e i).symm ⁻¹' (T.U a ∩ T.U b) := by
    ext w; simp only [chartSet, mem_inter_iff, mem_preimage]; tauto
  have ho : IsOpen (chartSet T a i ∩ chartSet T b i) := (isOpen_chartSet T a i).inter (isOpen_chartSet T b i)
  have hd : ∀ p q, DifferentiableOn ℂ (fun w => gIn T a b i w p q) (chartSet T a i ∩ chartSet T b i) := by
    intro p q; rw [hs]; exact T.holo a b p q i
  refine ⟨fun p q => ?_, ?_⟩
  · have h1 : ContDiffOn ℂ ∞ (fun w => gIn T a b i w p q) (chartSet T a i ∩ chartSet T b i) :=
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ ho (hd p q)
    exact (h1.restrict_scalars ℝ).contDiffAt (ho.mem_nhds hv)
  filter_upwards [ho.mem_nhds hv] with w hw η
  ext p q
  rw [mdbar_apply, dbar_eq_zero ((hd p q).differentiableAt (ho.mem_nhds hw))]
  rfl

theorem trans_eventually {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    ∀ᶠ w in 𝓝 v, w ∈ chartSet T a i ∩ chartSet T b i ∧
      subIn T b i w = chg (gIn T a b i w).toBlocks₁₁ (subIn T a i w) ∧
      midIn T b i w = chg (gIn T a b i w) (midIn T a i w) ∧
      quotIn T b i w = chg (gIn T a b i w).toBlocks₂₂ (quotIn T a i w) ∧
      (gIn T a b i w).toBlocks₂₁ = 0 := by
  have ho : IsOpen (chartSet T a i ∩ chartSet T b i) := (isOpen_chartSet T a i).inter (isOpen_chartSet T b i)
  filter_upwards [ho.mem_nhds hv] with w hw
  have h := T.trans a b _ ⟨hw.1.2, hw.2.2⟩
  exact ⟨hw, h.1, h.2.1, h.2.2, T.tri a b _ ⟨hw.1.2, hw.2.2⟩⟩

end GlobalTheory.SecForm
