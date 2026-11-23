import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem position_off {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w i : Pl E} (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (hi : i ≠ w) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e i = intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i := by
  simp [intersection_update_fsHerm_neg_one, hi]

private theorem position_at {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z)
    {w : Pl E} (hZ : w ∉ Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) :
    intersection_update_fsHerm_neg_one Z {w} L.ln e w = fn2 a b w (e w) := by
  simp [intersection_update_fsHerm_neg_one, hZ]

private theorem position_cof {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {Z : Finset (Pl E)} (L : Lv a b Z) :
    ∀ᶠ i in cofinite, intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one) i = ((K2 a b i : Subgroup _) : Set _).indicator 1 := by
  filter_upwards [Z.finite_toSet.compl_mem_cofinite] with i hi
  have hi' : i ∉ Z := hi
  simp [intersection_update_fsHerm_neg_one, hi']

private theorem fin_split {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E)) {Z : Finset (Pl E)}
    (L : Lv a b Z) {w : Pl E} (hw : w ∈ S) (hZ : w ∉ Z) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (y : Gf E a b) :
    finFn S (intersection_update_fsHerm_neg_one Z {w} L.ln e₁) (intersection_update_fsHerm_neg_one Z {w} L.ln e₂) y =
      (fn2 a b w (e₁ w) (atW w y) * if IsSplitAt w then fn2 a b w (e₂ w) (atW w (thP E a b y)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) y i := by
  rw [Fm.finFn_eq, Fm.fp_split S {w} (by simpa using hw) _ _ (fun i hi => ?_)
    (Fm.fac_fin S (position_cof L) (position_cof L) y)]
  · congr 1
    simp [Fm.fac, position_at L hZ]
  · have hi' : i ≠ w := by simpa using hi
    simp only [Fm.fac, position_off L _ hi']

private theorem ex_add {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (x y : Ex ι) (h : G) :
    (x.add y).fn K g h = x.fn K g h + y.fn K g h := rfl

private theorem ex_smul {ι G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) (c : ℂ) (x : Ex ι) (h : G) :
    (Ex.smul c x).fn K g h = c * x.fn K g h := rfl

theorem hkLin : HkLin := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ' w hw hZ x y z c
  have key : ∀ (e₁ e₂ : Ex (Fin (a + 1) × Fin (b + 1))) (u v : Unit) (h : Hf E a b), A.hk S L {w} (fun _ => e₁) (fun _ => e₂) u v h =
      A.blk.vol⁻¹ * ((fn2 a b w e₁ (atW w h) * if IsSplitAt w then fn2 a b w e₂ (atW w (thP E a b h)) else 1) *
        ∏ᶠ i ∈ S \ ↑({w} : Finset (Pl E)), Fm.fac (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) (intersection_update_fsHerm_neg_one Z ∅ L.ln (fun _ => .one)) h i) := by
    intro e₁ e₂ u v h
    exact congrArg _ (fin_split S L hw hZ _ _ h)
  refine ⟨?_, ?_, fun hs => ⟨?_, ?_⟩, fun hs => ?_⟩ <;> funext u v h
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul]; ring
  · simp only [Matrix.add_apply, Pi.add_apply, key, fn2, ex_add, if_pos hs]; ring
  · simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, key, fn2, ex_smul, if_pos hs]; ring
  · simp only [key, if_neg hs]

end UpperTheory.Zero.ConvolutionTheory.EB
