import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.FinsumQuotLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) : V.relIndex (K2 a b w) ≠ 0 := by
  have hK : IsCompact ((K2 a b w : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)) := by
    have := (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)
    simpa [K2, Subgroup.coe_prod] using this
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hV hK

theorem idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (v * g0) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hv hg), Set.indicator_of_mem hg]
  · have : v * g0 ∉ V := fun h => hg (by simpa using V.mul_mem (V.inv_mem hv) h)
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} {v : GLw a w × GLw b w} (hv : v ∈ V)
    (g0 : GLw a w × GLw b w) : idem V (g0 * v) = idem V g0 := by
  unfold idem
  by_cases hg : g0 ∈ V
  · rw [Set.indicator_of_mem (V.mul_mem hg hv), Set.indicator_of_mem hg]
  · have : g0 * v ∉ V := fun h => hg (by simpa using V.mul_mem h (V.inv_mem hv))
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem mconv_zero_left {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv (fun _ => (0 : ℂ)) f = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))

theorem mconv_zero_right {w : Pl E} (f : GLw a w × GLw b w → ℂ) :
    mconv f (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext m
  unfold mconv
  simpa using FinConv.hint_zero ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))

theorem mconv_left {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hf : ∀ x, f (v * x) = f x)
    (m : GLw a w × GLw b w) : mconv f g (v * m) = mconv f g m := by
  unfold mconv
  calc hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun m' => f m' * g (m'⁻¹ * (v * m)))
      = hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b))
          (fun z => (fun z => f (v * z) * g (z⁻¹ * m)) (v⁻¹ * z)) := by
        congr 1; funext z; simp [mul_assoc]
    _ = hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (fun z => f (v * z) * g (z⁻¹ * m)) :=
        FinConv.hint_left _ (fun z => f (v * z) * g (z⁻¹ * m)) v⁻¹
    _ = _ := by congr 1; funext z; rw [hf]

theorem mconv_right {w : Pl E} {f g : GLw a w × GLw b w → ℂ} {v : GLw a w × GLw b w} (hg : ∀ x, g (x * v) = g x)
    (m : GLw a w × GLw b w) : mconv f g (m * v) = mconv f g m := by
  unfold mconv
  congr 1; funext z; rw [← mul_assoc, hg]

theorem mconv_idem_left {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (v * x) = f x) :
    mconv (idem V) f = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => idem V m' * f (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [idem_right hk, _root_.mul_inv_rev, mul_assoc, hf _ (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk 1 → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (by simpa using V.inv_mem hm)
    unfold idem
    rw [Set.indicator_of_notMem this, zero_mul]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk 1 : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) u = f m
  rw [show ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk 1) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V (1 : GLw a w × GLw b w)
  simp only [hu]
  rw [e, one_mul]
  unfold idem
  rw [Set.indicator_of_mem hh.2, hf _ (V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

theorem mconv_idem_right {w : Pl E} {V : Subgroup (GLw a w × GLw b w)} (hV : IsOpen (V : Set (GLw a w × GLw b w)))
    (hle : V ≤ K2 a b w) {f : GLw a w × GLw b w → ℂ} (hf : ∀ v ∈ V, ∀ x, f (x * v) = f x) :
    mconv f (idem V) = f := by
  funext m
  have hr := relIndex_ne hV hle
  set u : GLw a w × GLw b w → ℂ := fun m' => f m' * idem V (m'⁻¹ * m) with hu
  have hSu : V ≤ rStab u := by
    intro k hk x
    simp only [hu]
    rw [hf _ hk, _root_.mul_inv_rev, mul_assoc, idem_left (V.inv_mem hk)]
  have hsupp : ∀ q : (GLw a w × GLw b w) ⧸ V, q ≠ QuotientGroup.mk m → u q.out = 0 := by
    intro q hq
    simp only [hu]
    have : q.out⁻¹ * m ∉ V := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 hm
    unfold idem
    rw [Set.indicator_of_notMem this, mul_zero]
  have hfin : (Function.support fun q : (GLw a w × GLw b w) ⧸ V => u q.out).Finite := by
    refine (Set.finite_singleton (QuotientGroup.mk m : (GLw a w × GLw b w) ⧸ V)).subset fun q hq => ?_
    by_contra hne
    exact hq (hsupp q hne)
  have h := PositivityTheory.Rg.BcN.F2.LocOpPf.hinteq (K2 a b w) V u hle hSu hr hfin
  change hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) u = f m
  rw [show ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) = K2 a b w from rfl, h,
    finsum_eq_single _ (QuotientGroup.mk m) hsupp]
  obtain ⟨hh, e⟩ := QuotientGroup.mk_out_eq_mul V m
  simp only [hu]
  rw [e, hf _ hh.2]
  unfold idem
  rw [Set.indicator_of_mem (by simpa using V.inv_mem hh.2)]
  have : ((V.relIndex (K2 a b w) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr
  field_simp

end PositivityTheory.Rg.BcB.F.FA.MatrixConvolutionPowers

end
