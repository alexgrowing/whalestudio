import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have key : ∀ S : Subgroup H, S = ⊤ → ((S.index : ℂ))⁻¹ * ∑ᶠ _ : H ⧸ S, c = c := by
    rintro S rfl
    haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    haveI : Unique (H ⧸ (⊤ : Subgroup H)) := Unique.mk' _
    rw [finsum_unique, Subgroup.index_top]
    simp
  exact key _ (by ext k; simp [rStab])

theorem ctT_split_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  intro E _ _ _ n a b h w ν ϖ hw hϖ k m
  have hT : UL n w = ⊤ := if_pos hw
  have hv : ∀ y : GLw n w, ((toSub (UL n w) y : UL n w) : GLw n w) = y := fun y => by
    have hy : y ∈ UL n w := hT ▸ Subgroup.mem_top y
    simp [toSub, hy]
  have hc : ∀ (x : GLw n w) (g : GlobalTheory.LFun.KGL w n),
      Tj ℂ n (Ov E w) ϖ k ((g : GLw n w)⁻¹ * x * g) = Tj ℂ n (Ov E w) ϖ k x := fun x g =>
    (Tj_mem_hecke (n := n) hϖ k).1 g⁻¹ g x
  unfold ctT ctMu ct
  congr 2
  congr 1
  funext X
  simp only [hv, hc]
  exact avg_const _

end GlobalTheory.CompanionTheory.CtS

end
