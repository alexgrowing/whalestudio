import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacTIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StabMoveTup

theorem unramAt_of_chrEq_mul {D : D7} {c : (AE D)ˣ →* Circle} {χ ξ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c (χ * ξ))
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    (hξ : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ ξ.UnrAt P → IsSplitPl D.host P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c _ hc v ε hv.1 fun P hP => Formalism.L2.Host.HChar.UnrAt.mul (hu P fun k hk => ?_) ?_
  · obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP
  · by_contra hn
    obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem (hξ P hn)
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem moveT_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  intro B X I hI hPins l Z ψ θ hψ hθ i hi vac hvac a μ om hchr hW c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hPins l Z ψ θ hψ hθ).1 i hi
  have b := StabMove.intG_of_moves _ mk
  have b' := StabMove.intG_of_moves _ mk'
  have a₁ := b.inv hP.gS
  have a₁' := b'.inv hP.gT
  rw [inv_inv] at a₁ a₁'
  have hξ : ∀ P, ¬ (I.xi a).UnrAt P → IsSplitPl B.host P := fun P hn =>
    ((GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host B.fields.K B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1.2.2.2 P hn).1
  obtain ⟨x₁, y₁, rx, ry, e⟩ := StabMove.om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq_mul hchr (I.C.isMu0 ⟨i, hi⟩).unr hξ hv) hvac hk hk' a₁ a₁'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (StabMove.moves_of_mul _ a₁ b hN) (StabMove.moves_of_mul _ a₁' b' hN') x₀ y₀ sx sy
  have ex := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (GlobalTheory.AdForm.VacAll.xiS_smul _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMoveTup
