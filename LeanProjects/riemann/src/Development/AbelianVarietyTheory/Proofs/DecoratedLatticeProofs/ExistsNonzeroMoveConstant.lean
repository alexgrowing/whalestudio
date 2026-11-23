import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPairStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.VacBase

theorem vacuum_reads_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ c₀ : ℂ, c₀ ≠ 0 ∧ A.MoveAt θ i hi c₀ 1 1 := by
  intro B X I l Z w u A ψ θ hA i hi
  obtain ⟨hstd, -, -, -⟩ := GlobalTheory.T.standard_pair_along_chain I l Z w u A ψ θ hA i hi
  have key := GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd (A.chr (i + 1)) (A.om i) (hA.om i hi) (A.vac i) (hA.vac i hi) 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := GlobalTheory.T.adelicTranslate_one_eq_standardLattice
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := GlobalTheory.T.character_eq_one_of_isDetRoot_of_even
  have S3 : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))),
      ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i))
        (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := GlobalTheory.T.lattice_chain_standard_pair I l Z w i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : A.chr (i + 1) x = 1 := S2 _ _ _ (hA.om i hi).resS hstd.rk.2.2.1 _ x hx
      have hy1 : A.chr (i + 1) y = 1 := S2 _ _ _ (hA.om i hi).resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacBase
