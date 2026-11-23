import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemOfListProdMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

set_option maxHeartbeats 1600000 in

theorem intC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  intro hL hDec hI hT hRT
  refine ((GlobalTheory.T.hecke_reading_eigenvalue_place hL hDec hI hT hRT).and (formsC_at_state hL)).trans
    (StepW.of_all fun K B f T w _ _ H P x hA θ hL' _ hstab hrd => ?_)
  obtain ⟨hB, hF⟩ := H
  intro j k Pl hj1 hj2 hsp hnot hk
  obtain ⟨-, -, Tf, hTf, hMK, hspan⟩ := hF P x hA j hj1 hj2
  obtain ⟨p, hp, hpP, hpN⟩ := GlobalTheory.SupPowNorm.exists_prime_dvd_card Pl
  have hW : ∀ y ∈ ((SOf x).A j).WK, hL' j k Pl y ∈ ((SOf x).A j).WK := fun y hy => hstab j hj1 hj2 k Pl y hy
  obtain ⟨n, hn⟩ := GlobalTheory.SupPowNorm.exists_pow_smul_mem_span ((SOf x).A j) (hL' j k Pl) Tf hTf
    (fun y hy => (hMK y hy).2) hspan hW hp hpN fun la hla g hg hb y =>
      hB P x hA hL' hstab hrd j k Pl hj1 hj2 hsp hnot hk la
        (fun q hq hqP => by rw [GlobalTheory.SupPowNorm.prime_eq_of_mem Pl hq hp hqP hpP]; exact hla) g hg (hW g hg) hb y
  exact ⟨n, fun y hy _ => hn y hy⟩

end GlobalTheory.HeightCounting.RatSide
