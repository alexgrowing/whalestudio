import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsKCRT
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsClosed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rhoSurj_X : Function.Surjective (AllRowsRhoX.rhoX X) := Formalism.L2.SG.Pf.RhoSurjW.reduction_map_surjective D X

theorem redKerOne_holds : RedKerOne X := redKerOne_of (X := X) (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)

theorem etUniv_holds : EtUniv X := etUniv_of (X := X) (redKer_of (X := X) (redKerOne_holds X))

theorem etUnip_holds (k : Fin 2) (S : Set (Tup D k)) : EtUnip X k S := etUnip_of (X := X) k (AllRowsRedKer.redKerP_holds X (1 - k)) S

theorem kppShape_holds : AllRowsKpp.KppShape X := Formalism.L2.SG.Pf.AllRowsKpp.kppShape_of_fwd (X := X) (rhoSurj_X X) (Formalism.L2.SG.Pf.KppFwdPf.kppFwd_holds (X := X))

theorem etAlg_holds (S : Set (Tup2 D)) : EtAlg X S := Formalism.L2.SG.Pf.AllRowsEtAlg.etAlg_of (X := X) (rhoSurj_X X) S

theorem etOne_holds (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) : EtOne X ψ₀ := Formalism.L2.SG.Pf.AllRowsEtOne.etOne_of (X := X) (rhoSurj_X X) (kppShape_holds X) ψ₀ hψ₀

theorem isAdmIdem_cyl (k : Fin 2) (S : Set (Tup D k)) :
    X.B.I.IsAdmIdem X.B.μf X.B.g (D.host.g (1 - k)) (eT X (cyl D k S)) := isAdmIdem_eT_cyl (X := X) k S (etAlg_holds X (cyl D k S)) (etUnip_holds X k S)

theorem kcrt_g (k : Fin 2) : KCRT X.B.I (D.host.g (1 - k)) (D.host.g k) := by
  refine AllRowsKCRT.kcrt_holds X.B.I ((Nat.coprime_primes (D.host.g_prime _) (D.host.g_prime _)).2 ?_)
  fin_cases k
  · exact D.host.g_ne.symm
  · exact D.host.g_ne

def allRowsOfL (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X) : AllRows D :=
  allRowsOfP X ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1) (etOne_holds X ψ₀ hψ₀) hL

theorem admissibleCount_allRows_level (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ) (hψ₀ : ∀ k, ψ₀ k ≠ 1) (hL : RowsLab X)
    {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (hC1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb) (hL6 : ConclusionL D)
    (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) (hB : CountBase X n₀ Alev C₃ cb)
    (hP : Formalism.MainNotions.N.CylinderCountFamily.PCountTie D (allRowsOfL X ψ₀ hψ₀ hL).toAt) (hAd : TieAdmG D) :
    Formalism.MainNotions.N.CylinderCountFamily.CylinderCountUniformAt D (allRowsOfL X ψ₀ hψ₀ hL).toAt n₀ Alev C₃ c₃ cb 6 := admissibleCount_allRows_partner (X := X) ψ₀ (AllRowsRedKer.redKerP_holds X 0) (AllRowsRedKer.redKerP_holds X 1)
  (etOne_holds X ψ₀ hψ₀) hL hψ₀ hC1 hL6 hg hB (fun k S => etAlg_holds X (cyl D k S)) hP hAd

end Formalism.L2.SG.Pf.AllRowsClosed
