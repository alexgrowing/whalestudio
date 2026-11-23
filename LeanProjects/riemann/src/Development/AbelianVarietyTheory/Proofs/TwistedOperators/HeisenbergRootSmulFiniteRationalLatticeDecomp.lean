import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MultLatDecomp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem heisO_eq_root_smul_finRat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf n hn w hw
  classical
  have hinf : w.map (infPart D) = 0 := by
    have h1 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hw
    funext i j
    have h2 : infPart D ((n • w) i j) = 0 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, map_nsmul] at h2
    have hn' : (n : D.host.F) ≠ 0 := by exact_mod_cast hn.ne'
    have h3 : (n : D.host.F) • infPart D (w i j) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h2
    show infPart D (w i j) = 0
    rw [← inv_smul_smul₀ hn' (infPart D (w i j)), h3, smul_zero]
  obtain ⟨M, u, hu, hM⟩ := GlobalTheory.LatVac.approx hS hT w
  have hw_eq : w = GlobalTheory.VacUnique.finRat S T M + u := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · have h1 : infPart D (w i j) = 0 := congrFun (congrFun hinf i) j
      have h2 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 :=
        congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, h1, h2, GlobalTheory.LatVac.infPart_of_mem hu, add_zero,
        sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, hM, sub_eq_zero]
      rfl
  have hmem : GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    have e : GlobalTheory.VacUnique.finRat S T (n • M) = n • w - n • u := by
      rw [map_nsmul, hw_eq, smul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem hw (nsmul_mem hu n)
  obtain ⟨ε, hε, hεf⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).2.2 f hf u hu
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ (GlobalTheory.VacUnique.finRat S T M) u f
  rw [hεf f hf, GlobalTheory.LatVac.heisO_smul] at h1
  have hinv : ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) = 1 := by
    rw [← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one]
  have hX : ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) =
      ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) := by
    rw [← ψ.map_add_eq_mul, symplOH, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
  have hY : ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have e : n • symplO S T (GlobalTheory.VacUnique.finRat S T M) u = symplO S T (GlobalTheory.VacUnique.finRat S T (n • M)) u := by
      change n • GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T M) u =
        GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T (n • M)) u
      rw [map_nsmul (GlobalTheory.VacUnique.finRat S T), map_nsmul (GlobalTheory.LatVac.symplHom S T), AddMonoidHom.nsmul_apply]
    rw [e]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hmem hu
  have e1 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n = 1 := by
    rw [hX]; exact hY
  refine ⟨M, ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u), ⟨2 * n, by omega, ?_⟩, hmem, ?_⟩
  · calc (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n)
        = (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n) *
          (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n := by
          rw [e2, mul_one]
      _ = (ε ^ 2) ^ n * ((ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) *
          ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ 2) ^ n := by ring
      _ = 1 := by rw [e1, hinv]; simp
  · rw [hw_eq, mul_comm, mul_smul, h1, smul_smul, hinv, one_smul]

end GlobalTheory.MultLatDecomp

end
