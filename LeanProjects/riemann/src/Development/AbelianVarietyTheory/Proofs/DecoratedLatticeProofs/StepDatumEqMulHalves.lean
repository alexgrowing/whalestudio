import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwisted
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DatumHalves

variable {D : D7}

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  simp

theorem omegaG_of_empty {a b : ℕ} (L : LevDat D.host.E ℂ a) (hL : L.Pg = ∅) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaG L χj y = 1 := by
  have hn : ∀ PP, PP ∉ L.Pg := fun PP h => Finset.notMem_empty PP (hL ▸ h)
  haveI : IsEmpty ↥L.Pg := ⟨fun PP => hn PP.1 PP.2⟩
  have h1 : ∀ g : G0 L.Pg L.r, g = 1 := fun g => funext fun PP => isEmptyElim PP
  have h2 : ∀ g : L.P.H, L.P.chi g = 1 := fun g => by
    rw [show g = 1 from Subtype.ext (h1 _), map_one]
  unfold omegaG
  rw [dif_pos ⟨fun PP h => absurd h (hn PP), fun PP => isEmptyElim PP, fun PP => isEmptyElim PP, fun PP => isEmptyElim PP,
    by rw [h1 (fun PP => _)]; exact L.P.H.one_mem⟩, h2, Fintype.prod_empty, Fintype.prod_empty]
  simp

theorem omegaG_datY {n b : ℕ} (r t j : ℕ) (hr : r ≤ n) (Pg Q Q' : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin n) (kP PP)) :
    omegaG (datY n r t j hr Pg Q P χ ξ Frm.B) χj y = omegaG (datY n r t j hr Pg Q' P χ ξ' Frm.B) χj y := rfl

theorem isHalf_smul {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S T : HSp D} (x : WO S T) :
    IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, GlobalTheory.PlaceDatum.idemSum_mul_self he]

set_option maxHeartbeats 800000 in

theorem stepDatum_eq_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  intro D S T βS βT r t j hr Pg Q P χ χj ξ eG eQ hG hQ _ x
  obtain ⟨iG, rG⟩ := GlobalTheory.InnerSteps.resS_idemSum hG
  obtain ⟨iQ, rQ⟩ := GlobalTheory.InnerSteps.resS_idemSum hQ
  have hsm : ∀ e : AE D, frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x :=
    fun e => GlobalTheory.RedHalfDrop.frMapO_smul_eq βS βT e x
  have hhG : IsHalf eG (eG • x) := isHalf_smul hG x
  have hhQ : IsHalf eQ (eQ • x) := isHalf_smul hQ x
  by_cases hx : IsHalf (eG + eQ) x
  swap
  · rw [if_neg hx, if_neg (fun h => hx h.1), mul_zero]
  have hxx : (eG + eQ) • x = x := funext fun a => funext fun b => hx a b
  have hNs := hsm (eG + eQ)
  rw [hxx, RingHom.map_add, add_smul] at hNs
  rw [if_pos hx, hsm, hsm]
  generalize frMapO S T βS βT x = N at hNs ⊢
  by_cases hI : IsIntM N
  · have iGN : IsIntM (toEAf D eG • N) := fun a b => mul_mem iG (hI a b)
    have iQN : IsIntM (toEAf D eQ • N) := fun a b => mul_mem iQ (hI a b)
    have e1 := GlobalTheory.PlaceDatum.omegaG_congr (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj
      (fun PP => redM PP (toEAf D eG • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iG PP (rG PP hPP) hI)
    have e2 := GlobalTheory.PlaceDatum.omegaQ_congr Q r ξ 1 (fun PP => redM PP (toEAf D eQ • N)) (fun PP => redM PP N)
      (fun PP hPP => GlobalTheory.LocSuppTw.redM_smul_of_res iQ PP (rQ PP hPP) hI)
    rw [if_pos (And.intro hx hI), if_pos (And.intro hhG iGN), if_pos (And.intro hhQ iQN), omegaQ_empty,
      omegaG_of_empty (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) rfl, e1, mul_one, mul_one, one_mul,
      omegaG_datY r t j hr Pg Q ∅ P χ ξ (fun _ => 1)]
    exact congrArg _ e2.symm
  · rw [if_neg (fun h : IsHalf (eG + eQ) x ∧ IsIntM N => hI h.2)]
    by_cases h1 : IsIntM (toEAf D eG • N)
    · have h2 : ¬ IsIntM (toEAf D eQ • N) := fun h2 => hI fun a b => by
        have e : N a b = (toEAf D eG • N) a b + (toEAf D eQ • N) a b := congrFun (congrFun hNs a) b
        exact e.symm ▸ Subring.add_mem _ (h1 a b) (h2 a b)
      rw [if_neg (fun k : IsHalf eQ (eQ • x) ∧ IsIntM (toEAf D eQ • N) => h2 k.2), mul_zero, zero_mul]
    · rw [if_neg (fun k : IsHalf eG (eG • x) ∧ IsIntM (toEAf D eG • N) => h1 k.2), zero_mul, zero_mul]

end GlobalTheory.DatumHalves
