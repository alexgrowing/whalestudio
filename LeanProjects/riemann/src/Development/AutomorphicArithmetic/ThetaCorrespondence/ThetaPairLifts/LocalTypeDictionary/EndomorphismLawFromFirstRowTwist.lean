import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFirstRowScalarMultiple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLawsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData
open GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FirstRowEndLaw
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {Γ : Grid k}
end Local
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
set_option maxHeartbeats 1600000 in
theorem square_identity_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (a : Fin ch.n) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∃ lam : locPl ch.G t → ℂ,
        (∀ w : locPl ch.G t, (locGrid ch.G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (Tflip ch.W ch.S.B t (ch.Phi a) w) =
          lam w • Tflip ch.W ch.S.B t (ch.Phi a) w) ∧
        (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c * ∏ w, lam w =
          ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  intro hP hS
  obtain ⟨CF0, hsc⟩ := _root_.GlobalTheory.T.twist_firstRow_scalar_multiple hP hS
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hsc⟩ := hsc ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hat => ?_⟩
  have hs := hsc D large₂ he hx Γ Pl0 T A Ks R F s ch hch hat
  intro t a k hk hk' c hc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := pde_ne_q' s
  have hcg : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  refine ⟨fun w => endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k), fun w => ?_, hs t k hk hk' c hc⟩
  exact Tflip_law hL ch.W ch.S.B t (ch.Phi a) hde hcg w.2 _ (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w)
end GlobalTheory.FirstRowEndLaw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_law_from_first_row_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (a : Fin ch.n) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∃ lam : locPl ch.G t → ℂ,
        (∀ w : locPl ch.G t, (locGrid ch.G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (Tflip ch.W ch.S.B t (ch.Phi a) w) =
          lam w • Tflip ch.W ch.S.B t (ch.Phi a) w) ∧
        (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c * ∏ w, lam w =
          ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @_root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction | exact _root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction | (intros; apply _root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction <;> assumption)
end
