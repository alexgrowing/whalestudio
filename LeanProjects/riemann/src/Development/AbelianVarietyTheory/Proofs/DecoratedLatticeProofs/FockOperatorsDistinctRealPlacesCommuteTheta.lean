import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceComm

open GlobalTheory.OrientedHeis (theta_add theta_smul theta_dRho)

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_comm {B : (X → ℂ) → (X → ℂ)} (hA : ∀ i f, P f → P (A i f))
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    B (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A i g) (B f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [hBA _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l), ih]

theorem pure_comm {B : (X → ℂ) → (X → ℂ)} (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Badd : ∀ f f', P f → P f' → B (f + f') = B f + B f') (Bsm : ∀ (a : ℂ) f, P f → B (a • f) = a • B f)
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    B (pureTensorL A f Q) = pureTensorL A (B f) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [Bsm _ _ (GlobalTheory.FockIndep.foldr_mem hA hf _), foldr_comm hA hBA hf]
  | add p q hp hq =>
    rw [map_add, map_add, Badd _ _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _) (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _),
      hp, hq]

theorem pure_fun_add (hA : ∀ i f, P f → P (A i f)) (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f') {f f' : X → ℂ} (hf : P f) (hf' : P f')
    (Q : MvPolynomial ι ℂ) : pureTensorL A (f + f') Q = pureTensorL A f Q + pureTensorL A f' Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (f + f') =
      l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Aadd _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_add]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
    abel

theorem pure_fun_smul (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (a : ℂ) {f : X → ℂ} (hf : P f)
    (Q : MvPolynomial ι ℂ) : pureTensorL A (a • f) Q = a • pureTensorL A f Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (a • f) = a • l.foldr (fun i g => A i g) f := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Asm _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_comm]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, smul_add]

end Generic

section Places

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ ≠ τ')
include hψ hθ hne

theorem dRho_comm_ne (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) =
      Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) := by
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' z' hf]
  simp [GlobalTheory.FockIndep.omDir, hne]

theorem dRho_aPlus_ne (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (aPlus (heisO ψ S T) θ τ' J u f) =
      aPlus (heisO ψ S T) θ τ' J u (Datum.dRho (heisO ψ S T) θ τ z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq,
    GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    GlobalTheory.FockIndep.dRho_add hψ hθ _ _ (ht _ _) (theta_smul _ (ht _ _)), GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (ht _ _),
    dRho_comm_ne hψ hθ hne _ _ hf, dRho_comm_ne hψ hθ hne _ _ hf]

theorem aPlus_comm_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (aPlus (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq τ J z (aPlus (heisO ψ S T) θ τ' J' u f), dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    dRho_aPlus_ne hψ hθ hne _ _ _ hf, ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))), ← GlobalTheory.FockIndep.aPlus_eq]

theorem annih_aPlus_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (annih (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [annih, annih, dRho_aPlus_ne hψ hθ hne _ _ _ hf, dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _))]

end Places

section Weil

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hW : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
  {τ τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'))
include hW hθ hne hg

theorem om_dRho_fix (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (Datum.dRho (heisO ψ V W) θ τ z f) =
      Datum.dRho (heisO ψ V W) θ τ z (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hW hθ _ _ τ z hf]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V (atTau θ V τ' g)) = 1 :=
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hg).2.2 τ hne
  have h3 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ (atTau θ V τ' g)
  rw [h2, Matrix.one_mul] at h3
  rw [h1, h3, Matrix.one_mul, Matrix.mul_one]

theorem om_aPlus_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (aPlus (heisO ψ V W) θ τ J u f) = aPlus (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq, map_smul, map_add, map_smul, om_dRho_fix hW hθ hne hg _ hf,
    om_dRho_fix hW hθ hne hg _ hf]

theorem om_annih_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (annih (heisO ψ V W) θ τ J u f) = annih (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [annih, annih, map_add, map_smul, om_dRho_fix hW hθ hne hg _ hf, om_dRho_fix hW hθ hne hg _ hf]

end Weil

theorem twoPlace_comm : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hW τ τ' hne F hF
  dsimp only
  have hψ := hW.std
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ ρ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g) :=
    fun ρ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ ρ _ _ h
  have Aadd : ∀ ρ (k : Fin W.rank × Fin V.rank) g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (g + g') =
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g +
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g' :=
    fun ρ _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ ρ _ _ h h'
  have Asm : ∀ ρ (k : Fin W.rank × Fin V.rank) (a : ℂ) g, IsThetaFunO ψ V W g →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (a • g) =
      a • aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g :=
    fun ρ _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ ρ _ _ a h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt
  refine ⟨fun P => GlobalTheory.FockIndep.pure_mem hadd hsm (hA τ') hF P, fun P hv z => ?_, fun P Q => ?_, fun g hg => ⟨?_, ?_⟩⟩
  · rw [pure_comm hadd hsm (hA τ') (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ τ _ z h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z a h)
      (fun k g hg => annih_aPlus_ne hψ hθ hne _ _ _ _ hg) hF P, hv z]
    have h0 := pure_fun_smul (hA τ') (Asm τ') 0 hF P
    rwa [zero_smul, zero_smul] at h0
  · symm
    refine pure_comm (B := fun g => pureTensorL (fun k : Fin W.rank × Fin V.rank =>
        aPlus (heisO ψ V W) θ τ' (cplxO (cart M τ') (cart M' τ')) (unitMap (onb M τ') (onb M' τ') k.1 k.2)) g Q)
      hadd hsm (hA τ) (fun _ _ h h' => pure_fun_add (hA τ') hadd hsm (Aadd τ') h h' Q)
      (fun a _ h => pure_fun_smul (hA τ') (Asm τ') a h Q) (fun k g hg => ?_) hF P
    exact (pure_comm hadd hsm (hA τ') (Aadd τ k) (Asm τ k)
      (fun j h hh => aPlus_comm_ne hψ hθ hne _ _ _ _ hh) hg Q).symm
  · intro hv z
    rw [← om_annih_fix hW hθ hne hg _ _ hF, hv z, map_zero]
  · intro P
    exact pure_comm hadd hsm (hA τ) (fun f f' _ _ => map_add _ f f') (fun a f _ => map_smul _ a f)
      (fun k h hh => om_aPlus_fix hW hθ hne hg _ _ hh) hF P

end GlobalTheory.TwoPlaceComm

end
