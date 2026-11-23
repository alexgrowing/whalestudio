import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x

def IsWittStep (B B' : HSp D) (t : ℕ) (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) : Prop :=
  B'.rank + 2 * t = B.rank ∧ HSpace.IsIsomEmb B' B ι ∧ IsIsoSub B C ∧ ct (frameMat B B' ι) * B.gram * C = 0

theorem isWittLower_iff (B B' : HSp D) (t : ℕ) : IsWittLower B B' t ↔ ∃ ι C, IsWittStep B B' t ι C :=
  ⟨fun ⟨h, ι, h1, C, h2, h3⟩ => ⟨ι, C, h, h1, h2, h3⟩, fun ⟨ι, C, h, h1, h2, h3⟩ => ⟨h, ι, h1, C, h2, h3⟩⟩

theorem exists_isWittStep_iff (B : HSp D) (t : ℕ) :
    (∃ B' ι C, IsWittStep B B' t ι C ∧ B'.SigOK) ↔ t ≤ GlobalTheory.Cusp.wittIndex B := by
  rw [← GlobalTheory.Cusp.exists_isWittLower_iff]
  exact ⟨fun ⟨B', ι, C, h, h'⟩ => ⟨B', (isWittLower_iff _ _ _).2 ⟨ι, C, h⟩, h'⟩,
    fun ⟨B', h, h'⟩ => let ⟨ι, C, h⟩ := (isWittLower_iff _ _ _).1 h; ⟨B', ι, C, h, h'⟩⟩

theorem IsWittStep.isIsoFrame {B B' : HSp D} {t : ℕ} {ι : B'.V →ₗ[D.host.E] B.V}
    {C : Matrix (Fin B.rank) (Fin t) D.host.E} (h : IsWittStep B B' t ι C) (ht : 1 ≤ t) : IsIsoFrame B C :=
  ⟨ht, h.2.2.1.1, h.2.2.1.2⟩

def IsLeviElt (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E)
    (a : GL (Fin t) (AE D)) (h' : GA D B') (m : GA D B) : Prop :=
  HMul.hMul (Formalism.L2.Theta.mt B m) (adel C) = HMul.hMul (adel C) a.val ∧
    HMul.hMul (Formalism.L2.Theta.mt B m) (adel (frameMat B B' ι)) =
      HMul.hMul (adel (frameMat B B' ι)) (Formalism.L2.Theta.mt B' h')

def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def IsRapidCusp (A : HSp D) (f : GA D A → ℂ) : Prop := GlobalTheory.Grow.RapidDec A f ∧ IsCuspFun A f

def IsQuotMeas (A : HSp D) (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ A) 𝓕 ν

abbrev Rep (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

def IsWeilRep (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ S T χS χT om

def HasConstS (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (om : Rep S T) (τ : D.what₂.Tau) (κ : ℝ) :
    Prop :=
  ∀ (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
    IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT →
    ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f →
    ∀ X ∈ lieAt S τ, X * sS = sS * X → ∀ g, IsAtTau θ S τ (NormedSpace.exp X) g →
      om (g, 1) f = Complex.exp (-(sT.trace / 2 * (sS * X).trace + (κ : ℂ) * X.trace)) • f

def HasConstT (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (om : Rep S T) (τ : D.what₂.Tau) (κ : ℝ) :
    Prop :=
  ∀ (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
    IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT →
    ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f →
    ∀ X ∈ lieAt T τ, X * sT = sT * X → ∀ h, IsAtTau θ T τ (NormedSpace.exp X) h →
      om (1, h) f = Complex.exp (sS.trace / 2 * (sT * X).trace + (κ : ℂ) * X.trace) • f

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)

def resT (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ :=
  fun w' => ∫ y in 𝓖, φ (adel C * (y : Matrix (Fin t) (Fin S.rank) (AE D)) +
    adel (frameMat T T' ι) * (w' : Matrix (Fin T'.rank) (Fin S.rank) (AE D))) ∂μ

def CompatT (om : Rep S T) (om' : Rep S T') : Prop :=
  ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 → ∀ (g : GA D S) φ, IsThetaFunO ψ S T φ →
    resT S T T' ι C μ 𝓖 (om (g, 1) φ) = om' (g, 1) (resT S T T' ι C μ 𝓖 φ)

def liftT {S T : HSp D} (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (om : Rep S T) (f : GA D S → ℂ) (φ : WO S T → ℂ) :
    GA D T → ℂ :=
  liftInt ν 𝓕 (fun h g φ => thetaKO om g h φ) φ f

def ThetaT {S T : HSp D} (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (om : Rep S T) (π : Submodule ℂ (GA D S → ℂ)) :
    Submodule ℂ (GA D T → ℂ) :=
  Submodule.span ℂ {F | ∃ f ∈ π, ∃ φ, IsThetaFunO ψ S T φ ∧ F = liftT ν 𝓕 om f φ}

def IsTowerT {S T : HSp D} (om : Rep S T) (r : ℕ) (Y : ℕ → HSp D) (ι : ∀ i, (Y i).V →ₗ[D.host.E] T.V)
    (C : ∀ i, Matrix (Fin T.rank) (Fin i) D.host.E) (omY : ∀ i, Rep S (Y i)) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → IsWittStep T (Y i) i (ι i) (C i) ∧ IsWeilRep ψ S (Y i) (omY i) ∧
    CompatT ψ S T (Y i) (ι i) (C i) om (omY i)

end Target

def CompatExistsT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  (∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∃ κ, HasConstS ψ θ S T om τ κ) ∧
    ∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E), 1 ≤ t → IsWittStep T T' t ι C →
      ∃ om' : Rep S T', IsWeilRep ψ S T' om' ∧ CompatT ψ S T T' ι C om om' ∧
        ∀ θ : InfFam D, IsInfFam θ → ∀ τ κ, HasConstS ψ θ S T om τ κ ↔ HasConstS ψ θ S T' om' τ κ

def LiftConvT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f, IsRapidCusp S f → ∀ φ, IsThetaFunO ψ S T φ →
    (∀ h, IntegrableOn (fun g => thetaKO om g h φ * f g) 𝓕 ν) ∧ Continuous (liftT ν 𝓕 om f φ) ∧
      ∀ γ ∈ GQ T, ∀ h, liftT ν 𝓕 om f φ (γ * h) = liftT ν 𝓕 om f φ h

def ConstTermT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep T T' t ι C)
    (om' : Rep S T'), IsWeilRep ψ S T' om' → CompatT ψ S T T' ι C om om' →
    ∃ (μa : GL (Fin t) (AE D) →* Circle) (ξ : GA D T' →* Circle), IsAutCharGL t μa ∧ IsAutCharU T' ξ ∧
      ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 →
        (∀ φ', IsThetaFunO ψ S T' φ' ↔ ∃ φ, IsThetaFunO ψ S T φ ∧ φ' = resT S T T' ι C μ 𝓖 φ) ∧
        ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f, IsRapidCusp S f → ∀ φ, IsThetaFunO ψ S T φ →
          (∀ h, constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om f φ) h =
            liftT ν 𝓕 om' f (resT S T T' ι C μ 𝓖 (om (1, h) φ)) 1) ∧
          ∀ a h' m, IsLeviElt T T' ι C a h' m →
            constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om f φ) m =
              (μa a : ℂ) * (detPow a S.rank : ℂ) * (ξ h' : ℂ) * liftT ν 𝓕 om' f (resT S T T' ι C μ 𝓖 φ) h'

def CuspIffT (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ Y ι C omY, IsTowerT ψ om (GlobalTheory.Cusp.wittIndex T) Y ι C omY →
    ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ π : Submodule ℂ (GA D S → ℂ), (∀ f ∈ π, IsRapidCusp S f) →
      ((∀ F ∈ ThetaT ψ ν 𝓕 om π, IsCuspFun T F) ↔
        ∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex T → ThetaT ψ ν 𝓕 (omY i) π = ⊥)

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)

def resS (μ : Measure (Mx D T.rank t)) (𝓖 : Set (Mx D T.rank t)) (φ : WO S T → ℂ) : WO S' T → ℂ :=
  fun w' => ∫ y in 𝓖, φ ((y : Matrix (Fin T.rank) (Fin t) (AE D)) * adel (ct C * S.gram) +
    (w' : Matrix (Fin T.rank) (Fin S'.rank) (AE D)) * adel (S'.gram⁻¹ * ct (frameMat S S' ι) * S.gram)) ∂μ

def CompatS (om : Rep S T) (om' : Rep S' T) : Prop :=
  ∀ μ 𝓖, IsCovolOne (ratMx D T.rank t) μ 𝓖 → ∀ (h : GA D T) φ, IsThetaFunO ψ S T φ →
    resS S S' T ι C μ 𝓖 (om (1, h) φ) = om' (1, h) (resS S S' T ι C μ 𝓖 φ)

def liftS {S T : HSp D} (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (om : Rep S T) (f : GA D T → ℂ) (φ : WO S T → ℂ) :
    GA D S → ℂ :=
  liftInt ν 𝓕 (thetaKO om) φ f

def ThetaS {S T : HSp D} (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (om : Rep S T) (π : Submodule ℂ (GA D T → ℂ)) :
    Submodule ℂ (GA D S → ℂ) :=
  Submodule.span ℂ {F | ∃ f ∈ π, ∃ φ, IsThetaFunO ψ S T φ ∧ F = liftS ν 𝓕 om f φ}

def IsTowerS {S T : HSp D} (om : Rep S T) (r : ℕ) (Y : ℕ → HSp D) (ι : ∀ i, (Y i).V →ₗ[D.host.E] S.V)
    (C : ∀ i, Matrix (Fin S.rank) (Fin i) D.host.E) (omY : ∀ i, Rep (Y i) T) : Prop :=
  ∀ i, 1 ≤ i → i ≤ r → IsWittStep S (Y i) i (ι i) (C i) ∧ IsWeilRep ψ (Y i) T (omY i) ∧
    CompatS ψ S (Y i) T (ι i) (C i) om (omY i)

end Source

def CompatExistsS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  (∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∃ κ, HasConstT ψ θ S T om τ κ) ∧
    ∀ (S' : HSp D) (t : ℕ) ι (C : Matrix (Fin S.rank) (Fin t) D.host.E), 1 ≤ t → IsWittStep S S' t ι C →
      ∃ om' : Rep S' T, IsWeilRep ψ S' T om' ∧ CompatS ψ S S' T ι C om om' ∧
        ∀ θ : InfFam D, IsInfFam θ → ∀ τ κ, HasConstT ψ θ S T om τ κ ↔ HasConstT ψ θ S' T om' τ κ

def LiftConvS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ f, IsRapidCusp T f → ∀ φ, IsThetaFunO ψ S T φ →
    (∀ g, IntegrableOn (fun h => thetaKO om g h φ * f h) 𝓕 ν) ∧ Continuous (liftS ν 𝓕 om f φ) ∧
      ∀ γ ∈ GQ S, ∀ g, liftS ν 𝓕 om f φ (γ * g) = liftS ν 𝓕 om f φ g

def ConstTermS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ (S' : HSp D) (t : ℕ) ι (C : Matrix (Fin S.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep S S' t ι C)
    (om' : Rep S' T), IsWeilRep ψ S' T om' → CompatS ψ S S' T ι C om om' →
    ∃ (μa : GL (Fin t) (AE D) →* Circle) (ξ : GA D S' →* Circle), IsAutCharGL t μa ∧ IsAutCharU S' ξ ∧
      ∀ μ 𝓖, IsCovolOne (ratMx D T.rank t) μ 𝓖 →
        (∀ φ', IsThetaFunO ψ S' T φ' ↔ ∃ φ, IsThetaFunO ψ S T φ ∧ φ' = resS S S' T ι C μ 𝓖 φ) ∧
        ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ f, IsRapidCusp T f → ∀ φ, IsThetaFunO ψ S T φ →
          (∀ g, constTerm (frameFlag (hs.isIsoFrame ht)) (liftS ν 𝓕 om f φ) g =
            liftS ν 𝓕 om' f (resS S S' T ι C μ 𝓖 (om (g, 1) φ)) 1) ∧
          ∀ a g' m, IsLeviElt S S' ι C a g' m →
            constTerm (frameFlag (hs.isIsoFrame ht)) (liftS ν 𝓕 om f φ) m =
              (μa a : ℂ) * (detPow a T.rank : ℂ) * (ξ g' : ℂ) * liftS ν 𝓕 om' f (resS S S' T ι C μ 𝓖 φ) g'

def CuspIffS (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T) : Prop :=
  ∀ Y ι C omY, IsTowerS ψ om (GlobalTheory.Cusp.wittIndex S) Y ι C omY →
    ∀ ν 𝓕, IsQuotMeas T ν 𝓕 → ∀ π : Submodule ℂ (GA D T → ℂ), (∀ f ∈ π, IsRapidCusp T f) →
      ((∀ F ∈ ThetaS ψ ν 𝓕 om π, IsCuspFun S F) ↔
        ∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex S → ThetaS ψ ν 𝓕 (omY i) π = ⊥)

def TowerGeneral (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T), IsWeilRep ψ S T om →
    (CompatExistsT ψ S T om ∧ LiftConvT ψ S T om ∧ ConstTermT ψ S T om ∧ CuspIffT ψ S T om) ∧
      CompatExistsS ψ S T om ∧ LiftConvS ψ S T om ∧ ConstTermS ψ S T om ∧ CuspIffS ψ S T om

def TowerAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : Rep S T), IsWeilRep ψ S T om → IsAniso S →
    CompatExistsT ψ S T om ∧
    (∀ (T' : HSp D) (t : ℕ) ι (C : Matrix (Fin T.rank) (Fin t) D.host.E) (ht : 1 ≤ t) (hs : IsWittStep T T' t ι C)
      (om' : Rep S T'), IsWeilRep ψ S T' om' → CompatT ψ S T T' ι C om om' →
      ∀ μ 𝓖, IsCovolOne (ratMx D t S.rank) μ 𝓖 → ∀ φ, IsThetaFunO ψ S T φ →
        IsThetaFunO ψ S T' (resT S T T' ι C μ 𝓖 φ) ∧
        (∀ g h, constTerm (frameFlag (hs.isIsoFrame ht)) (fun x => thetaKO om g x φ) h =
          thetaKO om' g 1 (resT S T T' ι C μ 𝓖 (om (1, h) φ))) ∧
        ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f : GA D S → ℂ, Continuous f → (∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) →
          ∀ h, constTerm (frameFlag (hs.isIsoFrame ht)) (liftT ν 𝓕 om (star f) φ) h =
            liftT ν 𝓕 om' (star f) (resT S T T' ι C μ 𝓖 (om (1, h) φ)) 1) ∧
    ∀ Y ι C omY, IsTowerT ψ om (GlobalTheory.Cusp.wittIndex T) Y ι C omY →
      ∀ ν 𝓕, IsQuotMeas S ν 𝓕 → ∀ f : GA D S → ℂ, Continuous f → (∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) →
        (∀ i, 1 ≤ i → i ≤ GlobalTheory.Cusp.wittIndex T → ∀ φ', IsThetaFunO ψ S (Y i) φ' →
          liftT ν 𝓕 (omY i) (star f) φ' = 0) →
        ∀ φ, IsThetaFunO ψ S T φ → IsCuspFun T (liftT ν 𝓕 om (star f) φ)

def TowerProperty (D : D7) : Prop := TowerAniso D ∧ TowerGeneral D

example (D : D7) : ∃ B' ι C, IsWittStep (CuspDecay.Model.plane D) B' 1 ι C ∧ B'.rank = 0 := by
  obtain ⟨B', ι, C, h, -⟩ := (exists_isWittStep_iff (CuspDecay.Model.plane D) 1).2 (GlobalTheory.Cusp.wittIndex_plane D).ge
  have h1 : B'.rank + 2 * 1 = 2 := h.1
  exact ⟨B', ι, C, h, by omega⟩

example (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) :
    IsLeviElt B B' ι C 1 1 1 := by
  simp [IsLeviElt, Formalism.L2.Theta.mt]

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
