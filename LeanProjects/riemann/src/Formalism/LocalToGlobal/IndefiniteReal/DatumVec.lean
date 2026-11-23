import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev EAf (D : D7) : Type := D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F

def toEAf (D : D7) : AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp (finPart D)

def eToEAf (D : D7) : D.host.E →+* EAf D := Algebra.TensorProduct.includeLeftRingHom

def frMapO (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βT⁻¹).val ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D))) βS.val

def frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (x : WO S T) : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
      (T.gram.map (incA D))).map (toEAf D)))
    βT.val

def IsIntM {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) : Prop :=
  ∀ i j, N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

open Classical in

def redM (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) :
    Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) :=
  fun i j => if h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨N i j, h⟩ else 0

def topL {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Matrix (Fin k) (Fin k) κ :=
  fun i j => if h : i.val < b ∧ j.val < a then y ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

def LowZero {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Prop :=
  ∀ i j, k ≤ i.val → j.val < k → y i j = 0

open Classical in

def omegaG {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
      ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
        (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
        (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H then
    ((L.P.chi ⟨fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (h.2.choose PP), h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
        ((L.cg (c + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (c + 1) (h.2.choose PP)) : ℂˣ) : ℂ)) *
      ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (h.2.choose PP))) : ℂˣ) : ℂ)⁻¹
  else 0

open Classical in

def omegaQ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then
    ∏ PP ∈ Q.attach, (((ξ PP.1 (h PP.1 PP.2).2.unit) : ℂˣ) : ℂ) ^ k
  else 0

open Classical in

def omegaK {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1 then 1 else 0

def IsIdemSum (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) ∧ e = ∑ PP ∈ P, es PP) ∧
    e * cA D e = 0

open Classical in

def IsStepVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) *
          omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
        else 0) f

def IsStepVec (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f : WO S T → ℂ) : Prop :=
  ∃ f₀, IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f

open Classical in

def IsThPVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
        else 0) f

def IsThPVec (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f : WO S T → ℂ) : Prop :=
  ∃ f₀, IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f

def pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] (WO S T → ℂ) :=
  pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f

structure IsDatumStep (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ fF : WO S T → ℂ) : Prop where
  cartS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)
  cartT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)
  onbS : ∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)
  onbT : ∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)
  frS : Formalism.L2.DIV.IsFrame βS ΛS
  frT : Formalism.L2.DIV.IsFrame βT ΛT
  sdS : IsSelfDualC S ΛS
  sdT : IsSelfDualC T ΛT
  disj : Disjoint LS.Pg Q
  vec : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ fF

structure IsDatumThP (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ fF : WO S T → ℂ) : Prop where
  cartS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)
  cartT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)
  onbS : ∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)
  onbT : ∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)
  frS : Formalism.L2.DIV.IsFrame βS ΛS
  frT : Formalism.L2.DIV.IsFrame βT ΛT
  sdS : IsSelfDualC S ΛS
  sdT : IsSelfDualC T ΛT
  disj : Disjoint Pg Q

  posS : ∀ τ, (gramAt D S τ).PosDef
  vec : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ fF

def PlaceModelExistsSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
      (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧
      ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm

open Classical in

def StepVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint LS.Pg Q →
    (∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f

open Classical in

def ThPVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q →
    (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f

def VecLaw {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (KS : Subgroup (GA D S))
    (chS : GA D S → ℂ) (KT : Subgroup (GA D T)) (chT : GA D T → ℂ) (f : WO S T → ℂ) : Prop :=
  (∀ κ ∈ KS, om (κ, 1) f = chS κ • f) ∧ ∀ κ ∈ KT, om (1, κ) f = chT κ • f

end Formalism.IndefR.Datum

end
