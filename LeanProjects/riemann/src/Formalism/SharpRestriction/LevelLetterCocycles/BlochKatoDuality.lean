import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace Formalism.MainNotions.BlochKatoDuality

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

section Rep

variable {G : Type} [Group G] {LL : Type} [Field LL]

def IsSubSumOf {W A B : Type} [AddCommGroup W] [Module LL W] [AddCommGroup A] [Module LL A]
    [AddCommGroup B] [Module LL B] (ρW : Representation LL G W) (ρA : Representation LL G A)
    (ρB : Representation LL G B) : Prop :=
  ∃ (a b : ℕ) (p : Fin a → W →ₗ[LL] A) (q : Fin b → W →ₗ[LL] B),
    (∀ i g w, p i (ρW g w) = ρA g (p i w)) ∧ (∀ j g w, q j (ρW g w) = ρB g (q j w)) ∧
    ∀ w, (∀ i, p i w = 0) → (∀ j, q j w = 0) → w = 0

end Rep

section Push

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {X : Type} [AddCommGroup X] [Module LL X] [Module Qp X] [IsScalarTower Qp LL X]
    [Module O X] [IsScalarTower O LL X] {ρX : Representation LL G X}
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    [Module O U] [IsScalarTower O LL U] {ρU : Representation LL G U}
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul LL X]

def IsGMapD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T)) :
    Prop :=
  ∀ g y, φ (actT LY g y) = repD LT g (φ y)

def pushD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T))
    (y : ↥(latticeCocycles LY)) : G → U ⧸ LT.T :=
  fun g => φ (evT LY g y)

end Push

section Stmts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

def LiftAll (A Bt : GRep G Qp LL O) (e : ℕ) : Prop :=
  ∀ W₁ W₂ : GRep G Qp LL O, IsSubSumOf W₁.ρ A.ρ Bt.ρ → IsSubSumOf W₂.ρ A.ρ Bt.ρ →
    ∀ (L₁ : Lattice (O := O) W₁.ρ) (L₂ : Lattice (O := O) W₂.ρ) (F : LatHom L₁ L₂),
      F.Onto → F.LiftF PD e

def spanPush (X U : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) : Submodule O (G → U.V ⧸ LT.T) :=
  Submodule.span O {c | ∃ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (_ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)), (y : G → X.V) ∈ latticeFiniteCocycles PD LY ∧ c = pushD LY LT φ y}

def lenMod {M : Type} [AddCommGroup M] [Module O M] (S H : Submodule O M) : ℕ∞ :=
  Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype)

end Stmts

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

def Hyp {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL] (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ)
    (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL) (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ) (e : ℕ) : Prop :=
  IsTwistRep χ⁻¹ V.ρ X.ρ ∧ IsDR PD U.ρ ∧ IsDual1 PD X.ρ X'.ρ PX ∧
    IsDualLat1 PD LT LT' PU ∧ (LiftAll PD X U e ∨ (IsDR PD X.ρ ∧ LiftAll PD X' U' e))

def ArcTheoremGlobal : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∀ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)), IsGMapD LY LT φ →
  ∀ y : ↥(latticeCocycles LY), (y : G → X.V) ∈ latticeFiniteCocycles PD LY →
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT

def PushoutSpanLengthBound : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∃ m k : ℕ, lenMod (spanPush PD X U LT) (HfD PD LT) = m ∧ lenOl PD (O := O) = k ∧
    m ≤ e * (finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T) * k

end Main

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def grepOf (T : Formalism.BasicNotions.LocLat G Qp LL O) : GRep G Qp LL O :=
  @GRep.mk G _ _ Qp LL O _ _ _ _ _ _ T.V T.acg T.modLL T.modQp T.towQp T.modO T.towO T.fdim T.top
    T.mtop T.cadd T.csmul T.ρ T.cont

def latOf (T : Formalism.BasicNotions.LocLat G Qp LL O) : Lattice (O := O) (grepOf T).ρ := T.L

end Bridge

section Packet

open Formalism.BasicNotions

def Conclusion1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), ArcTheoremGlobal ((D.loc l).PD K)

def Conclusion2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), PushoutSpanLengthBound ((D.loc l).PD K)

def adm1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkACore ((D.loc l).PD K)

def adm2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkBCore ((D.loc l).PD K)

def adm3 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), LocalTateTopDegree ((D.loc l).PD K)

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), cycIntCore ((D.loc l).PD K)

def adm5 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), TateFiniteness ((D.loc l).PD K)

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), drDualCore ((D.loc l).PD K)

def admitted (D : Formalism.BasicNotions.D7) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D

def Stmt (D : Formalism.BasicNotions.D7) : Prop := admitted D → Conclusion1 D ∧ Conclusion2 D

end Packet

end Formalism.MainNotions.BlochKatoDuality
