import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage3S
import Formalism.LocalToGlobal.GlobalTheory.PassageAtBaseSymmetricLevels
import Formalism.LocalToGlobal.IndefiniteReal.LevelAmbTransfer

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type)
    (m : ℕ) where
  A3 : FamIn3 K G Pl0 I0 Ty T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)
  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3
  X : CxData A3.fam3.amb3
  gE : Representation ℂ G X.EE

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

abbrev A : FamIn K G Pl0 T m := I.A3.A

abbrev cr : Crd I.A3.fam3.amb3 (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A3.fam3.amb3 (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A3.fam3.base3.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A3.fam3.base3.Tup) :
    Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))

open Classical in

def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

def eMat {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  (Formalism.IndefR.TransferLatticeStatement.charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, Formalism.IndefR.TransferLatticeStatement.charOf τ x⁻¹ • I.ρf x

abbrev LA {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : LevelAmb K (I.Sb false).D (I.Sb true).D where
  Dg := I.Sg.D
  Xg := I.Sg.XE
  Rg := I.Sg.RR
  ep0 := I.epM I.P0 I.ψ0
  ep1 := I.epM I.P1 I.ψ1
  S := S
  fS := inferInstance
  es s := I.eMat (τ s)
  nS s := Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨I.P1, I.ψ1⟩
  nbar := nbar
  G := Fintype.card G
  h0 := Nat.card I.P0
  h1 := Nat.card I.P1
  ι0 := I.Jm false
  ι1 := I.Jm true

structure Hyp (s : ℕ) : Prop where
  ok : I.A3.fam3.Ok3 s
  sep : I.A3.fam3.TypesSep3
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A3.side3 I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A3.side3 I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : ∀ (g : G) (x y : I.X.EE), ⟪I.gE g x, I.gE g y⟫_ℂ = ⟪x, y⟫_ℂ
  gequiv : GEquiv3 I.A3 I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PRange : Prop :=
  ∀ s, I.Hyp s → ∀ b, LinearMap.range (I.Jm b).mulVecLin = LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

def PLat : Prop := ∀ s, I.Hyp s → Submodule.IsLattice K I.Sg.RR

def PGLat : Prop := ∀ s, I.Hyp s → ∀ (g : G), ∀ x ∈ I.Sg.RR, I.ρf g *ᵥ x ∈ I.Sg.RR

def PSand : Prop :=
  ∀ s, I.Hyp s → ∀ b,
    (∀ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x ∈ I.Sg.RR) ∧
    ∀ y ∈ I.Sg.RR, y ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin →
      ∃ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x = ((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • y

def PGood {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) : Prop :=
  ∀ s, I.Hyp s → Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ I.A.fam.X → ∑ t, I.eMat (τ t) = 1

end In3

end Formalism.IndefR.CxPass
