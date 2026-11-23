import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7}

abbrev Pl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

abbrev Lat (S : HSp D) : Type := Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)

def compAt (D : D7) (w : Pl D) : AE D →+* Fv D.host.F w ⊗[D.host.F] D.host.E := (compFin D w).comp (finPart D)

def idAt (D : D7) (P : Pl D → Prop) : Ideal (AE D) :=
  RingHom.ker (infPart D) ⊓ ⨅ w : {w : Pl D // ¬ P w}, RingHom.ker (compAt D w.1)

def idOff (D : D7) (P : Pl D → Prop) : Ideal (AE D) := ⨅ w : {w : Pl D // P w}, RingHom.ker (compAt D w.1)

def intAt (D : D7) (P : Pl D → Prop) : Set (AE D) := {a | a ∈ idAt D P ∧ finPart D a ∈ intAE D}

def congGrp (V : HSp D) (I : Ideal (AE D)) : Subgroup (GA D V) :=
  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (matHom V)).ker

def grpAt (V : HSp D) (P : Pl D → Prop) : Subgroup (GA D V) := congGrp V (idAt D P)

def grpOff (V : HSp D) (P : Pl D → Prop) : Subgroup (GA D V) := congGrp V (idOff D P)

def MxAt (P : Pl D → Prop) {m n : ℕ} (x : Mx D m n) : Prop := ∀ i j, x i j ∈ idAt D P

def latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ v, ¬ P v → evalV D.host.F v α = 0) ∧ ∃ a ∈ 𝔞, ∃ x ∈ L,
    y = fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x i)}

def latV (S : HSp D) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) := latMul S {1} L P

def latA (S : HSp D) (L : Lat S) (P : Pl D → Prop) : AddSubgroup (Fin S.rank → AE D) :=
  latMul S {a | a ∈ D.host.AA} L P

def Moves (S : HSp D) (g : GA D S) (L M : Lat S) (P : Pl D → Prop) : Prop :=
  ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D P) → (y ∈ latV S L P ↔ mt S g *ᵥ y ∈ latV S M P)

def InK (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S) : Prop := κ ∈ grpAt S P ∧ Moves S κ L L P

def Vac (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) P) f

def Tame (D : D7) (v : Pl D) : Prop :=
  ExtUnramAt D v ∧ ((2 : 𝓞 D.host.F) ∉ v.asIdeal ∨
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)

def colMul {m n : ℕ} (x : Mx D m n) (i : Fin n) (a : AE D) : Fin m → AE D := fun k => a * x k i

def MonoAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = v) ↔
    (∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v)) ∧
      d.p0 *ᵥ y ∈ latV S₀ L₀ (· = v)

def OrthAt {S A B : HSp D} (o : OrthDec S A B) (L : Lat S) (LA : Lat A) (LB : Lat B) (v : Pl D) : Prop :=
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = v) ↔ o.pA *ᵥ y ∈ latV A LA (· = v) ∧ o.pB *ᵥ y ∈ latV B LB (· = v)

def PrimAt (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) : Prop :=
  ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ s ∈ idAt D (· = v),
    (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (s * a) ∈ latV S L (· = v)) ↔
      ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1

def ColsAt {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (x : Mx D W.rank ρ) (LV : Lat V) (LW : Lat W) (v : Pl D) : Prop :=
  ∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV V LV (· = v) ↔ colMul x i a ∈ latA W LW (· = v)

structure GoodBF (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀)
    (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D) : Prop where
  tame : Tame D v
  sdV : IsSelfDualC B.V LV
  sdV₀ : IsSelfDualC B.V₀ LV₀
  sdW : IsSelfDualC J.W LW
  sdW₀ : IsSelfDualC J.W₀ LW₀
  monoV : MonoAt B.d LV LV₀ v
  monoW : MonoAt J.d LW LW₀ v
  prim : PrimAt ψ B.d LV v
  cols : ColsAt B.d (xZero J.d) LV LW v
  last : 0 < ρ → ∀ a ∈ idAt D (· = v),
    J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ)) ∈ latO B.V₀ J.W (LV₀ : Set _) (LW : Set _) (· = v) ↔
      a ∈ intAt D (· = v)

structure AdaptFB (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (LV : Lat J.W)
    (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D) : Prop where
  tame : Tame D v
  sdV : IsSelfDualC J.W LV
  sdV₀ : IsSelfDualC J.W₀ LV₀
  sdW : IsSelfDualC B.V LW
  sdW₀ : IsSelfDualC B.V₀ LW₀
  monoV : MonoAt J.d LV LV₀ v
  monoW : MonoAt B.d LW LW₀ v
  prim : PrimAt ψ J.d LV v
  cols : ColsAt J.d (xLast B.d (vecB B.o B.ζ)) LV LW v

def SplitCore {ρ : ℕ} (B : BesLev D ρ) (L₀ : Lat B.V₀) (v : Pl D) : Prop :=
  ∃ (LA : Lat B.A) (LL : Lat B.L), IsSelfDualC B.A LA ∧ IsSelfDualC B.L LL ∧ OrthAt B.o L₀ LA LL v

def UInv (W : HSp D) {ρ : ℕ} (x y : Mx D W.rank ρ) : Prop := ∀ u : UX D ρ, pairS W (x ⬝ u.1.1) y = pairS W x y

structure HeisLaws (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : Pl D → Prop) (𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)) : Prop where
  theta : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V₀ W₀ (𝔉 f)
  dual : ∀ f, IsThetaFunO ψ V W f → ∀ a : Mx D W.rank ρ, MxAt P a → UInv W x a →
    𝔉 (heisO ψ V W (dV.extY W a) f) = ψ (symplO V W (dV.extX W x) (dV.extY W a)) • 𝔉 f
  iso : ∀ f, IsThetaFunO ψ V W f → ∀ ξ : Mx D σ V₀.rank, MxAt P ξ →
    𝔉 (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • 𝔉 f
  core : ∀ f, IsThetaFunO ψ V W f → ∀ w : WO V₀ W₀, MxAt P w →
    𝔉 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) f) = heisO ψ V₀ W₀ w (𝔉 f)

variable {ψ : AddChar (AF D.host.F) ℂ}

structure IsFlatBF {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (P : Pl D → Prop)
    (𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)) : Prop where
  Heisenberg₂ : HeisLaws ψ B.d J.d (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) P 𝔉
  equiv : ∀ f, IsThetaFunO ψ B.V J.W f → ∀ n ∈ flagN J.d, n ∈ grpAt J.W P → ∀ h ∈ grpAt J.W₀ P,
    𝔉 (s.om (1, n * J.d.emb0 h) f) = star (psiFlag ψ J.d n) • opA ψ J.d B.o B.ζ s.om₀ n h (𝔉 f)

structure IsFlatFB {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (P : Pl D → Prop)
    (𝔉 : (WO J.W B.V → ℂ) → (WO J.W₀ B.V₀ → ℂ)) : Prop where
  Heisenberg₂ : HeisLaws ψ J.d B.d (xLast B.d (vecB B.o B.ζ)) 0 P 𝔉
  equiv : ∀ f, IsThetaFunO ψ J.W B.V f → ∀ n ∈ flagN B.d, n ∈ grpAt B.V P → ∀ h ∈ grpAt B.A P,
    𝔉 (s.om (1, n * embA B.d B.o h) f) =
      star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • s.om₀ (1, B.o.emb (h, 1)) (𝔉 f)

structure SplitPt (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] where
  v : Pl D
  e : AE D
  split : IsSplitIdem D e
  above : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  pr : AE D →+* k
  sec : k →+ AE D
  pr_sec : ∀ a, pr (sec a) = a
  sec_pr : ∀ x, sec (pr x) = e * x
  cont_pr : Continuous pr
  cont_sec : Continuous sec
  int_iff : ∀ a, a ∈ 𝒪[k] ↔ finPart D (sec a) ∈ intAE D

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

def SplitPt.IsChar (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) : Prop := ∀ a, (χ a : ℂ) = psiE ψ (p.sec a)

def SplitPt.UnitAA : Prop :=
  (∀ a ∈ intAt D (· = p.v), incA D D.host.xi0 * a ∈ intAt D (· = p.v) ∧ incA D D.host.xi0⁻¹ * a ∈ intAt D (· = p.v)) ∧
    ∀ (S : HSp D) (L : Lat S), latA S L (· = p.v) = latV S L (· = p.v)

structure Frame (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  b : Matrix (Fin S.rank) n k
  b' : Matrix n (Fin S.rank) k
  bb' : b * b' = 1
  b'b : b' * b = 1
  gl : GL n k →* GA D S
  gl_supp : ∀ g, SuppAt p.e S (gl g)
  gl_mat : ∀ g, (mt S (gl g)).map p.pr = b * g.val * b'

variable {p} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def Frame.rep (β : Frame p S n) : Representation ℂ (GL n k) (GA D S → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ fun x => x * β.gl g
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [LinearMap.funLeft, mul_assoc]

def Frame.IsLat (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ x : n → k, x ∈ Λ ↔ (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)

def rd (α : Frame p S n') (β : Frame p T n) (t : WO S T) : Matrix n n' k :=
  β.b' ⬝ Matrix.map t p.pr ⬝ α.b

open Classical in

def extFun (α : Frame p S n') (β : Frame p T n) (Ψ : Matrix n n' k → ℂ) (t : WO S T) : ℂ :=
  if IsHalf p.e t then Ψ (rd α β t) else 0

def Over (ψ : AddChar (AF D.host.F) ℂ) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ)
    (Ψ : Matrix n n' k → ℂ) (f : WO S T → ℂ) : Prop :=
  IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Vac ψ S T LS LT (· = p.v) f₀ ∧ Ψ ∈ SB (Matrix n n' k) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) 1 f₀ (extFun α β Ψ) f

def IsSumFrame {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p A n)
    (β₀ : Frame p S₀ (n ⊕ Fin 1)) : Prop :=
  β₀.b = fromCols (o.jA.map p.pr * β.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i))

def IsRam (β : Frame p S n) (φ : Form k n (GA D S → ℂ)) : Prop :=
  φ ∈ EqForm β.rep ∧ φ ∈ Mram k n (GA D S → ℂ) ∧ ∀ P, IsContAut S (φ P)

def RamAt (β : Frame p S n) (P : Pair k n) (φ₀ : GA D S → ℂ) : Prop := ∃ φ, IsRam β φ ∧ φ P = φ₀

structure GluedCore {ρ : ℕ} (B : BesLev D ρ) (L₀ : Lat B.V₀) (q : Unif k) (β : Frame p B.A n)
    (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n) : Prop where
  unit : p.UnitAA
  sum : IsSumFrame B.o B.ζ β β₀
  norm : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ))) = valuation k ((q.1 : 𝒪[k]) : k)
  lat : β₀.IsLat L₀ (gluedS q 1 P.ker P.vec)

def tensCol (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (x : Matrix n (n' ⊕ Fin 1) k) : ℂ :=
  Ψ (x.submatrix id Sum.inl) * a fun i => x i (Sum.inr 0)

def tensRow (Ψ : Matrix n n' k → ℂ) (b : (n' → k) → ℂ) (x : Matrix (n ⊕ Fin 1) n' k) : ℂ :=
  Ψ (x.submatrix Sum.inl id) * b (x (Sum.inr 0))

open Classical in

def vecInd (Λ : Submodule 𝒪[k] (n → k)) (y : n → k) : ℂ := if y ∈ Λ then 1 else 0

open Classical in

def dualInd (Λ : Submodule 𝒪[k] (n → k)) (η : n → k) : ℂ := if GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.InDual Λ η then 1 else 0

def charInd (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) (y : n → k) : ℂ := χ (-Q.ev y) * vecInd Q.lat y

end Frames

def liftA {S A L T : HSp D} (o : OrthDec S A L) (om : Om S T) (vA : Vol A) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ)
    (h : GA D T) (w : WO L T) : ℂ :=
  ∫ a in vA.𝓕, φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, w)) ∂vA.μ

theorem handBF_eq {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (h : GA D J.W₀) (w : WO J.W₀ L') :
    handBF s l φ Ξ h w = star (liftA B.o s.om₀ B.vA φ Ξ h (l.κ J.W₀ w)) := rfl

def hand0 {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ)
    (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) : GA D B'.A → ℂ :=
  handFB s₂ vL (handBF s₁ l φ Ξ₁) Ξ₂

end GlobalTheory.FinPl

end
