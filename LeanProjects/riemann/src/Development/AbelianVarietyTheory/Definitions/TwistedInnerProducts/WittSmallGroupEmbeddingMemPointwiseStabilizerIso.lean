import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open GlobalTheory.BesselChar (superSum)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

variable {D : D7}

def psiE (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : ℂ := ψ (Algebra.trace (AF D.host.F) (AE D) x)

def UX (D : D7) (ρ : ℕ) : Subgroup (GL (Fin ρ) (AE D)) := GlobalTheory.UniIndexPrime.uniSub ρ (AE D)

scoped instance measUX (ρ : ℕ) : MeasurableSpace (UX D ρ) := borel _

def UXQ (D : D7) (ρ : ℕ) : Subgroup (UX D ρ) where
  carrier := {u | u.1.1 ∈ ratMx D ρ ρ ∧ (u.1⁻¹).1 ∈ ratMx D ρ ρ}
  one_mem' := ⟨ratMx_one, ratMx_one⟩
  mul_mem' := fun {a b} ha hb => ⟨ratMx_mul ha.1 hb.1, by
    rw [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]; exact ratMx_mul hb.2 ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, ha.1⟩

def IsUnitU (D : D7) (ρ : ℕ) (ν : Measure (UX D ρ)) : Prop :=
  ν.IsHaarMeasure ∧ ∃ 𝓤 : Set (UX D ρ), IsFundamentalDomain (UXQ D ρ) 𝓤 ν ∧ ν 𝓤 = 1

def upSum {ρ : ℕ} (T : Mx D ρ ρ) : AE D := ∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then T i j else 0

def ell (D : D7) (ρ : ℕ) : Fin ρ → AE D := fun i => if i.1 + 1 = ρ then 1 else 0

def psiUni (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (u : GL (Fin ρ) (AE D)) : ℂ := psiE ψ (upSum u.1)

def fixer (T : HSp D) {k : ℕ} (x : Mx D T.rank k) : Subgroup (GA D T) where
  carrier := {g | mt T g ⬝ x = x}
  one_mem' := by change mt T 1 ⬝ x = x; rw [mt_one, Matrix.one_mul]
  mul_mem' := fun {a b} ha hb => by
    change mt T (a * b) ⬝ x = x
    rw [mt_mul, Matrix.mul_assoc, show mt T b ⬝ x = x from hb, show mt T a ⬝ x = x from ha]
  inv_mem' := fun {a} ha => by
    change mt T a⁻¹ ⬝ x = x
    conv_lhs => rw [← show mt T a ⬝ x = x from ha]
    rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mem_fixer {T : HSp D} {k : ℕ} {x : Mx D T.rank k} {g : GA D T} : g ∈ fixer T x ↔ mt T g ⬝ x = x := Iff.rfl

section Groups

variable {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)

abbrev flagN : Subgroup (GA D S) := NFlag S d.e

def radX : Subgroup (GA D S) := flagN d ⊓ fixer S d.jX

def centre : Subgroup (GA D S) where
  carrier := Set.range d.nC
  one_mem' := ⟨0, d.nC_zero⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, d.nC_add a b⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, (d.nC_inv a).symm⟩

def embA : GA D A →* GA D S := d.emb0.comp (o.emb.comp (MonoidHom.inl _ _))

theorem embA_apply (h : GA D A) : embA d o h = d.emb0 (o.emb (h, 1)) := rfl

def jacGrp : Subgroup (GA D S) := flagN d ⊔ d.emb0.range

def besGrp : Subgroup (GA D S) := flagN d ⊔ (embA d o).range

def stabX : Subgroup (GA D S) := fixer S d.jX

end Groups

def semiMeas {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H] (N : Subgroup G) (s : H →* G)
    (μ : Measure H) (ν : Measure N) : Measure (N ⊔ s.range : Subgroup G) :=
  (μ.prod ν).map fun p : H × N =>
    ⟨p.2.1 * s p.1, mul_mem (Subgroup.mem_sup_left p.2.2) (Subgroup.mem_sup_right ⟨p.1, rfl⟩)⟩

def AbsConv {H N : Type} [MeasurableSpace H] [MeasurableSpace N] (μ : Measure H) (𝓕 : Set H) (ν : Measure N) (𝓝 : Set N)
    (K : H → N → ℂ) : Prop :=
  Integrable (Function.uncurry K) ((μ.restrict 𝓕).prod (ν.restrict 𝓝))

section Chars

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

def blockX (g : GA D S) : Mx D ρ ρ := d.pX ⬝ (mt S g ⬝ d.jX)

def coefX (z : Fin S₀.rank → D.host.E) (g : GA D S) : Fin ρ → AE D := (d.pX ⬝ (mt S g ⬝ d.j0)) *ᵥ ratV z

def psiFlag (n : GA D S) : ℂ := psiE ψ (upSum (blockX d n))

def simpleSum (z : Fin S₀.rank → D.host.E) (n : GA D S) : AE D := upSum (blockX d n) + ell D ρ ⬝ᵥ coefX d z n

def psiBes (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ℂ := psiE ψ (incA D θ * simpleSum d z n)

end Chars

def zEll (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : Mx D T.rank ρ := vecMulVec (ratV z) (ell D ρ)

def yZero (S : HSp D) (ρ : ℕ) (z : Fin S.rank → D.host.E) : Mx D S.rank ρ := -zEll S ρ z

def xZero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) : Mx D T.rank ρ := d.jX

def xLast {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (z' : Fin T₀.rank → D.host.E) : Mx D T.rank (σ + 1) :=
  Matrix.of fun k => Fin.snoc (α := fun _ => AE D) (d.jX k) ((d.j0 *ᵥ ratV z') k)

def vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) : Fin S₀.rank → D.host.E := o.iB *ᵥ ζ

section JacT

variable (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ)

def ptT (n : GA D T) : WO S T₀ := d.p0 ⬝ (mt T n⁻¹ ⬝ d.incAdj S y)

def cenT (n : GA D T) : AF D.host.F := symplOH S T (d.incAdj S y) (mt T n⁻¹ ⬝ d.incAdj S y)

def jacT (n : GA D T) (f : WO S T₀ → ℂ) : WO S T₀ → ℂ := ψ (cenT d S y n) • heisO ψ S T₀ (ptT d S y n) f

end JacT

section JacS

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

def ptS (n : GA D S) : WO S₀ T := d.extX T x ⬝ mt S n ⬝ d.j0

def cenS (n : GA D S) : AF D.host.F := symplOH S T (d.extX T x) (d.extX T x ⬝ mt S n)

def jacS (n : GA D S) (f : WO S₀ T → ℂ) : WO S₀ T → ℂ := ψ (cenS d T x n) • heisO ψ S₀ T (ptS d T x n) f

end JacS

abbrev Om (S T : HSp D) : Type := GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)

def thetaJT (ψ : AddChar (AF D.host.F) ℂ) {W W₀ L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (ζ : Fin L.rank → D.host.E)
    (omz : Om L W₀) (Φz : WO L W₀ → ℂ) (n : GA D W) (h : GA D W₀) : ℂ :=
  jacT ψ dW L (yZero L ρ ζ) n (omz (1, h) Φz) 0

def thetaJS (ψ : AddChar (AF D.host.F) ℂ) {V V₀ L' : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (ζ' : Fin L'.rank → D.host.E)
    (omz : Om V₀ L') (Φ₀ : WO V₀ L' → ℂ) (n : GA D V) (h : GA D V₀) : ℂ :=
  jacS ψ dV L' (zEll L' ρ ζ') n (omz (h, 1) Φ₀) 0

section Lift

variable {S T : HSp D} (om : Om S T)

def liftS (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (G : GA D T → ℂ) (f : WO S T → ℂ) : GA D S → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓕 (thetaKO om) f G

def liftT (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (φ : GA D S → ℂ) (f : WO S T → ℂ) : GA D T → ℂ :=
  Formalism.IndefR.Lift.liftInt μ 𝓕 (fun h g f => thetaKO om g h f) f φ

theorem liftS_apply (ν 𝓕 G f) (g : GA D S) : liftS om ν 𝓕 G f g = ∫ h in 𝓕, om (g, h) f 0 * G h ∂ν := rfl

theorem liftT_apply (μ 𝓕 φ f) (h : GA D T) : liftT om μ 𝓕 φ f h = ∫ g in 𝓕, om (g, h) f 0 * φ g ∂μ := rfl

end Lift

def rTrans {G : Type} [Mul G] (h : G) (F : G → ℂ) : G → ℂ := fun g => F (g * h)

section Bessel

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : D.host.E) {V V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  (ζ : Fin L.rank → D.host.E)

def besFun (φ : GA D A → ℂ) (f : GA D V → ℂ) (h : GA D A) (n : flagN d) : ℂ :=
  φ h * f (n.1 * embA d o h) * star (psiBes ψ d θ (vecB o ζ) n.1)

def besPer (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure (flagN d)) (𝓝 : Set (flagN d))
    (φ : GA D A → ℂ) (f : GA D V → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ θ d o ζ φ f h n ∂ν ∂μ

end Bessel

section FJT

variable (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)

def fjFun (ζ : Fin L.rank → D.host.E) (omz : Om L W₀) (φ' : GA D W₀ → ℂ) (G' : GA D W → ℂ) (Φz : WO L W₀ → ℂ)
    (h : GA D W₀) (n : flagN dW) : ℂ :=
  φ' h * G' (n.1 * dW.emb0 h) * thetaJT ψ dW ζ omz Φz n.1 h * star (psiFlag ψ dW n.1)

def fjPer (ζ : Fin L.rank → D.host.E) (omz : Om L W₀) (μ : Measure (GA D W₀)) (𝓕 : Set (GA D W₀))
    (ν : Measure (flagN dW)) (𝓝 : Set (flagN dW)) (φ' : GA D W₀ → ℂ) (G' : GA D W → ℂ) (Φz : WO L W₀ → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, fjFun ψ dW ζ omz φ' G' Φz h n ∂ν ∂μ

variable (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀)

def opA (n : GA D W) (h : GA D W₀) (Ξ : WO V₀ W₀ → ℂ) : WO V₀ W₀ → ℂ :=
  jacT ψ dW V₀ (yZero V₀ ρ (vecB o ζ)) n (om (1, h) Ξ)

def fjKer (Ξ : WO V₀ W₀ → ℂ) (h₀ : GA D A) (n : GA D W) (h : GA D W₀) : ℂ :=
  om (o.emb (h₀, 1), 1) (opA ψ dW o ζ om n h Ξ) 0

def fjAllFun (μA : Measure (GA D A)) (𝓕A : Set (GA D A)) (φ : GA D A → ℂ) (G' : GA D W → ℂ) (Ξ : WO V₀ W₀ → ℂ)
    (h : GA D W₀) (n : flagN dW) : ℂ :=
  G' (n.1 * dW.emb0 h) * star (psiFlag ψ dW n.1) * ∫ h₀ in 𝓕A, φ h₀ * fjKer ψ dW o ζ om Ξ h₀ n.1 h ∂μA

def fjAll (μA : Measure (GA D A)) (𝓕A : Set (GA D A)) (μ : Measure (GA D W₀)) (𝓕 : Set (GA D W₀))
    (ν : Measure (flagN dW)) (𝓝 : Set (flagN dW)) (φ : GA D A → ℂ) (G' : GA D W → ℂ) (Ξ : WO V₀ W₀ → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, fjAllFun ψ dW o ζ om μA 𝓕A φ G' Ξ h n ∂ν ∂μ

end FJT

section FJS

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ L' : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ)

def fjSrcKerFun (Th : GA D V → GA D V₀ → ℂ) (f : GA D V → ℂ) (h : GA D V₀) (n : flagN dV) : ℂ :=
  Th n.1 h * f (n.1 * dV.emb0 h) * star (psiFlag ψ dV n.1)

def fjSrcKer (μ : Measure (GA D V₀)) (𝓕 : Set (GA D V₀)) (ν : Measure (flagN dV)) (𝓝 : Set (flagN dV))
    (Th : GA D V → GA D V₀ → ℂ) (f : GA D V → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, fjSrcKerFun ψ dV Th f h n ∂ν ∂μ

variable (ζ' : Fin L'.rank → D.host.E) (omz : Om V₀ L')

def fjSrcFun (φ : GA D V₀ → ℂ) (f : GA D V → ℂ) (Φ₀ : WO V₀ L' → ℂ) (h : GA D V₀) (n : flagN dV) : ℂ :=
  φ h * f (n.1 * dV.emb0 h) * star (thetaJS ψ dV ζ' omz Φ₀ n.1 h) * star (psiFlag ψ dV n.1)

def fjSrc (μ : Measure (GA D V₀)) (𝓕 : Set (GA D V₀)) (ν : Measure (flagN dV)) (𝓝 : Set (flagN dV))
    (φ : GA D V₀ → ℂ) (f : GA D V → ℂ) (Φ₀ : WO V₀ L' → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, fjSrcFun ψ dV ζ' omz φ f Φ₀ h n ∂ν ∂μ

end FJS

def thPair {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f f' : Mx D m n → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * star (f' w) ∂μ

def contractT {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (μ : Measure (WO S B)) (𝓕 : Set (WO S B)) (F : WO S T → ℂ)
    (Φ₀ : WO S B → ℂ) : WO S A → ℂ :=
  fun w => thPair μ 𝓕 (fun v => F ((o.resT S).symm (w, v))) Φ₀

def contractS {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (μ : Measure (WO B T)) (𝓕 : Set (WO B T)) (F : WO S T → ℂ)
    (Φ₀ : WO B T → ℂ) : WO A T → ℂ :=
  fun w => thPair μ 𝓕 (fun v => F ((o.resS T).symm (w, v))) Φ₀

section Flat

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
  (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D σ V₀.rank)) (𝓕T : Set (Mx D σ V₀.rank))

def evalAt (Ψ : WO V W → ℂ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) : WO V₀ W₀ → ℂ :=
  dW.mixT V₀ ψ μT 𝓕T (dV.mixS W ψ μS 𝓕S Ψ x) y

def flatFun (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ) (w : WO V₀ W₀) (u : UX D ρ) : ℂ :=
  star (psiUni ψ u.1) * evalAt ψ dV dW μS 𝓕S μT 𝓕T Ψ (x ⬝ u.1.1) y w

def flatAt (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ) : WO V₀ W₀ → ℂ :=
  fun w => ∫ u, flatFun ψ dV dW μS 𝓕S μT 𝓕T x y Ψ w u ∂νU

end Flat

section FlatBes

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ A L : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  (ζ : Fin L.rank → D.host.E) (dW : HypDec W W₀ ρ)
  (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D ρ V₀.rank)) (𝓕T : Set (Mx D ρ V₀.rank))

def flat (νU : Measure (UX D ρ)) (Ψ : WO V W → ℂ) : WO V₀ W₀ → ℂ :=
  flatAt ψ dV dW μS 𝓕S μT 𝓕T νU (xZero dW) (yZero V₀ ρ (vecB o ζ)) Ψ

def evalZero (Ψ : WO V W → ℂ) : WO V₀ W₀ → ℂ :=
  evalAt ψ dV dW μS 𝓕S μT 𝓕T Ψ (xZero dW) (yZero V₀ ρ (vecB o ζ))

end FlatBes

section FlatFJ

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₂ W₁ L' : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₂ σ)
  (o' : OrthDec W₂ W₁ L') (ζ' : Fin L'.rank → D.host.E)
  (μS : Measure (Mx D W.rank (σ + 1))) (𝓕S : Set (Mx D W.rank (σ + 1)))
  (μT : Measure (Mx D σ V₀.rank)) (𝓕T : Set (Mx D σ V₀.rank))

def flatLast (νU : Measure (UX D (σ + 1))) (Ψ : WO V W → ℂ) : WO V₀ W₂ → ℂ :=
  flatAt ψ dV dW μS 𝓕S μT 𝓕T νU (xLast dW (vecB o' ζ')) 0 Ψ

variable (μL : Measure (WO V₀ L')) (𝓕L : Set (WO V₀ L'))

def flatPairFun (Ψ : WO V W → ℂ) (Φ₀ : WO V₀ L' → ℂ) (w : WO V₀ W₁) (u : UX D (σ + 1)) : ℂ :=
  star (psiUni ψ u.1) *
    contractT o' V₀ μL 𝓕L (evalAt ψ dV dW μS 𝓕S μT 𝓕T Ψ (xLast dW (vecB o' ζ') ⬝ u.1.1) 0) Φ₀ w

def flatPair (νU : Measure (UX D (σ + 1))) (Ψ : WO V W → ℂ) (Φ₀ : WO V₀ L' → ℂ) : WO V₀ W₁ → ℂ :=
  fun w => ∫ u, flatPairFun ψ dV dW o' ζ' μS 𝓕S μT 𝓕T μL 𝓕L Ψ Φ₀ w u ∂νU

def stabLast : Subgroup (GA D W) := fixer W (xLast dW (vecB o' ζ'))

end FlatFJ

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ 0 = 1 := by rw [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (x y : AE D) : psiE ψ (x + y) = psiE ψ x * psiE ψ y := by
  rw [psiE, map_add, AddChar.map_add_eq_mul]; rfl

theorem upSum_one (ρ : ℕ) : upSum (1 : Mx D ρ ρ) = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
    split_ifs with h
    · exact Matrix.one_apply_ne fun e => by rw [e] at h; omega
    · rfl

theorem mem_UX {ρ : ℕ} {u : GL (Fin ρ) (AE D)} : u ∈ UX D ρ ↔ u ∈ upperUni ρ (AE D) := Iff.rfl

theorem ell_vecMul {ρ : ℕ} {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) : ell D ρ ᵥ* u.1 = ell D ρ := by
  funext j
  change ∑ i, ell D ρ i * u.1 i j = _
  rw [Finset.sum_eq_single j]
  · rw [(hu j j).2, mul_one]
  · intro i _ hi
    unfold ell
    split_ifs with h
    · have := j.2
      rw [(hu i j).1 (lt_of_le_of_ne (by rw [Fin.le_def]; omega) hi.symm), mul_zero]
    · rw [zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

theorem zEll_mul (T : HSp D) {ρ : ℕ} (z : Fin T.rank → D.host.E) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    zEll T ρ z ⬝ u.1 = zEll T ρ z := by
  rw [zEll, Matrix.vecMulVec_mul, ell_vecMul hu]

theorem yZero_mul (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    yZero S ρ z ⬝ u.1 = yZero S ρ z := by
  rw [yZero, Matrix.neg_mul, zEll_mul S z hu]

theorem ratV_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E) :
    ratV (M *ᵥ z) = rat M *ᵥ ratV z := (GlobalTheory.BesselChar.mulVec_map (incA D) M z).symm

theorem yZero_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ρ : ℕ) (ζ : Fin L.rank → D.host.E) :
    yZero S₀ ρ (vecB o ζ) = o.jB ⬝ yZero L ρ ζ := by
  rw [yZero, yZero, zEll, zEll, Matrix.mul_neg, Matrix.mul_vecMulVec, vecB, ratV_mulVec]; rfl

section Values

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E)

theorem blockX_levi (a : GL (Fin ρ) (AE D)) : blockX d (d.levi a) = a.1 := by
  rw [blockX, d.levi_jX, cancel₂ d.pX_jX, Matrix.one_mul]

theorem blockX_of_fix {g : GA D S} (hg : g ∈ stabX d) : blockX d g = 1 := by
  rw [blockX, mem_fixer.1 hg, d.pX_jX]

theorem nB_mem_radX (b : Mx D ρ S₀.rank) : d.nB b ∈ radX d := ⟨d.nB_mem_NFlag b, d.nB_jX b⟩

theorem nC_mem_radX (c : skewA D ρ) : d.nC c ∈ radX d := ⟨d.nC_mem_NFlag c, d.nC_jX c⟩

theorem radX_le_stabX : radX d ≤ stabX d := inf_le_right

theorem wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic (g : GA D S₀) : d.emb0 g ∈ stabX d := d.wittDecomp_anisotropicEmbedding_inclX g

theorem coefX_levi (a : GL (Fin ρ) (AE D)) : coefX d z (d.levi a) = 0 := by
  rw [coefX, d.wittDecomp_levi_inclAnisotropic, d.pX_j0, Matrix.zero_mulVec]

theorem coefX_nB (b : Mx D ρ S₀.rank) : coefX d z (d.nB b) = b *ᵥ ratV z := by
  rw [coefX, d.nB_j0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]

theorem coefX_nC (c : skewA D ρ) : coefX d z (d.nC c) = 0 := by
  rw [coefX, d.nC_j0, d.pX_j0, Matrix.zero_mulVec]

theorem psiFlag_levi_mul (u : GL (Fin ρ) (AE D)) {n : GA D S} (hn : n ∈ stabX d) :
    psiFlag ψ d (d.levi u * n) = psiUni ψ u := by
  rw [psiFlag, blockX, mt_mul, Matrix.mul_assoc, mem_fixer.1 hn, ← blockX, blockX_levi, psiUni]

theorem psiBes_levi (u : GL (Fin ρ) (AE D)) : psiBes ψ d 1 z (d.levi u) = psiUni ψ u := by
  rw [psiBes, simpleSum, coefX_levi, dotProduct_zero, add_zero, map_one, one_mul, blockX_levi, psiUni]

theorem psiBes_nB (θ : D.host.E) (b : Mx D ρ S₀.rank) :
    psiBes ψ d θ z (d.nB b) = psiE ψ (incA D θ * ell D ρ ⬝ᵥ b *ᵥ ratV z) := by
  rw [psiBes, simpleSum, coefX_nB, blockX_of_fix d (d.nB_jX b), upSum_one, zero_add]

theorem psiBes_nC (θ : D.host.E) (c : skewA D ρ) : psiBes ψ d θ z (d.nC c) = 1 := by
  rw [psiBes, simpleSum, coefX_nC, blockX_of_fix d (d.nC_jX c), upSum_one, dotProduct_zero, add_zero, mul_zero, psiE_zero]

theorem levi_xZero (u : GL (Fin ρ) (AE D)) : mt S (d.levi u) ⬝ xZero d = xZero d ⬝ u.1 := d.levi_jX u

end Values

theorem symplO_yZero {V₀ W W₀ : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (b : Mx D ρ V₀.rank) :
    symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) =
      Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV z) := by
  have h := dW.symplO_incX_incAdj V₀ b (yZero V₀ ρ z)
  rw [GlobalTheory.OrientedHeis.symplO_skew]
  refine (congrArg Neg.neg h).trans ?_
  rw [yZero, Matrix.neg_mul, trace_neg, map_neg, neg_neg, zEll, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
    dotProduct_mulVec, dotProduct_comm]

theorem psi_yZero (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (z : Fin V₀.rank → D.host.E) (b : Mx D ρ V₀.rank) :
    ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) = psiBes ψ dV 1 z (dV.nB b) := by
  rw [symplO_yZero, psiBes_nB, map_one, one_mul, psiE]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  rw [heisO, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

section JacTVal

variable (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (y : Mx D S.rank ρ)

theorem levi_inv_incAdj (a : GL (Fin ρ) (AE D)) : mt T (d.levi a)⁻¹ ⬝ d.incAdj S y = d.incAdj S (y ⬝ a.1) := by
  have h := d.actO_incAdj S 1 a y
  rwa [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul] at h

theorem jacT_levi_mul {a : GL (Fin ρ) (AE D)} (ha : y ⬝ a.1 = y) (n : GA D T) :
    jacT ψ d S y (d.levi a * n) = jacT ψ d S y n := by
  have h : mt T (d.levi a * n)⁻¹ ⬝ d.incAdj S y = mt T n⁻¹ ⬝ d.incAdj S y := by
    rw [_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc, levi_inv_incAdj, ha]
  funext f
  rw [jacT, jacT, cenT, cenT, ptT, ptT, h]

theorem jacT_one : jacT ψ d S y 1 = id := by
  funext f
  rw [jacT, cenT, ptT, inv_one, mt_one, Matrix.one_mul, GlobalTheory.OrientedHeis.symplOH_self, AddChar.map_zero_eq_one, one_smul,
    d.incAdj_apply, d.incY_apply, cancel₂ d.p0_jY, Matrix.zero_mul, heisO_zero, id]

theorem ptT_nB_mul_nC (b : Mx D ρ T₀.rank) (c : skewA D ρ) :
    ptT d S y (d.nB b * d.nC c) = plus T₀ b ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA S)) := by
  rw [ptT, ← d.nC_mul_nB, _root_.mul_inv_rev, d.nB_inv, d.nC_inv, ← d.nC_mul_nB, mt_mul, Matrix.mul_assoc,
    cancel₂ (d.wittDecomp_projAnisotropic_unipotentSkew _), cancel₂ (d.wittDecomp_projAnisotropic_unipotentMixed _), d.incAdj_apply, d.incY_apply, Matrix.sub_mul, cancel₂ d.p0_jY,
    Matrix.mul_assoc, cancel₂ d.pY_jY, Matrix.zero_mul, Matrix.one_mul, plus_neg, Matrix.neg_mul, zero_sub, neg_neg]

theorem cenT_nC (c : skewA D ρ) : cenT d S y (d.nC c) = d.qT S c y := by
  rw [cenT, HypDec.qT, sub_eq_add_neg, GlobalTheory.OrientedHeis.symplOH_add_right]
  have h := GlobalTheory.OrientedHeis.symplOH_add_right (d.incAdj S y) (d.incAdj S y) (-d.incAdj S y)
  rw [add_neg_cancel, symplOH_zero_right, GlobalTheory.OrientedHeis.symplOH_self, zero_add] at h
  rw [← h, add_zero]

end JacTVal

section Line

variable {S₀ A L T T₀ : HSp D} {ρ : ℕ} (o : OrthDec S₀ A L) (d : HypDec T T₀ ρ)

theorem incAdj_jB (y : Mx D L.rank ρ) : d.incAdj S₀ (o.jB ⬝ y) = d.incAdj L y ⬝ o.pB := by
  rw [d.incAdj_apply, d.incAdj_apply, d.incY_apply, d.incY_apply, o.pB_eq, adj_mul]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, gA_giA_cancel]

theorem ptT_yZero_vecB (ζ : Fin L.rank → D.host.E) (n : GA D T) :
    o.resS T₀ (ptT d S₀ (yZero S₀ ρ (vecB o ζ)) n) = (0, ptT d L (yZero L ρ ζ) n) := by
  rw [o.resS_apply, yZero_vecB, ptT, ptT, incAdj_jB]
  simp only [Matrix.mul_assoc, o.pB_jA, o.pB_jB, Matrix.mul_zero, Matrix.mul_one]

theorem cenT_yZero_vecB (ζ : Fin L.rank → D.host.E) (n : GA D T) :
    cenT d S₀ (yZero S₀ ρ (vecB o ζ)) n = cenT d L (yZero L ρ ζ) n := by
  rw [cenT, cenT, o.symplOH_resS, o.resS_apply, o.resS_apply, yZero_vecB, incAdj_jB]
  simp only [Matrix.mul_assoc, o.pB_jA, o.pB_jB, Matrix.mul_zero, Matrix.mul_one, symplOH_zero_left, zero_add]

end Line

section JacSVal

variable (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

theorem jacS_levi_mul {a : GL (Fin ρ) (AE D)} (ha : x ⬝ a.1 = x) (n : GA D S) :
    jacS ψ d T x (d.levi a * n) = jacS ψ d T x n := by
  have h : d.extX T x ⬝ mt S (d.levi a * n) = d.extX T x ⬝ mt S n := by
    rw [mt_mul, ← Matrix.mul_assoc, d.extX_levi, ha]
  funext f
  rw [jacS, jacS, cenS, cenS, ptS, ptS, h]

theorem jacS_one : jacS ψ d T x 1 = id := by
  funext f
  rw [jacS, cenS, ptS, mt_one, Matrix.mul_one, GlobalTheory.OrientedHeis.symplOH_self, AddChar.map_zero_eq_one, one_smul,
    d.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero, heisO_zero, id]

theorem ptS_nB_mul_nC (b : Mx D ρ S₀.rank) (c : skewA D ρ) : ptS d T x (d.nB b * d.nC c) = x ⬝ b := by
  rw [ptS, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, d.extX_apply, Matrix.mul_assoc, Matrix.mul_add,
    d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]

theorem cenS_nC (c : skewA D ρ) : cenS d T x (d.nC c) = d.qS T c x := by
  rw [cenS, d.extX_nC, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_self, zero_add, HypDec.qS]

end JacSVal

def IsLineVec (L : HSp D) (ζ : Fin L.rank → D.host.E) : Prop := L.rank = 1 ∧ star ζ ⬝ᵥ L.gram *ᵥ ζ ≠ 0

section Compare

variable {V V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) {ζ : Fin L.rank → D.host.E}

theorem qX_e : d.qX * d.e = 1 := d.e'e

theorem isIsoSub_e : IsIsoSub V d.e :=
  ⟨Matrix.mulVec_injective_iff.1 fun x y h => by
    have := congrArg (d.qX *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, qX_e, Matrix.one_mulVec] using this, d.ee⟩

def toBesDat (hζ : IsLineVec L ζ) {θ : D.host.E} (hθ : θ ≠ 0) (ι : A.V →ₗ[D.host.E] V.V)
    (hι : frameMat V A ι = d.i₀ * o.iA) : BesDat A V ι where
  ρ := ρ
  codim := by have := d.rank_add; have := o.rank_add; have := hζ.1; omega
  e := d.e
  e_iso := isIsoSub_e d
  e_perp := by
    rw [cT_sig, hι, conjTranspose_mul, Matrix.mul_assoc o.iAᴴ, Matrix.mul_assoc o.iAᴴ, d.i₀e, Matrix.mul_zero]
  z := d.i₀ *ᵥ vecB o ζ
  z_perpA := by
    change (_ : Matrix _ _ D.host.E) *ᵥ _ = 0
    rw [cT_sig, hι, conjTranspose_mul, vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc o.iAᴴ,
      Matrix.mul_assoc o.iAᴴ, d.iso, o.orth', Matrix.zero_mulVec]
  z_perpE := by
    change (_ : Matrix _ _ D.host.E) *ᵥ _ = 0
    have h := congrArg conjTranspose d.i₀e
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at h
    rw [cT_sig, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  z_ne := by
    have h : ∀ x : Fin V.rank → D.host.E,
        Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram x x = star x ⬝ᵥ V.gram *ᵥ x := fun x => by
      simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
      rfl
    rw [h, vecB, Matrix.mulVec_mulVec, Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      conjTranspose_mul, Matrix.mul_assoc o.iBᴴ, Matrix.mul_assoc o.iBᴴ, ← Matrix.mul_assoc _ d.i₀, d.iso,
      ← Matrix.mul_assoc, o.isoB]
    exact hζ.2
  c _ := θ
  c_ne _ := hθ
  y := 1

theorem superSum_const (t : AE D) (T : Mx D ρ ρ) (b : Fin ρ → AE D) :
    superSum (fun _ => t) T b = t * (upSum T + ell D ρ ⬝ᵥ b) := by
  simp only [superSum, upSum, ell, dotProduct, mul_add, Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul, one_mul]

theorem upSum_add (T T' : Mx D ρ ρ) : upSum (T + T') = upSum T + upSum T' := by
  rw [upSum, upSum, upSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [add_zero]

variable (ψ : AddChar (AF D.host.F) ℂ) (hζ : IsLineVec L ζ) {θ : D.host.E} (hθ : θ ≠ 0) (ι : A.V →ₗ[D.host.E] V.V)
  (hι : frameMat V A ι = d.i₀ * o.iA)

theorem besChar_toBesDat {n : GA D V} (hn : n ∈ flagN d) :
    besChar ψ (toBesDat d o hζ hθ ι hι) n = psiBes ψ d θ (vecB o ζ) n := by
  obtain ⟨T, b, -, h1, h2⟩ := GlobalTheory.BesselChar.exists_coords (toBesDat d o hζ hθ ι hι) n hn
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  have e1 : mt V n ⬝ d.jX = d.jX + d.jX ⬝ (show Mx D ρ ρ from T) := h1
  have e2 : mt V n *ᵥ ratV (d.i₀ *ᵥ vecB o ζ) = ratV (d.i₀ *ᵥ vecB o ζ) + d.jX *ᵥ (show Fin ρ → AE D from b) := h2
  have e3 : blockX d n = 1 + (show Mx D ρ ρ from T) := by
    rw [blockX, e1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  have e4 : coefX d (vecB o ζ) n = b := by
    rw [ratV_mulVec] at e2
    rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, HypDec.j0, e2, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← HypDec.j0, d.pX_j0, d.pX_jX, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
  rw [psiBes, simpleSum, e3, e4, upSum_add, upSum_one, zero_add]
  exact congrArg (psiE ψ) (superSum_const (incA D θ) T b)

end Compare

section Struct

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem exists_blocks {n : GA D S} (hn : n ∈ flagN d) : ∃ (T : Mx D ρ ρ) (b : Mx D ρ S₀.rank),
    GlobalTheory.BesselChar.StrictUp T ∧ mt S n ⬝ d.jX = d.jX + d.jX ⬝ T ∧ mt S n ⬝ d.j0 = d.j0 + d.jX ⬝ b := by
  obtain ⟨⟨T, hT, h1⟩, h2⟩ := (GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1 n).1 hn
  choose a ha using fun j => h2 (fun k => d.j0 k j) (funext fun i => congrFun (congrFun d.pY_j0 i) j)
  exact ⟨T, (Matrix.of a)ᵀ, hT, h1, funext fun k => funext fun j => congrFun (ha j) k⟩

theorem simpleSum_eq (z : Fin S₀.rank → D.host.E) {n : GA D S} {T : Mx D ρ ρ} {b : Mx D ρ S₀.rank}
    (h1 : mt S n ⬝ d.jX = d.jX + d.jX ⬝ T) (h2 : mt S n ⬝ d.j0 = d.j0 + d.jX ⬝ b) :
    simpleSum d z n = superSum (fun _ => 1) T (b *ᵥ ratV z) := by
  rw [superSum_const, one_mul, simpleSum, blockX, coefX, h1, h2, Matrix.mul_add, Matrix.mul_add, d.pX_jX, d.pX_j0,
    cancel₂ d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul, Matrix.one_mul, zero_add, upSum_add, upSum_one, zero_add]

theorem simpleSum_mul (z : Fin S₀.rank → D.host.E) {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    simpleSum d z (n * n') = simpleSum d z n + simpleSum d z n' := by
  obtain ⟨T, b, hT, h1, h2⟩ := exists_blocks d hn
  obtain ⟨T', b', hT', h1', h2'⟩ := exists_blocks d hn'
  have e1 : mt S (n * n') ⬝ d.jX = d.jX + d.jX ⬝ (T + T' + T ⬝ T') := by
    rw [mt_mul]; exact GlobalTheory.BesselChar.mul_cols h1 h1'
  have e2 : mt S (n * n') ⬝ d.j0 = d.j0 + d.jX ⬝ (b + b' + T ⬝ b') := by
    rw [mt_mul, Matrix.mul_assoc, h2', Matrix.mul_add, h2, cancel₂ h1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  rw [simpleSum_eq d z e1 e2, simpleSum_eq d z h1 h2, simpleSum_eq d z h1' h2', Matrix.add_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, GlobalTheory.BesselChar.superSum_mul _ hT hT']

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem psiBes_mul (θ : D.host.E) (z : Fin S₀.rank → D.host.E) {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    psiBes ψ d θ z (n * n') = psiBes ψ d θ z n * psiBes ψ d θ z n' := by
  rw [psiBes, simpleSum_mul d z hn hn', mul_add, psiE_add]; rfl

theorem psiFlag_eq (n : GA D S) : psiFlag ψ d n = psiBes ψ d 1 0 n := by
  have h : ratV (0 : Fin S₀.rank → D.host.E) = 0 := funext fun _ => map_zero _
  rw [psiBes, simpleSum, coefX, h, Matrix.mulVec_zero, dotProduct_zero, add_zero, map_one, one_mul, psiFlag]

theorem psiFlag_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    psiFlag ψ d (n * n') = psiFlag ψ d n * psiFlag ψ d n' := by
  simp only [psiFlag_eq, psiBes_mul d ψ 1 0 hn hn']

end Struct

example (D : D7) : IsLineVec (diagSp D 1 ![true] 0 1) (fun _ => 1) := by
  refine ⟨rfl, ?_⟩
  rw [diagSp_gram]
  change ∑ i : Fin 1, star (1 : D.host.E) * ∑ j : Fin 1, Matrix.diagonal (fun i => Examples₂.sgn (![true] i)) i j * 1 ≠ 0
  simp [Examples₂.sgn]

example (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (d : HypDec S S₀ 0) (θ z n) : psiBes ψ d θ z n = 1 := by
  rw [psiBes, simpleSum, upSum, dotProduct, Finset.sum_of_isEmpty, Finset.sum_of_isEmpty, add_zero, mul_zero, psiE_zero]

example (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (d : HypDec S S₀ 1) (z) (b : Mx D 1 S₀.rank) :
    psiBes ψ d 1 z (d.nB b) = psiE ψ ((b *ᵥ ratV z) 0) := by
  rw [psiBes_nB, map_one, one_mul, dotProduct, Fin.sum_univ_one, show ell D 1 0 = 1 from rfl, one_mul]

example (T : Mx D 2 2) : upSum T = T 0 1 := by simp [upSum, Fin.sum_univ_two]

example (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)
    (c : skewA D ρ) (f : WO S₀ T → ℂ) : jacS ψ d T x (d.nC c) f = ψ (d.qS T c x) • f := by
  have h := ptS_nB_mul_nC d T x 0 c
  rw [d.nB_zero, one_mul, Matrix.mul_zero] at h
  rw [jacS, h, cenS_nC, heisO_zero]

end GlobalTheory.MixPer

end
