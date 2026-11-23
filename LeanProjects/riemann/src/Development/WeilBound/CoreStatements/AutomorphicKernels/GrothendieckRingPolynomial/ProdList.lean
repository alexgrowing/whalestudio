import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def cl0 {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : GrothGL k :=
  if h : HasFiniteLength π then clsGL π h else 0

def sg (x : IrrGL k) : GrothGL k := Finsupp.single x 1

def mulR (a b : GrothGL k) : GrothGL k :=
  a.sum fun x m => b.sum fun y n => (m * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))

def J (W : List (IrrGL k)) (a : GrothGL k) : ℤ := a.sum fun x m => m * ((jmL W (IrrGL.rep x)).toNat : ℤ)

def sq (𝔪 : Multiset (Segment k)) : ℕ := (𝔪.map fun Δ => Δ.len ^ 2).sum

def vWord (Δ : Segment k) (S : Finset (Fin Δ.len)) : List (IrrGL k) :=
  (((List.finRange Δ.len).filter fun a => a ∈ S).reverse ++ (List.finRange Δ.len).filter fun a => a ∉ S).map Δ.term

def vSets (Δ : Segment k) : Finset (Finset (Fin Δ.len)) := Finset.univ.filter fun S => ∀ a ∈ S, (a : ℕ) ≠ 0

variable (k)

structure Cls : Prop where
  ex : ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL k, IsL 𝔪 x.rep
  exh : ∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep
  free : LOrderFree k
  soc : LSocleGL k
  jac : LSegJacquet k
  seg : LSegExists k
  unl : LUnlinkedIrr k
  com : LUnlinkedComm k

def MulCls : Prop := ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
  HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ →
    HasFiniteLength (prod₂ π₁ π₂) ∧ cl0 (prod₂ π₁ π₂) = mulR (cl0 π₁) (cl0 π₂)

def Assoc : Prop := ∀ x y z : IrrGL k, mulR (mulR (sg x) (sg y)) (sg z) = mulR (sg x) (mulR (sg y) (sg z))

def Comm : Prop := ∀ x y : IrrGL k, cl0 (prod₂ x.rep y.rep) = cl0 (prod₂ y.rep x.rep)

def One : Prop := ∀ x : IrrGL k, mulR (GrothGL.unit k) (sg x) = sg x

def ProdList : Prop := ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
  cl0 (prodIrr x hd) = (List.ofFn x).foldr (fun y a => mulR (sg y) a) (GrothGL.unit k)

def Tri : Prop := ∀ (𝔪 𝔫 : Multiset (Segment k)) (h : ℕ) (x : Fin h → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
  LFactors 𝔪 x → IsL 𝔫 y.rep → jhMult y.rep (prodIrr x hd) ≠ 0 → msupp 𝔪 = msupp 𝔫 ∧ (𝔪 = 𝔫 ∨ sq 𝔪 < sq 𝔫)

def MultOne : Prop := ∀ (𝔪 : Multiset (Segment k)) (h : ℕ) (x : Fin h → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
  LFactors 𝔪 x → IsL 𝔪 y.rep → jhMult y.rep (prodIrr x hd) = 1

def JCls : Prop := ∀ (W : List (IrrGL k)) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
  IsSmooth π → HasFiniteLength π → jmL W π ≠ ⊤ ∧ J W (cl0 π) = ((jmL W π).toNat : ℤ)

def JSeg : Prop := ∀ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z → ∀ Δ : Segment k,
  jmL (List.ofFn Δ.term) (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) = 1 ∧
    ∀ S ∈ vSets Δ, S ≠ ∅ → jmL (vWord Δ S) (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) = 0

open Classical in

def AltSum : Prop := ∀ (Δ : Segment k) (h : ℕ) (Γ : Fin h → Segment k),
  ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ) =
    if Finset.univ.val.map Γ = {Δ} then (-1) ^ (Δ.len - 1) else 0

end PositivityTheory.Groth

namespace PositivityTheory.Groth

def TriAut : Prop := ∀ (σ : Type 1) (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ),
  (∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧ ψ (MvPolynomial.X s) = (ε : ℤ) • MvPolynomial.X s + p) →
    Function.Bijective ψ

def UniTri : Prop := ∀ (M I C : Type 1) (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ), (∀ m, w m ≤ b (c m)) →
  (∀ m, f m (L m) = 1) → (∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) →
    Function.Bijective (Finsupp.linearCombination ℤ f) ∧
      ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧ Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1

end PositivityTheory.Groth

end
