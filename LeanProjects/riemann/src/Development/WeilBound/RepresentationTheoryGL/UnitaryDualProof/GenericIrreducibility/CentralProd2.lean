import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SwapProducts.SwapProd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FactorIrr : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), IsSmooth A → IsSmooth B →
    (prod₂ A B).IsIrreducible → A.IsIrreducible ∧ B.IsIrreducible

def Comm2Irr : Prop :=
  ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N),
    (prodIrr ![x, y] hd).IsIrreducible → (prodIrr ![y, x] hd').IsIrreducible

def MoveLast : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (prodIrr x hd).IsIrreducible → ∀ j : Fin h,
    ∃ (y : IrrGL k) (hd2 : ∑ a, (![y, x j] a).1 = N), Nonempty ((prodIrr x hd).Equiv (prodIrr ![y, x j] hd2))

def MoveFirst : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (prodIrr x hd).IsIrreducible → ∀ j : Fin h,
    ∃ (y : IrrGL k) (hd2 : ∑ a, (![x j, y] a).1 = N), Nonempty ((prodIrr x hd).Equiv (prodIrr ![x j, y] hd2))

def ThetaProd : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), IsSmooth A → IsSmooth B →
    Nonempty (Representation.Equiv ((prod₂ A B).comp (Zc.Cos.thetaW k (r + t)))
      (ind₂ (stdSum (add_comm t r)) (extTensor (B.comp (Zc.Cos.thetaW k t)) (A.comp (Zc.Cos.thetaW k r)))))

def ThetaFacts : Prop :=
  (∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsGeneric π → IsGeneric (π.comp (Zc.Cos.thetaW k N))) ∧
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (ω : kˣ →* ℂˣ),
    HasCentralChar π ω → HasCentralChar (π.comp (Zc.Cos.thetaW k N)) ω⁻¹

def CentralProd2 : Prop :=
  ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (ω ω' : kˣ →* ℂˣ), HasCentralChar x.rep ω →
    HasCentralChar y.rep ω' → HasCentralChar (prodIrr ![x, y] hd) (ω * ω')

end PositivityTheory.RgUd.Exp
