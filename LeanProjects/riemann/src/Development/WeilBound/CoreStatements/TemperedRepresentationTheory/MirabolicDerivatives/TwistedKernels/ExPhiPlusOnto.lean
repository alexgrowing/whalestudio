import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.BetaFun

noncomputable section

open Matrix GlobalTheory.PRep

namespace GlobalTheory.BZMir.Fun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SmPsiMinus : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (psiMinus k τ)

def SmPsiPlus : Prop :=
  ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin n) k) W), IsSmooth σ →
    IsSmooth (psiPlus k σ)

def SmPhiMinus : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V),
    IsSmooth τ → IsSmooth (phiMinus k ψ τ)

def SmPhiPlus : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Mir k n) W),
    IsSmooth (phiPlus k ψ σ) ∧ IsSmooth (phiHat k ψ σ)

def Exhaust : Prop :=
  ∀ (n : ℕ) (s : Finset (Mir k n)), (↑s : Set (Mir k n)) ⊆ MirUin k n →
    ∃ L : Subgroup (Mir k n), L ≤ MirUin k n ∧ (↑s : Set (Mir k n)) ⊆ L ∧ IsCompact (L : Set (Mir k n))

def ThetaOpen : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (a : Fin n → k), IsOpen ((thetaA k ψ a).ker : Set (MirUin k n))

def MirCharEq : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ), mirChar k ψ n = thetaA k ψ (Pi.single (Fin.last n) 1)

def ThetaConj : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (a : Fin n → k) (m : GL (Fin n) k) (u : MirUin k n),
    ∃ h : levi k n m * (u : Mir k n) * (levi k n m)⁻¹ ∈ MirUin k n,
      thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k)) u = thetaA k ψ a ⟨_, h⟩

def TwKerConj : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (a : Fin n → k) (m : GL (Fin n) k) (v : V),
    v ∈ twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ↔
      τ (levi k n m) v ∈ twKer τ (MirUin k n) (thetaA k ψ a)

def Fourier : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V), IsSmooth τ → ∀ v : V,
      (∀ a : Fin n → k, v ∈ twKer τ (MirUin k n) (thetaA k ψ a)) → v = 0

def ExPsiMinus : Prop :=
  ∀ (n : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃]
    [Module ℂ V₃] (τ₁ : Representation ℂ (Mir k n) V₁) (τ₂ : Representation ℂ (Mir k n) V₂)
    (τ₃ : Representation ℂ (Mir k n) V₃), IsSmooth τ₁ → IsSmooth τ₂ → IsSmooth τ₃ →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (τ₁ x v) = τ₂ x (f v)) (hg : ∀ x v, g (τ₂ x v) = τ₃ x (g v)),
      LinearMap.range f = LinearMap.ker g →
      LinearMap.range (twMap τ₁ τ₂ (MirUin k n) 1 f hf) = LinearMap.ker (twMap τ₂ τ₃ (MirUin k n) 1 g hg)

def ExPhiMinus : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
    [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (τ₁ : Representation ℂ (Mir k (n + 1)) V₁)
    (τ₂ : Representation ℂ (Mir k (n + 1)) V₂) (τ₃ : Representation ℂ (Mir k (n + 1)) V₃),
    IsSmooth τ₁ → IsSmooth τ₂ → IsSmooth τ₃ →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (τ₁ x v) = τ₂ x (f v)) (hg : ∀ x v, g (τ₂ x v) = τ₃ x (g v)),
      LinearMap.range f = LinearMap.ker g →
      LinearMap.range (twMap τ₁ τ₂ (MirUin k (n + 1)) (mirChar k ψ n) f hf) =
        LinearMap.ker (twMap τ₂ τ₃ (MirUin k (n + 1)) (mirChar k ψ n) g hg)

def ExPhiPlusOnto : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (Mir k n) W) (σ' : Representation ℂ (Mir k n) W'), IsSmooth σ → IsSmooth σ' →
    ∀ (f : W →ₗ[ℂ] W'), Function.Surjective f → (∀ x w, f (σ x w) = σ' x (f w)) →
    ∀ F : cIndSpace (Q k n) (qRep k ψ σ'), ∃ F' : cIndSpace (Q k n) (qRep k ψ σ),
      ∀ g, f ((F' : smoothPart (ind (Q k n) (qRep k ψ σ))).1.1 g) = (F : smoothPart (ind (Q k n) (qRep k ψ σ'))).1.1 g

def ExPhiPlusKer : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (W₁ W₂ W₃ : Type) [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] (σ₁ : Representation ℂ (Mir k n) W₁) (σ₂ : Representation ℂ (Mir k n) W₂)
    (σ₃ : Representation ℂ (Mir k n) W₃), IsSmooth σ₁ → IsSmooth σ₂ → IsSmooth σ₃ →
    ∀ (f : W₁ →ₗ[ℂ] W₂) (g : W₂ →ₗ[ℂ] W₃), (∀ x w, f (σ₁ x w) = σ₂ x (f w)) → (∀ x w, g (σ₂ x w) = σ₃ x (g w)) →
      LinearMap.range f = LinearMap.ker g →
    ∀ F : cIndSpace (Q k n) (qRep k ψ σ₂), (∀ x, g ((F : smoothPart (ind (Q k n) (qRep k ψ σ₂))).1.1 x) = 0) →
      ∃ F₁ : cIndSpace (Q k n) (qRep k ψ σ₁),
        ∀ x, f ((F₁ : smoothPart (ind (Q k n) (qRep k ψ σ₁))).1.1 x) = (F : smoothPart (ind (Q k n) (qRep k ψ σ₂))).1.1 x

def AdjPsi : Prop :=
  ∀ (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k n) V)
    (σ : Representation ℂ (GL (Fin n) k) W),
    ∃ e : Representation.IntertwiningMap (psiMinus k τ) σ ≃ Representation.IntertwiningMap τ (psiPlus k σ),
      ∀ f v, e f v = f (Submodule.Quotient.mk v)

def AdjPhi : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k (n + 1)) V) (σ : Representation ℂ (Mir k n) W), IsSmooth τ →
    ∃ e : Representation.IntertwiningMap (phiMinus k ψ τ) σ ≃ Representation.IntertwiningMap τ (phiHat k ψ σ),
      ∀ f v, (e f v).1.1 1 = f (Submodule.Quotient.mk v)

def CompPsiPsi : Prop :=
  ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin n) k) W),
    Nonempty (Representation.Equiv (psiMinus k (psiPlus k σ)) σ)

def CompPhiPsi : Prop :=
  ∀ (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin (n + 1)) k) W),
    Subsingleton (TwJacquet (psiPlus k σ) (MirUin k (n + 1)) (mirChar k ψ n))

def CompPsiPhi : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Mir k n) W), IsSmooth σ →
    Subsingleton (TwJacquet (phiPlus k ψ σ) (MirUin k (n + 1)) 1)

def CompPhiPhi : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Mir k n) W), IsSmooth σ →
    ∃ e : Representation.Equiv (phiMinus k ψ (phiPlus k ψ σ)) σ,
      ∀ F : cIndSpace (Q k n) (qRep k ψ σ),
        e (Submodule.Quotient.mk F) = (F : smoothPart (ind (Q k n) (qRep k ψ σ))).1.1 1

def BetaInd : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V)
    (v : V), betaFun ψ τ v ∈ indSpace (Q k n) (qRep k ψ (phiMinus k ψ τ))

def BetaSmooth : Prop :=
  ∀ (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (n + 1)) V),
    IsSmooth τ → ∀ v : V, IsOpen {g : Mir k (n + 1) | ∀ x, betaFun ψ τ v (x * g) = betaFun ψ τ v x}

def BetaCompact : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V), IsSmooth τ → ∀ v ∈ twKer τ (MirUin k (n + 1)) 1,
      ∃ C : Set (Mir k (n + 1)), IsCompact C ∧ ∀ g, betaFun ψ τ v g ≠ 0 → ∃ h ∈ Q k n, ∃ c ∈ C, g = h * c

def BetaInj : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V), IsSmooth τ → ∀ v ∈ twKer τ (MirUin k (n + 1)) 1,
      (∀ g, betaFun ψ τ v g = 0) → v = 0

def BetaOnto : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V), IsSmooth τ →
    ∀ F : cIndSpace (Q k n) (qRep k ψ (phiMinus k ψ τ)), ∃ v ∈ twKer τ (MirUin k (n + 1)) 1,
      ∀ g, betaFun ψ τ v g = (F : smoothPart (ind (Q k n) (qRep k ψ (phiMinus k ψ τ)))).1.1 g

def FunSeq : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V), IsSmooth τ →
    ∃ ι : Representation.IntertwiningMap (phiPlus k ψ (phiMinus k ψ τ)) τ,
      Function.Injective ι ∧ LinearMap.range ι.toLinearMap = twKer τ (MirUin k (n + 1)) 1

end GlobalTheory.BZMir.Fun

end
