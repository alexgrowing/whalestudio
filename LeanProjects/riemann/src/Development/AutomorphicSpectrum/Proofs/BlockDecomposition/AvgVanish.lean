import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

section Abstract

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def AvgVanish (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ) (p : G) : Prop :=
  ∃ (L : Subgroup G) (hL : L ≤ U), IsCompact (L : Set G) ∧ ∃ g : cIndSpace H σ,
    f - g ∈ twKer (cInd H σ) L (θ.comp (Subgroup.inclusion hL)) ∧
    (∀ l : L, cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL l) : ℂˣ) : ℂ) • g) ∧
    ∀ u ∈ U, (g : smoothPart (ind H σ)).1.1 (p * u) = 0

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def piPerm (i t : ℕ) : Equiv.Perm (Fin ((i + 1) + t + 1)) :=
  (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)).trans ((ePG i (t + 1)).symm.trans (eGP (i + 1) t))

variable (k) in

def wGL (i t : ℕ) : GL (Fin ((i + 1) + t + 1)) k where
  val := Equiv.Perm.permMatrix k (piPerm i t)⁻¹
  inv := Equiv.Perm.permMatrix k (piPerm i t)
  val_inv := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

variable (k) in

def wEl (i t : ℕ) : Mir k ((i + 1) + t + 1) := levi k _ (wGL k i t)

variable (k) in

def sEmb (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

variable (k) in

def dEmb (i t : ℕ) (d : Fin (t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)), MirU_le_Mir k _ ⟨_, rfl⟩⟩

variable (k) in

def Cl (i t : ℕ) : Set (Mir k ((i + 1) + t + 1)) :=
  {p | ∀ c : Fin (i + 1), (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0}

variable (k) in

def castM {a b : ℕ} (h : a = b) : Mir k a ≃* Mir k b := h ▸ MulEquiv.refl _

section Fibre

variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

abbrev sigX : Representation ℂ (HPG k (i + 1) (t + 1)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k (i + 1) (t + 1))

abbrev XS : Submodule ℂ (smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))) := cIndSpace (HPG k (i + 1) (t + 1)) (sigX τ σ)

abbrev evX {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (p : Mir k ((i + 1) + (t + 1))) : τ.V ⊗[ℂ] σ.V :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.1 p

abbrev sigC : Representation ℂ (MirabolicParabolic k (i + 1) t) ((psiN τ).V ⊗[ℂ] σ.V) :=
  (extTensor ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k (i + 1) t)

abbrev sigO (ψ : AddChar k Circle) : Representation ℂ (HPG k i (t + 1)) ((phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (t + 1))

def qC : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ

def qO (ψ : AddChar k Circle) : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ

variable (k) in

def muD (t : ℕ) : @MeasureTheory.Measure (Fin t → k) (borel _) :=
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  MeasureTheory.Measure.addHaar

def intC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
    (fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))

def intO {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => evX f (dEmb k i t d * y))

def eC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    (psiN τ).V ⊗[ℂ] σ.V :=
  ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))

def eO (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    (phiN ψ τ).V ⊗[ℂ] σ.V :=
  ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
    qO τ σ ψ (intO f (wEl k i t * sEmb k _ (castM k (by omega) m)))

end Fibre

end GlobalTheory.CompanionTheory.BZPhiPG

end
