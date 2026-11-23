import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FB

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

def x0 (B : BesLev D σ) : Mx D B.V.rank (σ + 1) := xLast B.d (vecB B.o B.ζ)

def zl (B : BesLev D σ) : Mx D B.L.rank (σ + 1) := zEll B.L (σ + 1) B.ζ

def orb (B : BesLev D σ) : Set (Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B)}

def Quasi (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (y : WO S L → ℂ) : Prop :=
  (∀ γ w, y (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * y w) ∧ Continuous y

def RQ (B : BesLev D σ) : Subgroup (GQ B.V) := (besGrp B.d B.o).subgroupOf (GQ B.V)

abbrev Cos (B : BesLev D σ) : Type := GQ B.V ⧸ RQ B

def rep {B : BesLev D σ} (q : Cos B) : GA D B.V := ((q.out : GQ B.V) : GA D B.V)⁻¹

def th (J : JacLev D (σ + 1)) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ) (n : GA D J.W) : ℂ :=
  star (jacS ψ J.d B.L (zl B) n y 0) * star (psiFlag ψ J.d n)

variable {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)

def term (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) : WO J.W₀ B.V → ℂ := J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ x

def kerN (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) : ℂ :=
  ∫ n in J.vN.𝓝, th J ψ B y n.1 * s.om (n.1, 1) Ψ 0 ∂J.vN.ν

def bFun (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) (b : Mx D (σ + 1) J.W₀.rank) : ℂ :=
  term s Ψ x (x ⬝ b) * star (y (zl B ⬝ b))

def bTerm (vB : VolM D (σ + 1) J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) : ℂ :=
  ∫ b in vB.𝓕, bFun s y Ψ x b ∂vB.μ

def uFun (vB : VolM D (σ + 1) J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1))
    (u : UX D (σ + 1)) : ℂ :=
  star (psiUni ψ u.1) * bTerm s vB y (s.om (J.d.levi u.1, 1) Ψ) x

def tFlat (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) : ℂ :=
  contractT B.o J.W₀ vL.μ vL.𝓕 (flatFB s Ψ) y 0

def unfF (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ)
    (h : GA D B.V) : ℂ :=
  G h * handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1

theorem quasi_of_fam {S L : HSp D} {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) (h : GA D S) : Quasi ψ S L (Y h) :=
  ⟨hY.quasi h, hY.cont.comp (Continuous.prodMk_right h)⟩

end GlobalTheory.Unf.FB

end
