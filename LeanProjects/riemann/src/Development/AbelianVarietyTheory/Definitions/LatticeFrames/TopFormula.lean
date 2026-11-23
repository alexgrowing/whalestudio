import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.HermitianForms.TiedSym

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

def HasMat (h : GA D D.sp.X')
    (y : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  h ∈ GfC D.sp.X' ∧ ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j = y.1 (finCongr (rankP D) i) (finCongr (rankP D) j)

def TopLev (K : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : K.lev.U, HasMat h κ.1) ∧ ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ)

open Classical in

structure IsJ (u : D.what₂.Word) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) : Prop where
  inj : Function.Injective j
  range : LinearMap.range j = ValC (gramC (gramP D) (embT D)) (sgT u)
  eqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
    ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
      j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y'

open Classical in

def TopFormula {K : ClsPTied u} (V : ValPTied u K) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ))
    (eT : (D.mem u).P.Mt → SmT M →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  ∀ (F : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), HasMat h (K.y c).1 →
    eT F v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (V.eW.symm (Pi.single c (j v))) F

end GlobalTheory.Core.Rk.Top

end
