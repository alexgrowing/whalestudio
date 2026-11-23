import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LatticeEmbeddingHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjEquivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OrthogonalFrameIff

noncomputable section

namespace GlobalTheory.DictPinCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase IsLatEmb IsModelOf IsOrthoFrame IsArchAt IsRatUnitary ratTo LatMark
  IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver)
open Formalism.L2.PjFree (Unf.ofPj)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def formOf (V : HSp D) : V.V →ₛₗ[conjHom D.host.E] V.V →ₗ[D.host.E] D.host.E := V.hT

section Record

variable (T : Formalism.L2.Pj.Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ)

def SideLaws (hr : (T.V j σ).rank = D.R.r) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop :=
  (∀ k, Formalism.L2.Pj.ModelW (T.V j σ) hr ((T.U j σ).X k)) ∧ (∀ k, Formalism.L2.Pj.IsOrthogonalFrame ((T.U j σ).X k) x₀) ∧
    Formalism.L2.Pj.KfHalf (T.V j σ) (T.Kf j σ) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ∧
    ∀ k, ((T.U j σ).X k).p0 = (T.Q.Dw j).q ∧
      ∀ τ : D.host.E →+* ℂ, τ ∈ ((T.U j σ).X k).Ψ ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0

def AdPinAnd (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (ι₀ : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E))
    (Q : ∀ k, ((T.Q.Dw j).La → ((T.U j σ).X k).Λ) → Prop) : Prop :=
  ∃ (hr : (T.V j σ).rank = D.R.r)
    (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
    (F : FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
      (fun i => Formalism.L2.Pj.relab T.Q.c σ (e i).1))
    (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
    (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    (Formalism.L2.Pj.LatEmb (T.V j σ) ι ∧ Formalism.L2.Pj.LatIsom (T.V j σ) (T.Q.Dw j).EF ι ∧
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      Formalism.L2.Pj.DictLat (T.U j σ) (T.V j σ) hr (T.dict j σ) ι e F ik φ th x₀) ∧
    ∀ k, Q k fun a => φ k (F.t (ik k) a)

def SecondPin (hr : (T.V j σ).rank = D.R.r) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.AdPin D.host.F hr (T.V j σ).frame (T.V j σ).hD (T.V j σ).L0
    (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) D.host.xi0 (Unf.ofPj (T.U j σ)) (infHom (T.V j σ)) (finHom (T.V j σ))
    (T.dict j σ) (T.Kf j σ)

end Record

end GlobalTheory.DictPinCompare
