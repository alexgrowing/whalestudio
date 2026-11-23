import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

def RightInv : Prop :=
  ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (Γ : Subgroup H) [Countable Γ]
    (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (𝓕 : Set H),
    IsFundamentalDomain Γ 𝓕 ν → ∀ ψ : H → ℂ, (∀ γ ∈ Γ, ∀ h, ψ (γ * h) = ψ h) → ∀ k : H,
      (IntegrableOn (fun h => ψ (h * k)) 𝓕 ν ↔ IntegrableOn ψ 𝓕 ν) ∧
        ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ h in 𝓕, ψ h ∂ν

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnimodGA (V : HSp D) : Prop :=
  ∀ μ : Measure (GA D V), μ.IsHaarMeasure → μ.IsMulRightInvariant

def RightInvGA (V : HSp D) : Prop :=
  MeasurableMul (GA D V) → Countable (GQ V) → UnimodGA V →
    ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      Lev.IsMeasFD V K μ 𝓕 → ∀ ψ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ h, ψ (γ * h) = ψ h) → ∀ k : GA D V,
        (IntegrableOn (fun h => ψ (h * k)) 𝓕 μ ↔ IntegrableOn ψ 𝓕 μ) ∧
          ∫ h in 𝓕, ψ (h * k) ∂μ = ∫ h in 𝓕, ψ h ∂μ

end GA

def IoExistsOf : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds]
    [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))),
    (∀ F : CCs, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν) →
    (∀ F : CCs, ∃ u : CCt, ∀ φ v g,
      (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g = Lift.liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g) →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0) →
    Lift.IoExists ν 𝓕 th pt T CCs CCt

section Mult

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def IoUniqueAt : Prop :=
  ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : Mult.DSModel V S)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Kf : ∀ τ, Submodule ℂ (M.sm τ)) (Sinf Ds : Type) [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds]
    [Module ℂ Ds] (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ)),
    (∀ τ (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0) →
      ∀ w : M.sm τ, ℓ (w : M.H τ) = 0) →
    (∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, T φ w = x}) →
    ∀ u ∈ Mult.MultT θ M J χ, (∀ φ w, u (T φ w) = 0) → u = 0

def IoUniqueIo : Prop :=
  ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : Mult.DSModel V S)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Kf : ∀ τ, Submodule ℂ (M.sm τ)) (Sinf Ds : Type) [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds]
    [Module ℂ Ds] (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ)) (H S' : Type) [MeasurableSpace H] (ν : Measure H)
    (𝓕 : Set H) (th : GA D V → H → S' → ℂ) (pt : Sinf → S') (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (io io' : CCs →ₗ[ℂ] Mult.MultT θ M J χ),
    (∀ τ (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0) →
      ∀ w : M.sm τ, ℓ (w : M.H τ) = 0) →
    (∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, T φ w = x}) →
    Lift.IsIo ν 𝓕 th pt T CCs (Mult.MultT θ M J χ) io → Lift.IsIo ν 𝓕 th pt T CCs (Mult.MultT θ M J χ) io' →
      io = io'

end Mult

def rtr {H Ds : Type*} [Mul H] [AddCommGroup Ds] [Module ℂ Ds] (b : H) (F : Ds →ₗ[ℂ] (H → ℂ)) :
    Ds →ₗ[ℂ] (H → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun h => h * b) ∘ₗ F

def LiftEquiv : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H]
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]
    (Γ : Subgroup H) [Countable Γ] (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (𝓕 : Set H)
    (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt)
    (ι κ : Type) [Fintype ι] [Fintype κ] (b : ι → H) (c : ι → ℂ) (a : κ → G) (d : κ → ℂ),
    IsFundamentalDomain Γ 𝓕 ν →
    (∀ F : CCs, ∀ v, ∀ γ ∈ Γ, ∀ h, (F : Ds →ₗ[ℂ] (H → ℂ)) v (γ * h) = (F : Ds →ₗ[ℂ] (H → ℂ)) v h) →
    (∀ g φ, ∀ γ ∈ Γ, ∀ h, th g (γ * h) (pt φ) = th g h (pt φ)) →
    (∀ g h φ, ∑ i, c i * th g (h * (b i)⁻¹) (pt φ) = ∑ k, d k * th (g * a k) h (pt φ)) →
    (∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0) →
    Lift.IsIo ν 𝓕 th pt T CCs CCt io →
    ∀ F : CCs, (∀ i φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v (h * b i)) 𝓕 ν) →
      ∀ F' : CCs, (F' : Ds →ₗ[ℂ] (H → ℂ)) = ∑ i, c i • rtr (b i) (F : Ds →ₗ[ℂ] (H → ℂ)) →
        ∀ u : CCt, (u : Dt →ₗ[ℂ] (G → ℂ)) = ∑ k, d k • rtr (a k) ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) →
          io F' = u

def PeterssonLiftIdentity : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace G] [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) [SFinite ν] (𝓕 : Set H)
    (νG : Measure G) [SFinite νG] (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ)))
    (ipS : CCs →ₗ[ℂ] CCs →ₗ⋆[ℂ] ℂ) (ipT : CCt →ₗ[ℂ] CCt →ₗ⋆[ℂ] ℂ) (io : CCs →ₗ[ℂ] CCt) (up : CCt →ₗ[ℂ] CCs),
    Lift.AdjointLiftPeterssonIdentity ν 𝓕 νG 𝓕G th pt T Tp ipDs ipDt CCs CCt ipS ipT io up

def PeterssonNormOfUpLift : Prop :=
  ∀ (G H S Sinf Ds Dt : Type) [MeasurableSpace G] [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H)
    (νG : Measure G) (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S) (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds)
    (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ)))
    (ipS : CCs →ₗ[ℂ] CCs →ₗ⋆[ℂ] ℂ) (up : CCt →ₗ[ℂ] CCs),
    Lift.IsSchur ν 𝓕 ipDs CCs ipS → Lift.IsIoUp νG 𝓕G th pt Tp CCs CCt up →
    ∀ (u : CCt) φ v,
      Lift.pet ν 𝓕 (fun h => ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG)
          (fun h => ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG) =
        ipS (up u) (up u) * ipDs (Tp φ v) (Tp φ v)

end Formalism.IndefR.Eqv

end
