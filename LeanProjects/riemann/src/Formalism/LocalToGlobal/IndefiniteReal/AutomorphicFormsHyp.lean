import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Filter Topology
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.AutomorphicFormsHyp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section General

variable {N : ℕ}

def hK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AE D :=
  ∑ a, ∑ b, cA D (y a 0) * incA D (K a b) * x b 0

def symplK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hK K x y)

def symplKH (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * symplK K x y

def heisK (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (w₀ : Mx D N 1) (f : Mx D N 1 → ℂ) :
    Mx D N 1 → ℂ :=
  fun w => ψ (symplKH K w w₀) * f (w + w₀)

def ratK (D : D7) (N : ℕ) : AddSubgroup (Mx D N 1) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin N) (n := Fin 1)).range

abbrev UK (D : D7) (K : Matrix (Fin N) (Fin N) D.host.E) : Type := HA (AF D.host.F) D.sp.cm.sig K

def ratU (K : Matrix (Fin N) (Fin N) D.host.E) : Subgroup (UK D K) := HFinIn (AF D.host.F) D.sp.cm.sig K

def actK (K : Matrix (Fin N) (Fin N) D.host.E) (g : UK D K) (x : Mx D N 1) : Mx D N 1 :=
  HMul.hMul ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) x

structure IsL2ThetaVector (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (μ : Measure (Mx D N 1))
    (𝓕 : Set (Mx D N 1)) (f : Mx D N 1 → ℂ) : Prop where
  quasi : ∀ γ ∈ ratK D N, ∀ w, f (γ + w) = ψ (-(symplKH K γ w)) * f w
  meas : AEStronglyMeasurable f μ
  fin : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ ≠ ⊤

structure IsL2SplittingUnitary (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (μ : Measure (Mx D N 1))
    (𝓕 : Set (Mx D N 1)) (om : UK D K → Module.End ℂ (Mx D N 1 → ℂ)) : Prop where
  pres : ∀ g f, IsL2ThetaVector ψ K μ 𝓕 f → IsL2ThetaVector ψ K μ 𝓕 (om g f)
  unit : ∀ g f, IsL2ThetaVector ψ K μ 𝓕 f → ∫⁻ w in 𝓕, ‖om g f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  one : ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → om 1 f =ᵐ[μ] f
  mul : ∀ g g' f, IsL2ThetaVector ψ K μ 𝓕 f → om (g * g') f =ᵐ[μ] om g (om g' f)
  Heisenberg₂ : ∀ g w₀ f, IsL2ThetaVector ψ K μ 𝓕 f → om g (heisK ψ K w₀ f) =ᵐ[μ] heisK ψ K (actK K g w₀) (om g f)
  rat : ∀ γ ∈ ratU K, ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → om γ f =ᵐ[μ] fun w => f (actK K γ⁻¹ w)
  cont : ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → ∀ g₀,
    Tendsto (fun g => ∫⁻ w in 𝓕, ‖om g f w - om g₀ f w‖ₑ ^ 2 ∂μ) (𝓝 g₀) (𝓝 0)

end General

def GelbartRogawskiSplit (D : D7) : Prop :=
  ∀ (s : ℤ) (ψ : AddChar (AF D.host.F) ℂ), (s = 1 ∨ s = -1) → IsStdChar D ψ s →
    ∀ (N : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 →
      ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ 1 →
        ∀ (μ : Measure (Mx D N 1)) (𝓕 : Set (Mx D N 1)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratK D N) 𝓕 μ →
          ∃ om : UK D K → Module.End ℂ (Mx D N 1 → ℂ), IsL2SplittingUnitary ψ K μ 𝓕 om

def WeilExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

structure IsL2ThetaPair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (f : WO S T → ℂ) : Prop where
  quasi : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w
  meas : AEStronglyMeasurable f μ
  fin : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ ≠ ⊤

structure IsL2SplittingPair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (om : GA D S × GA D T → Module.End ℂ (WO S T → ℂ)) : Prop where
  pres : ∀ p f, IsL2ThetaPair ψ S T μ 𝓕 f → IsL2ThetaPair ψ S T μ 𝓕 (om p f)
  unit : ∀ p f, IsL2ThetaPair ψ S T μ 𝓕 f → ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  one : ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f → om 1 f =ᵐ[μ] f
  mul : ∀ p p' f, IsL2ThetaPair ψ S T μ 𝓕 f → om (p * p') f =ᵐ[μ] om p (om p' f)
  Heisenberg₂ : ∀ g h w₀ f, IsL2ThetaPair ψ S T μ 𝓕 f →
    om (g, h) (heisO ψ S T w₀ f) =ᵐ[μ] heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  rat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f →
    om (γ, γ') f =ᵐ[μ] fun w => f (actO S T γ⁻¹ γ'⁻¹ w)
  cont : ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f → ∀ p₀,
    Tendsto (fun p => ∫⁻ w in 𝓕, ‖om p f w - om p₀ f w‖ₑ ^ 2 ∂μ) (𝓝 p₀) (𝓝 0)

def WeilL2SplittingExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∃ om : GA D S × GA D T → Module.End ℂ (WO S T → ℂ), IsL2SplittingPair ψ S T μ 𝓕 om

structure IsWeilPreO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  om_pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  om_heis : ∀ g h w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  om_aut : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → om (γ, γ') f 0 = f 0
  om_cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  om_unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

def WeilPreExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilPreO ψ S T om

def HeckeEtaExists (D : D7) : Prop := ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ 1

def StepVecO (D : D7) : Prop := GelbartRogawskiSplit D → HeckeEtaExists D → WeilL2SplittingExists D

def StepSmoothO (D : D7) : Prop := WeilL2SplittingExists D → WeilPreExistsO D

def StepCharO (D : D7) : Prop := GelbartRogawskiSplit D → HeckeEtaExists D → WeilPreExistsO D → WeilExistsO D

end Formalism.IndefR.AutomorphicFormsHyp

end
