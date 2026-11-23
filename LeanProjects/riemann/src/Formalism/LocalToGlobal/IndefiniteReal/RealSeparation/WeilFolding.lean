import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.MajIter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rInt (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μX : Measure (NI S CS)) (𝓕X : Set (NI S CS)) (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)) (ν : Measure (GA D S))
    (β : GA D S → ℝ) (Φ : GA D S → ℂ) : ℂ :=
  ∫ h, (β h : ℂ) * ∫ p in 𝓕X ×ˢ 𝓕0, Φ ((p.1 : GA D S) * lev p.2 * h) ∂(μX.prod μ0) ∂ν

def CutoffExistence (D : D7) : Prop :=
  MajIter D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T → Continuous ψ → PsiRat ψ →
  ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau →

  ∀ (A : HSp D) (ι : A.V →ₗ[D.host.E] T.V) (d : BesDat A T ι) (s : GA D A →* GA D T),
    HSpace.IsIsomEmb A T ι → IsEmbHom ι s → (∀ i, d.c i = 1) → (d.y : GA D T) = 1 →
  ∀ (μH : Measure (GA D A)) (𝓕H : Set (GA D A)), IsQuotPair A μH 𝓕H →
  (∃ K : Set (GA D A), IsCompact K ∧ ∀ g ∈ 𝓕H, ∃ a ∈ GinfC A, ∃ k ∈ K, g = a * k) →
  ∀ (μN : Measure (NFlag T d.e)) (𝓕N : Set (NFlag T d.e)), IsNPair d μN 𝓕N →

  ∀ (C' : Matrix (Fin T.rank) (Fin d.ρ) D.host.E) (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E),
    IsQuotFrame T d.e C' T0 B0 →
  ∀ z0 : Fin T0.rank → D.host.E, B0.mulVec z0 = d.z →
  ∀ ιH : GA D A →* GA D T0, (∀ h, IsLeviEmb T d.e C' T0 B0 (ιH h) (s h)) →

  ∀ (CS CS' : Matrix (Fin S.rank) (Fin d.ρ) D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
    IsQuotFrame S CS CS' S0 BS →
  ∀ lev : GA D S0 →* GA D S, (∀ h, IsLeviEmb S CS CS' S0 BS h (lev h)) →

  ∀ (μ : Measure (Mx D d.ρ S.rank)) (𝓕 : Set (Mx D d.ρ S.rank)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratMx D d.ρ S.rank) 𝓕 μ → μ 𝓕 = 1 →
  ∀ (μS : Measure (Mx D T0.rank d.ρ)) (𝓕S : Set (Mx D T0.rank d.ρ)), μS.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratMx D T0.rank d.ρ) 𝓕S μS → μS 𝓕S = 1 →
  ∀ om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ), IsDescOf ψ S T d.e C' T0 B0 μ 𝓕 om om0 →
  ∀ om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ), IsDescSOf ψ S T0 CS CS' S0 BS μS 𝓕S om0 om00 →

  ∀ (ν : Measure (GA D S)) (𝓕W : Set (GA D S)), IsQuotPair S ν 𝓕W →
  (∃ K : Set (GA D S), IsCompact K ∧ ∀ g ∈ 𝓕W, ∃ a ∈ GinfC S, ∃ k ∈ K, g = a * k) →
  ∀ (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)), IsQuotPair S0 μ0 𝓕0 →
  ∀ (μX : Measure (NI S CS)) (𝓕X : Set (NI S CS)), μX.IsHaarMeasure → IsFundamentalDomain (NIQ S CS) 𝓕X μX →
    μX 𝓕X = 1 →
  ∀ (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)), μU.IsHaarMeasure →
    IsFundamentalDomain (MUQ S CS CS' S0 BS) 𝓕U μU → μU 𝓕U = 1 →

  ∀ φ : GA D A → ℂ, IsAutFun A φ → (∀ a : ℕ, IntegrableOn (fun h => normInf θ A h ^ a * ‖φ h‖) 𝓕H μH) →
  ∀ G : GA D S → ℂ, IsAutFun S G → (∀ N : ℕ, ∃ c : ℝ, ∀ g ∈ 𝓕W, ‖G g‖ * normInf θ S g ^ N ≤ c) →
    (∃ N : ℕ, IntegrableOn (fun g => (normInf θ S g)⁻¹ ^ N) 𝓕W ν) →
  ∀ f, IsThetaFunO ψ S T f →
    ∃ β, IsCutoff S S0 CS lev μX μ0 β

def WeilFolding (D : D7) : Prop :=
  MajIter D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T → Continuous ψ → PsiRat ψ →
  ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau →

  ∀ (A : HSp D) (ι : A.V →ₗ[D.host.E] T.V) (d : BesDat A T ι) (s : GA D A →* GA D T),
    HSpace.IsIsomEmb A T ι → IsEmbHom ι s → (∀ i, d.c i = 1) → (d.y : GA D T) = 1 →
  ∀ (μH : Measure (GA D A)) (𝓕H : Set (GA D A)), IsQuotPair A μH 𝓕H →
  (∃ K : Set (GA D A), IsCompact K ∧ ∀ g ∈ 𝓕H, ∃ a ∈ GinfC A, ∃ k ∈ K, g = a * k) →
  ∀ (μN : Measure (NFlag T d.e)) (𝓕N : Set (NFlag T d.e)), IsNPair d μN 𝓕N →

  ∀ (C' : Matrix (Fin T.rank) (Fin d.ρ) D.host.E) (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E),
    IsQuotFrame T d.e C' T0 B0 →
  ∀ z0 : Fin T0.rank → D.host.E, B0.mulVec z0 = d.z →
  ∀ ιH : GA D A →* GA D T0, (∀ h, IsLeviEmb T d.e C' T0 B0 (ιH h) (s h)) →

  ∀ (CS CS' : Matrix (Fin S.rank) (Fin d.ρ) D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
    IsQuotFrame S CS CS' S0 BS →
  ∀ lev : GA D S0 →* GA D S, (∀ h, IsLeviEmb S CS CS' S0 BS h (lev h)) →

  ∀ (μ : Measure (Mx D d.ρ S.rank)) (𝓕 : Set (Mx D d.ρ S.rank)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratMx D d.ρ S.rank) 𝓕 μ → μ 𝓕 = 1 →
  ∀ (μS : Measure (Mx D T0.rank d.ρ)) (𝓕S : Set (Mx D T0.rank d.ρ)), μS.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratMx D T0.rank d.ρ) 𝓕S μS → μS 𝓕S = 1 →
  ∀ om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ), IsDescOf ψ S T d.e C' T0 B0 μ 𝓕 om om0 →
  ∀ om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ), IsDescSOf ψ S T0 CS CS' S0 BS μS 𝓕S om0 om00 →

  ∀ (ν : Measure (GA D S)) (𝓕W : Set (GA D S)), IsQuotPair S ν 𝓕W →
  (∃ K : Set (GA D S), IsCompact K ∧ ∀ g ∈ 𝓕W, ∃ a ∈ GinfC S, ∃ k ∈ K, g = a * k) →
  ∀ (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)), IsQuotPair S0 μ0 𝓕0 →
  ∀ (μX : Measure (NI S CS)) (𝓕X : Set (NI S CS)), μX.IsHaarMeasure → IsFundamentalDomain (NIQ S CS) 𝓕X μX →
    μX 𝓕X = 1 →
  ∀ (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)), μU.IsHaarMeasure →
    IsFundamentalDomain (MUQ S CS CS' S0 BS) 𝓕U μU → μU 𝓕U = 1 →

  ∀ φ : GA D A → ℂ, IsAutFun A φ → (∀ a : ℕ, IntegrableOn (fun h => normInf θ A h ^ a * ‖φ h‖) 𝓕H μH) →
  ∀ G : GA D S → ℂ, IsAutFun S G → (∀ N : ℕ, ∃ c : ℝ, ∀ g ∈ 𝓕W, ‖G g‖ * normInf θ S g ^ N ≤ c) →
    (∃ N : ℕ, IntegrableOn (fun g => (normInf θ S g)⁻¹ ^ N) 𝓕W ν) →
  ∀ f, IsThetaFunO ψ S T f →
    ∀ ε : D.host.E, (ε = 1 ∨ ε = -1) → (∀ F, IsThetaFunO ψ S T F → ∀ n ∈ NI T d.e,
        xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (1, n) F) 0 =
          besChar ψ d n * xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) F 0) → ∀ β, IsCutoff S S0 CS lev μX μ0 β →
      (∀ h, BSharpAbs ψ S T0 CS CS' S0 BS A lev ιH om00 (yMat T0 d.ρ ε z0) μ0 𝓕0 μX 𝓕X μU 𝓕U μH 𝓕H φ
          (xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (h, 1) f)) (rTr S h G)) ∧
      Integrable (fun h => (β h : ℂ) *
        bSharp ψ S T0 CS CS' S0 BS A lev ιH om00 (yMat T0 d.ρ ε z0) μ0 𝓕0 μX 𝓕X μU 𝓕U μH 𝓕H φ
          (xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (h, 1) f)) (rTr S h G)) ν ∧
      IntegrableOn (fun h0 => φ h0 * ∫ n in 𝓕N, star (besChar ψ d (n : GA D T)) * rInt S S0 CS lev μX 𝓕X μ0 𝓕0 ν β (fun h' =>
        xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (h', (n : GA D T) * s h0) f) 0 *
          G h') ∂μN) 𝓕H μH ∧
      ∫ h0 in 𝓕H, φ h0 * ∫ n in 𝓕N, star (besChar ψ d (n : GA D T)) * rInt S S0 CS lev μX 𝓕X μ0 𝓕0 ν β (fun h' =>
        xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (h', (n : GA D T) * s h0) f) 0 *
          G h') ∂μN ∂μH =
        cutInt S ν β (fun h =>
          bSharp ψ S T0 CS CS' S0 BS A lev ιH om00 (yMat T0 d.ρ ε z0) μ0 𝓕0 μX 𝓕X μU 𝓕U μH 𝓕H φ
          (xiEv ψ S T d.e C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S (yMat T0 d.ρ ε z0) (om (h, 1) f)) (rTr S h G))

end Formalism.IndefR.Mi

end
