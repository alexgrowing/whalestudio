import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsEnum {n : ℕ} (S : SPar) (lam : Fin n → ℝ) (ε : Fin n → Bool) : Prop :=
  StrictAnti lam ∧ ∃ q : Fin n → ℚ, (∀ a, lam a = (q a : ℝ)) ∧ S = Finset.univ.image fun a => (q a, ε a)

def GoodPar (n p q : ℕ) (S : SPar) : Prop :=
  ∃ (lam : Fin n → ℝ) (ε : Fin n → Bool), IsEnum S lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
    (Finset.univ.filter fun a => ε a = true).card = p ∧ (Finset.univ.filter fun a => ε a = false).card = q

def isoDef {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (J : Matrix (Fin n) (Fin n) ℂ)
    (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ M) (S : SPar) : Submodule ℂ M :=
  sSup {W | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (P : Matrix (Fin n) (Fin n) ℂ) (T : H →ₗ[ℂ] M),
    IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = J ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ v, T (σ (P * g * P⁻¹) v) = π g (T v)) ∧ W = LinearMap.range T}

def IsDsig (D : D7) (τ : D.what₂.Tau) (d : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ ∧
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d

def DsigHC (D : D7) : Prop := ∀ τ, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

def IsVolMeasG (D : D7) (W : HSp D) (P Q : D.what₂.Tau → ℕ) (μ : Measure (GA D W)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (IsInfFam (D := D)) fun θ =>
  AllSome (fun A : ∀ ρ : D.what₂.Tau, Matrix (Fin (P ρ) ⊕ Fin (Q ρ)) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (P ρ) (Q ρ) * A ρ = gramAt D W ρ) fun A =>
  ∀ B : ∀ ρ : D.what₂.Tau, Set (UpqT (P ρ) (Q ρ)), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D W) ↔
          (finMat D.sp.cm.sig W.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D W)) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig W.gram (θ ρ) h} =
      ∏ ρ, D.cd.cd (P ρ) (Q ρ) (B ρ)

def IsVolPair (D : D7) (W : HSp D) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) : Prop :=
  IsVolMeasG D W (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2) μ ∧
    IsFundamentalDomain (GQ W) 𝓕 μ

def VolTieG (D : D7) : Prop :=
  ∀ W : HSp D, W.SigOK →
    AllSome (IsVolMeasG D W (fun ρ => (W.sig (tauE D ρ)).1) (fun ρ => (W.sig (tauE D ρ)).2)) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (GQ W) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal (D.vol W)

open Classical in

def rhoOfIndex {p q : ℕ} (a : Ix p q) : ℚ :=
  ((Finset.univ.filter fun b => posC a b).card : ℚ) - ((Finset.univ.filter fun b => posC b a).card : ℚ)

def vogan {p q : ℕ} (μ : Ix p q → ℚ) : ℚ := ∑ a, (μ a + rhoOfIndex a) ^ 2

def HasParam {p q : ℕ} {T : GrpData p q} (R : DSRep T) (lam : Ix p q → ℚ) : Prop :=
  (∃ v, IsHW R.HK.act (blattner lam) v) ∧ ∀ μ v, IsHW R.HK.act μ v → vogan (blattner lam) ≤ vogan μ

abbrev AE (D : D7) : Type := AF D.host.F ⊗[D.host.F] D.host.E

def infPart (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finPart (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def IsHeckeChar (D : D7) (χ : (AE D)ˣ →* Circle) : Prop :=
  Continuous χ ∧ ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1

def HasInfExp (D : D7) (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a : ℚ) : Prop :=
  ∃ n : ℤ, (n : ℚ) = 2 * a ∧
    AllSome (IsInfFam (D := D)) fun θ =>
      ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
        ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n

def idF (D : D7) : (AF D.host.F)ˣ →* (AE D)ˣ :=
  Units.map (algebraMap (AF D.host.F) (AE D)).toMonoidHom

def IsEta (D : D7) (η : (AF D.host.F)ˣ →* Circle) : Prop :=
  Continuous η ∧ (∀ a : D.host.Fˣ, η (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom a) = 1) ∧
    (∀ x : (AE D)ˣ, η (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) = 1) ∧ η ≠ 1

def ResEta (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) : Prop :=
  AllSome (IsEta D) fun η => ∀ a, χ (idF D a) = η a ^ n

def intAE (D : D7) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def UnramEverywhere (D : D7) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsIsoSub {D : D7} (V : HSp D) {i : ℕ} (C : Matrix (Fin V.rank) (Fin i) D.host.E) : Prop :=
  LinearIndependent D.host.E C.transpose ∧ Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * C = 0

def IsWittLower {D : D7} (V V' : HSp D) (i : ℕ) : Prop :=
  V'.rank + 2 * i = V.rank ∧ ∃ ι : V'.V →ₗ[D.host.E] V.V, HSpace.IsIsomEmb V' V ι ∧
    ∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C ∧
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram * C = 0

end Formalism.L2.Theta

end
