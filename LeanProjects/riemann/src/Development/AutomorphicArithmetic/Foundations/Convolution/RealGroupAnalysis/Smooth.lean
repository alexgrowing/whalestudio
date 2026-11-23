import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.St

section Base

variable (F : Type) [Field F] [NumberField F]

def Gen : Prop :=
  Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) = ⊤ ∧
    Subgroup.closure (Set.range (fun b : F => nU (rt b)) ∪ {wW F}) = Gam F

def MeasEx : Prop := Nonempty (Meas F)

def Red : Prop := ∃ c : ℝ, 0 < c ∧ ∀ g : G1 F, ∃ γ b a, ∃ k ∈ KK F, ratS F γ * g = nU b * mD a * k ∧ c ≤ ab a

def Inv : Prop :=
  ∀ (M : Meas F) (u : G1 F → ℂ), Measurable u → (∀ b g, u (nU b * g) = u g) → Integrable (iw u) M.ν →
    (∀ g₀, Integrable (iw fun g => u (g * g₀)) M.ν ∧ (M.I0 fun g => u (g * g₀)) = M.I0 u) ∧
    ∀ t, Integrable (iw fun g => u (cD t g)) M.ν ∧ (M.I0 fun g => u (cD t g)) = (((ab t)⁻¹ : ℝ) : ℂ) * M.I0 u

variable [IsTotallyReal F]

def Cen : Prop :=
  ∀ π : TR.CuspSub F 2, ∃ ω : (A F)ˣ →* ℂˣ, Continuous ω ∧ ∀ f ∈ π.V, ∀ s g,
    f.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) = ((ω s : ℂˣ) : ℂ) * f.1 g

def Decay : Prop :=
  ∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, Continuous f.1 ∧ ∀ C : Set (GL (Fin 2) (A F)), IsCompact C → ∀ c : ℝ, 0 < c → ∀ r : ℕ,
    ∃ B : ℝ, ∀ b a, ∀ k ∈ C, c ≤ ab a → ‖f.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ^ r

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

variable (F E) in

def DatEx : Prop := Module.finrank F E = 2 → Nonempty (Dat F E)

def WeilEx (D : Dat F E) : Prop := Nonempty (Weil D)

variable {D : Dat F E} (W : Weil D) (M : Meas F)

structure Hat : Prop where
  n : ∀ b φ v, hat (W.Om (nU b) φ).1 v = ψ (b * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) * hat φ.1 (Function.update v 1 (v 1 + b * v 0))
  m : ∀ (a : (A F)ˣ) φ v, hat (W.Om (mD a) φ).1 v = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
    hat φ.1 ![a * v 0, ((a⁻¹ : (A F)ˣ) : A F) * v 1, a * v 2, a * v 3]
  w : ∀ φ v, hat (W.Om (wW F) φ).1 v =
    ∫ z : Fin 2 → A F, hat φ.1 ![-v 1, v 0, z 0, z 1] * ψ (2 * (z 0 * v 2 - rt D.δ * (z 1 * v 3))) ∂(adeleMeasurePi F)
  nE : ∀ u t φ x z₀ z₁, hat (W.L (gl (nU (D.mkE u t))) φ).1 ![0, x, z₀, z₁] =
    ψ (-(x * (2 * (u * z₀ - rt D.δ * (t * z₁))))) * hat φ.1 ![0, x, z₀, z₁]
  aE : ∀ (α : (A E)ˣ) φ y x z₀ z₁, hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] =
    hat φ.1 ![y, (ideleNorm F E α : (A F)ˣ) * x, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
      D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1]
  mem : ∀ φ : S4 F, hat φ.1 ∈ schwartzBruhatPi F (Fin 4)
  th : ∀ φ : S4 F, Th φ.1 = Th (hat φ.1)
  row : ∀ γ (r : Fin 2 → F) φ, ThRow (rt (r 0)) (rt (r 1)) (W.Om (ratS F γ) φ).1 =
    ThRow (rt ((r ᵥ* γ.1) 0)) (rt ((r ᵥ* γ.1) 1)) φ.1

structure FockSt : Prop where
  fin : ∀ k, ∀ φ ∈ Fock D.δ, W.L (finGL E 2 k) φ ∈ Fock D.δ
  cpt : ∀ φ ∈ Fock D.δ, ∃ U : Submodule ℂ (S4 F), U ≤ Fock D.δ ∧ FiniteDimensional ℂ U ∧
    ∀ k : Kinf E 2, W.L (infGL E 2 (Unitary.toUnits k)) φ ∈ U
  om : ∀ φ ∈ Fock D.δ, ∀ C : Set (G1 F), IsCompact C → (∀ k ∈ C, InfOrth k) →
    ∃ U : Submodule ℂ (S4 F), U ≤ Fock D.δ ∧ FiniteDimensional ℂ U ∧ ∀ k ∈ C, W.Om k φ ∈ U

variable (π : TR.CuspSub F 2)

def Conv : Prop :=
  ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h,
    IntegrableOn (fun g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1) M.D M.μ ∧
    IntegrableOn (fun g => f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1) M.D M.μ ∧
    Measurable (w1 W f.1 φ h) ∧ (∀ b g, w1 W f.1 φ h (nU b * g) = w1 W f.1 φ h g) ∧ Integrable (iw (w1 W f.1 φ h)) M.ν

def Equiv : Prop :=
  ∀ f ∈ π.V, ∀ φ : S4 F, (∀ γ h, lift W M f.1 φ (ratGL E 2 γ * h) = lift W M f.1 φ h) ∧
    ∀ ω : (A F)ˣ →* ℂˣ, (∀ s g, f.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) s * g) = ((ω s : ℂˣ) : ℂ) * f.1 g) →
      ∀ z h, lift W M f.1 φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((ω (ideleNorm F E z) : ℂˣ) : ℂ) * lift W M f.1 φ h

def Smooth : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∃ Φ : Sm E 2, Φ.1 = lift W M f.1 φ

def Stable : Prop := IsStable (span W M π)

def Cap : Prop :=
  ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m →
    ∀ u, ∀ Φ ∈ span W M π, cap τ u Φ = (m.map (u + ·)).prod • Φ

def Aut : Prop := π.IsRegAlg → ∀ Φ ∈ span W M π, IsAutForm Φ

def Exp : Prop := ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, WE D (lift W M f.1 φ) h = W1 W M f.1 φ h

def Cusp : Prop :=
  ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Φ ∈ span W M π, IsCuspidal Φ.1 ∧ ((∀ h, WE D Φ.1 h = 0) → Φ = 0)

def Ne : Prop := ∃ f ∈ π.V, ∃ φ ∈ Fock D.δ, ∃ h, W1 W M f.1 φ h ≠ 0

def Dih : Prop := π.IsRegAlg → ¬ ThetaLiftTrivialOrbitTermsVanish W M π → IsoTwist π W.η

def Irr : Prop := π.IsRegAlg → ThetaLiftTrivialOrbitTermsVanish W M π → span W M π ≠ ⊥ → ∃ P : CuspSub E 2, P.V ≤ span W M π

def Split : Prop :=
  ThetaLiftTrivialOrbitTermsVanish W M π → ∀ P : CuspSub E 2, P.V ≤ span W M π →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E),
    Continuous i → (∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def Unr : Prop :=
  ThetaLiftTrivialOrbitTermsVanish W M π → ∀ P : CuspSub E 2, P.V ≤ span W M π →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ v : HeightOneSpectrum (𝓞 F),
    v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → ∀ f : ℕ, normV w = normV v ^ f →
      ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

end UpperTheory.ConvolutionTheory.R2.St

end
