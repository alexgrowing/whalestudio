import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import GroundTheory.GlobalFields.Adele.BaseChange
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
import GroundTheory.AutomorphicForms.AffineBruhat
import GroundTheory.AutomorphicForms.Cartan

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NumberField.AdeleRing TensorProduct

namespace PositivityTheory.Rg.Tf.Geo

section Quot
variable {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]

def IsNormAlong (u : X → G) (j : T → G) (ν : Measure T) (ρ : G → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ x, ∫⁻ t, ρ (j t * u x) ∂ν = 1

open Classical in

def quotInt (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (Φ : X → ℂ) : ℂ :=
  if h : ∃ ρ, IsNormAlong u j ν ρ then ∫ x, Φ x * ((h.choose (u x)).toReal : ℂ) ∂μ else 0
end Quot

section Match
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
  [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)]

abbrev mapGL {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (f : R →+* S) : GL (Fin n) R →* GL (Fin n) S :=
  Matrix.GeneralLinearGroup.map f

def orb (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ}))
    (f : GL (Fin n) R → ℂ) : ℂ :=
  quotInt μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν fun x => f (x⁻¹ * γ * x)

def twOrb (ι : R →+* S) (s : S →+* S) (μ : Measure (GL (Fin n) S)) (γ : GL (Fin n) R)
    (ν : Measure (Subgroup.centralizer {γ})) (δ : GL (Fin n) S) (φ : GL (Fin n) S → ℂ) : ℂ :=
  quotInt μ id (fun t : Subgroup.centralizer {γ} => mapGL n ι (t : GL (Fin n) R)) ν fun x => φ (x⁻¹ * δ * mapGL n s x)

def Match (ι : R →+* S) (s : S →+* S) (l : ℕ) (μS : Measure (GL (Fin n) S)) (μR : Measure (GL (Fin n) R)) (c : ℂ)
    (φ : GL (Fin n) S → ℂ) (f : GL (Fin n) R → ℂ) : Prop :=
  ∀ γ : GL (Fin n) R, (γ : Matrix (Fin n) (Fin n) R).charpoly.Separable →
    ∀ ν : Measure (Subgroup.centralizer {γ}), ν.IsHaarMeasure →
      (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ → twOrb ι s μS γ ν δ φ = c * orb μR γ ν f) ∧
      ((¬ ∃ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ) → orb μR γ ν f = 0)
end Match

section Galois
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def galOf {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) :
    B →+* B :=
  (e : E ⊗[F] A →+* B).comp (((Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) : E ⊗[F] A →ₐ[F] E ⊗[F] A) :
    E ⊗[F] A →+* E ⊗[F] A).comp (e.symm : B →+* E ⊗[F] A))

def galAd (σ : E ≃ₐ[F] E) : 𝔸[E] →+* 𝔸[E] := galOf (adeleTensorEquiv F E) σ

def galFin (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : CompletionsOver E v →+* CompletionsOver E v :=
  galOf (tensorEquiv' E v) σ

def galInf (σ : E ≃ₐ[F] E) : InfiniteAdeleRing E →+* InfiniteAdeleRing E :=
  galOf (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ

variable (E) in

def incFin (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →+* CompletionsOver E v :=
  RingHom.pi fun w => completionMap v w.1

def atFin (v : HeightOneSpectrum (𝓞 F)) : 𝔸[E] →+* CompletionsOver E v where
  toFun a w := a.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {n : ℕ}

variable (E n) in

def unitSet (v : HeightOneSpectrum (𝓞 F)) : Set (GL (Fin n) (CompletionsOver E v)) :=
  {g | ∀ w : PlacesOver E v, mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g ∈
    GLnLocal.integralGL (w.1.adicCompletion E) n}

def IsGalTwist (σ : E ≃ₐ[F] E) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] (θ : Twist μ) : Prop :=
  ∀ g : G1 E n, ((θ.e g : G1 E n) : AdelicGLn.AdelicGL E n) = mapGL n (galAd σ) (g : AdelicGLn.AdelicGL E n)

def EllElt (σ : E ≃ₐ[F] E) (δ : GL (Fin n) E) : Prop :=
  ∃ p : F[X], Irreducible p ∧ p.map (algebraMap F E) = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly

def Ell (σ : E ≃ₐ[F] E) (f : G1 E n → ℂ) : Prop :=
  ∀ (δ : GL (Fin n) E) (x y : G1 E n), (y : AdelicGLn.AdelicGL E n) =
    (x : AdelicGLn.AdelicGL E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : AdelicGLn.AdelicGL E n) →
    f y ≠ 0 → EllElt σ δ

open Classical in

def ext0 (f : G1 E n → ℂ) (g : AdelicGLn.AdelicGL E n) : ℂ := if h : g ∈ normOneGL E n then f ⟨g, h⟩ else 0

def GMatch (σ : E ≃ₐ[F] E) (μE : Measure (G1 E n)) (μF : Measure (G1 F n)) (c : ℂ) (fE : G1 E n → ℂ) (fF : G1 F n → ℂ) : Prop :=
  ∀ (γ : GL (Fin n) F) (γ₁ : G1 F n), (γ₁ : AdelicGLn.AdelicGL F n) = AdelicGLn.diagonal F n γ →
    Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly →
    ∀ ν : Measure (Subgroup.centralizer {γ₁}), ν.IsHaarMeasure →
      (∀ δ : GL (Fin n) E, normGL σ δ = incl γ →
        quotInt μE (fun x : G1 E n => (x : AdelicGLn.AdelicGL E n))
          (fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : AdelicGLn.AdelicGL F n)) ν
          (fun x => ext0 fE ((x : AdelicGLn.AdelicGL E n)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (x : AdelicGLn.AdelicGL E n))) =
        c * quotInt μF id (fun t : Subgroup.centralizer {γ₁} => (t : G1 F n)) ν fun x => fF (x⁻¹ * γ₁ * x)) ∧
      ((¬ ∃ δ : GL (Fin n) E, normGL σ δ = incl γ) →
        quotInt μF id (fun t : Subgroup.centralizer {γ₁} => (t : G1 F n)) ν (fun x => fF (x⁻¹ * γ₁ * x)) = 0)

def tensE (φi : GL (Fin n) (InfiniteAdeleRing E) → ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (CompletionsOver E v) → ℂ) (g : AdelicGLn.AdelicGL E n) : ℂ :=
  φi (mapGL n (RingHom.fst _ _) g) * ∏ᶠ v, φ v (mapGL n (atFin v) g)

def tensF (fi : GL (Fin n) (InfiniteAdeleRing F) → ℂ)
    (f : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F) → ℂ) (g : AdelicGLn.AdelicGL F n) : ℂ :=
  fi (mapGL n (RingHom.fst _ _) g) * ∏ᶠ v, f v (finAt v g)

def avg (Φ : AdelicGLn.AdelicGL E n → ℂ) (g : G1 E n) : ℂ :=
  ∫ t : ℝ, Φ (centralSection E n ⟨Real.exp t, Real.exp_pos t⟩ * (g : AdelicGLn.AdelicGL E n))

def heightOff (q : HeightOneSpectrum (𝓞 F)) (g : AdelicGLn.AdelicGL E n) : ℝ :=
  (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult) *
    ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q), AutomorphicForm.locHeight (finAt w g)

end Galois

end PositivityTheory.Rg.Tf.Geo
