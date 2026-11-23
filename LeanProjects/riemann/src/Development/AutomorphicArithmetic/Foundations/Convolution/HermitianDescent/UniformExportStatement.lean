import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

def CsrOf : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R), c ^ 2 = 1 → ∀ n : ℕ,
    (∀ (J : Matrix (Fin n) (Fin n) R) (γ : GL (Fin n) R), IsUnit J.det → cong c γ J = J → IsCsr c n (cp γ)) ∧
    ∀ d : GL (Fin n) R, IsCsr c n (cp (d * th c d))

def ModelEx : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R), IsGal c 2 → ∀ (n : ℕ) (P : R[X]), IsCsr c n P → P.Separable →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (b : Module.Basis (Fin n) k A) (g : (R ⊗[k] A)ˣ), IsReg c b g ∧ cp (matU b g) = P

def GramBasic : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 →
    (∀ s z, ct c (mat b z) * gramL b s = gramL b (io c A z * s) ∧ gramL b s * mat b z = gramL b (s * z) ∧
      ct c (gramL b s) = gramL b (io c A s) ∧ (gramL b s).det = Algebra.norm R s * (gram R b 1).det) ∧
    (∀ x : A, gram R b x = (Matrix.of fun i j => Algebra.trace k A (x * (b i * b j))).map (algebraMap k R) ∧
      (gram R b x).det = algebraMap k R (Algebra.norm k x) * (gram R b 1).det) ∧
    ∀ g, IsReg c b g → IsUnit (gram R b (1 : A)).det ∧ Function.Injective (gramL (R := R) b) ∧
      ∀ y : Matrix (Fin n) (Fin n) R, y * mat b g = mat b g * y → ∃ z, y = mat b z

def UClass : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g →
    ∀ (J : Matrix (Fin n) (Fin n) R) (γ : GL (Fin n) R), IsHerm c J → cong c γ J = J → cp γ = cp (matU b g) →
    ∃ (x : Aˣ) (y : GL (Fin n) R), cong c y J = gram R b (x : A) ∧ y⁻¹ * γ * y = matU b g

def UIso : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∀ x x' : Aˣ,
    (IsHerm c (gram R b (x : A)) ∧ cong c (matU b g) (gram R b (x : A)) = gram R b (x : A)) ∧
    (∀ y : GL (Fin n) R, (cong c y (gram R b (x : A)) = gram R b (x' : A) ∧ Commute y (matU b g)) ↔
      ∃ z : (R ⊗[k] A)ˣ, y = matU b z ∧ (1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A) = z * io c A z)

def TBase : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∃ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val

def TClass : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∀ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val →
    ∀ d : GL (Fin n) R, cp (d * th c d) = cp (matU b g) →
    ∃ (x : Aˣ) (y : GL (Fin n) R), ((thConj c y d)⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)

def TIso : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (n : ℕ) (b : Module.Basis (Fin n) k A) (c : R ≃ₐ[k] R), IsGal c 2 → ∀ g, IsReg c b g → ∀ w : (R ⊗[k] A)ˣ, io c A w.val = g.val * w.val →
    (∀ x : Aˣ, ∃ d : GL (Fin n) R, (d⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val)) ∧
    ∀ (x x' : Aˣ) (d d' : GL (Fin n) R), (d⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x : A)) * w.val) →
      (d'⁻¹ : GL (Fin n) R).val = gramL b (((1 : R) ⊗ₜ[k] (x' : A)) * w.val) → d * th c d = matU b g ∧
      ∀ y, d' = thConj c y d ↔ ∃ z : (R ⊗[k] A)ˣ, y = matU b z ∧ (1 : R) ⊗ₜ[k] ((x' / x : Aˣ) : A) = z * io c A z

def ModelExt : Prop :=
  ∀ (F E A k : Type) [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing k] [Algebra F k] (n : ℕ)
    (b : Module.Basis (Fin n) F A) (c : E ≃ₐ[F] E),
    (∀ z : E ⊗[F] A, mat (Algebra.TensorProduct.basis k b) (incL k A z) = (mat b z).map (inc k) ∧
      gramL (Algebra.TensorProduct.basis k b) (incL k A z) = (gramL b z).map (inc k) ∧
      io (ext k c) (k ⊗[F] A) (incL k A z) = incL k A (io c A z)) ∧
    ∀ g, IsReg c b g → IsReg (ext k c) (Algebra.TensorProduct.basis k b) (Units.map (incL (F := F) (E := E) k A).toRingHom.toMonoidHom g)

def NormBridge : Prop :=
  ∀ (F E k A : Type) [Field F] [Field E] [Algebra F E] [CommRing k] [Algebra F k] [CommRing A] [Algebra F A] [Algebra k A]
    [IsScalarTower F k A] (c : E ≃ₐ[F] E), IsGal c 2 → ∀ x : Aˣ,
    (NormIn (ext k c) x ↔ IsNm F E (x : A)) ∧ (NormIn c x ↔ IsNm F E (x : A))

def SgnLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (K : Type) [Field K] [Algebra F K] [Algebra (v.adicCompletion F) K]
      [IsScalarTower F (v.adicCompletion F) K] [FiniteDimensional (v.adicCompletion F) K] (x y : Kˣ),
      sgn F E ((x * y : Kˣ) : K) = sgn F E (x : K) * sgn F E (y : K) ∧
        sgn F E (x : K) = sgn F E (Algebra.norm (v.adicCompletion F) (x : K))) ∧
    ∀ (v : InfinitePlace F) (K : Type) [Field K] [Algebra F K] [Algebra v.Completion K] [IsScalarTower F v.Completion K]
      [FiniteDimensional v.Completion K] (x y : Kˣ),
      sgn F E ((x * y : Kˣ) : K) = sgn F E (x : K) * sgn F E (y : K) ∧ sgn F E (x : K) = sgn F E (Algebra.norm v.Completion (x : K))

def SgnUnram : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (x : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))ˣ),
      (sgn (maximalRealSubfield E) E x.val = 1 ↔ GlobalTheory.UnitaryBC.IsSplitAt w ∨ Even (WithZero.log (Valued.v x.val)))) ∧
    ∀ (v : InfinitePlace (maximalRealSubfield E)) (hv : v.IsReal) (x : v.Completionˣ),
      (sgn (maximalRealSubfield E) E x.val = 1 ↔ 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv x.val)

def Recip : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (A : Type) [CommRing A] [Algebra F A] (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, Field (K i)]
    [∀ i, NumberField (K i)] [∀ i, Algebra F (K i)] (e : A ≃ₐ[F] ∀ i, K i)
    (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F ⊗[F] A)ˣ) (x' : ∀ v : InfinitePlace F, (v.Completion ⊗[F] A)ˣ),
    {v | ¬ IsNm F E (x v).val}.Finite →
    ((∃ a : Aˣ, (∀ v, IsNm F E ((x v).val * (1 ⊗ₜ (a⁻¹ : Aˣ).val))) ∧ ∀ v, IsNm F E ((x' v).val * (1 ⊗ₜ (a⁻¹ : Aˣ).val))) ↔
      ∀ i, (∏ᶠ v, sgn F E (Algebra.norm (v.adicCompletion F)
          (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) _) ((Pi.evalAlgHom F K i).comp e.toAlgHom) (x v).val))) *
        ∏ v, sgn F E (Algebra.norm v.Completion
          (Algebra.TensorProduct.map (AlgHom.id v.Completion _) ((Pi.evalAlgHom F K i).comp e.toAlgHom) (x' v).val)) = 1)

def HermLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), IsGal c 2 → ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (J J' : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)), IsHerm (ext _ c) J → IsHerm (ext _ c) J' →
    ((∃ y, cong (ext _ c) y J = J') ↔ ∃ z : (v.adicCompletion F ⊗[F] E)ˣ, J'.det = J.det * (z.val * ext (v.adicCompletion F) c z.val))

def HermHasse : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E) J → IsHerm (IsCMField.complexConj E) J' →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ y,
      cong (ext (v.adicCompletion (maximalRealSubfield E)) (IsCMField.complexConj E)) y (J.map (inc _)) = J'.map (inc _)) →
    (∀ v : InfinitePlace (maximalRealSubfield E), ∃ y,
      cong (ext v.Completion (IsCMField.complexConj E)) y (J.map (inc _)) = J'.map (inc _)) →
    ∃ y, cong (IsCMField.complexConj E) y J = J'

def RealPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace (maximalRealSubfield E)) (A : Type) [CommRing A] [Algebra v.Completion A] (n : ℕ)
    (b : Module.Basis (Fin n) v.Completion A) (x₀ : Aˣ),
    (∃ y, cong (ext v.Completion (IsCMField.complexConj E)) y (gram _ b (x₀ : A)) = 1) →
    Nonempty (A ≃ₐ[v.Completion] (Fin n → v.Completion)) ∧ ∀ x : Aˣ,
      (∃ y, cong (ext v.Completion (IsCMField.complexConj E)) y (gram _ b (x : A)) = 1) ↔ NormIn (ext v.Completion (IsCMField.complexConj E)) x

def Factors : Prop :=
  ∀ (F A : Type) [Field F] [NumberField F] [CommRing A] [Algebra F A] (n : ℕ) (b : Module.Basis (Fin n) F A),
    IsUnit (Matrix.of fun i j => Algebra.trace F A (b i * b j)).det →
    ∃ (m : ℕ) (K : Fin m → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Algebra F (K i)),
      Nonempty (A ≃ₐ[F] ∀ i, K i) ∧ (IsTotallyReal F →
        (∀ v : InfinitePlace F, Nonempty (v.Completion ⊗[F] A ≃ₐ[v.Completion] (Fin n → v.Completion))) → ∀ i, IsTotallyReal (K i))

end UpperTheory.ConvolutionTheory.D
