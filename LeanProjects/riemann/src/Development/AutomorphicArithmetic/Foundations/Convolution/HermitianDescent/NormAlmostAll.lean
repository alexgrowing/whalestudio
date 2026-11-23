import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm

noncomputable section

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.D

def GalField : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → IsGal σ (Module.finrank F E)

def GalExt : Prop :=
  ∀ (F E k : Type) [Field F] [Field E] [Algebra F E] [CommRing k] [Algebra F k] (σ : E ≃ₐ[F] E) (q : ℕ),
    IsGal σ q → IsGal (ext k σ) q

def GalBase : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (A : Type) [CommRing A] [Algebra k A] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q →
    Module.Finite k R ∧ Module.Projective k R ∧ Module.FaithfullyFlat k R ∧
    IsGal (Algebra.TensorProduct.congr AlgEquiv.refl σ : A ⊗[k] R ≃ₐ[A] A ⊗[k] R) q

def Descent : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q →
    ∀ (M : Type) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] (s : M →ₗ[k] M),
    (∀ (r : R) m, s (r • m) = σ r • s m) → s ^ q = 1 →
    Function.Bijective (TensorProduct.lift ((Algebra.lsmul k k M (A := R)).toLinearMap.compl₂ (LinearMap.eqLocus s LinearMap.id).subtype))

def H90 : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (S T : Type) [CommRing S] [CommRing T] [Algebra k S] [Module.Finite k S] [Algebra S T]
    (σ : T ≃ₐ[S] T) (q : ℕ), IsGal σ q → ∀ a : Tˣ, ∏ i ∈ Finset.range q, (σ ^ i) a = 1 → ∃ z : Tˣ, (a : T) * σ z = z

def ConjSep : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] [Module.Finite k R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R), g.charpoly.Separable →
    (∀ g' : Matrix (Fin n) (Fin n) R, g'.charpoly = g.charpoly → ∃ x : GL (Fin n) R, g * x.val = x.val * g') ∧
    (∀ y, y * g = g * y → ∃ p : R[X], y = aeval g p) ∧ ∀ p : R[X], aeval g p = 0 ↔ g.charpoly ∣ p

def NmPoly : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q → ∀ (n : ℕ) (δ : GL (Fin n) R),
    (∃ p : k[X], p.Monic ∧ cp (nm σ q δ) = p.map (algebraMap k R)) ∧ ∀ x, nm σ q (sgConj σ x δ) = x⁻¹ * nm σ q δ * x

def NmRep : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q → ∀ (n : ℕ) (δ : GL (Fin n) R) (γ : GL (Fin n) k),
    (cp γ).Separable → cp (nm σ q δ) = (cp γ).map (algebraMap k R) →
    ∃ x, nm σ q (sgConj σ x δ) = up R γ ∧ Commute (sgConj σ x δ) (up R γ)

def NmInj : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q → ∀ (n : ℕ) (δ δ' : GL (Fin n) R),
    (cp (nm σ q δ)).Separable → cp (nm σ q δ') = cp (nm σ q δ) → ∃ x, δ' = sgConj σ x δ

def NmCent : Prop :=
  ∀ (k R : Type) [CommRing k] [IsLocalRing k] [CommRing R] [Algebra k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q → ∀ (n : ℕ) (a : GL (Fin n) R) (γ : GL (Fin n) k),
    (cp γ).Separable → nm σ q a = up R γ → ∀ x, sgConj σ x a = a ↔ ∃ t : GL (Fin n) k, Commute t γ ∧ x = up R t

def HasseEt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] (A : Type) [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A] (x : Aˣ),
    (∀ v : HeightOneSpectrum (𝓞 F), IsNm F E ((1 : v.adicCompletion F) ⊗ₜ[F] (x : A))) →
    (∀ v : InfinitePlace F, IsNm F E ((1 : v.Completion) ⊗ₜ[F] (x : A))) → IsNm F E (x : A)

def NmHasse : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (γ : GL (Fin n) F), (cp γ).Separable →
    (∀ v : HeightOneSpectrum (𝓞 F), ∃ δ, cp (nm (ext (v.adicCompletion F) σ) (Module.finrank F E) (n := n) δ) =
      (cp γ).map ((inc (v.adicCompletion F)).comp (algebraMap F E))) →
    (∀ v : InfinitePlace F, ∃ δ, cp (nm (ext v.Completion σ) (Module.finrank F E) (n := n) δ) =
      (cp γ).map ((inc v.Completion).comp (algebraMap F E))) →
    ∃ a : GL (Fin n) E, nm σ (Module.finrank F E) a = up E γ ∧ Commute a (up E γ)

def NormAlmostAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (A : Type) [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A] (a : Aˣ),
    {v : HeightOneSpectrum (𝓞 F) | ¬ IsNm F E ((1 : v.adicCompletion F) ⊗ₜ[F] (a : A))}.Finite

def NmInt : Prop :=
  ∀ (O S k R : Type) [CommRing O] [IsLocalRing O] [CommRing S] [Algebra O S] [Field k] [CommRing R] [Algebra k R]
    (i : O →+* k) (j : S →+* R) (s : S ≃ₐ[O] S) (σ : R ≃ₐ[k] R) (q : ℕ), IsGal s q → IsGal σ q → Function.Injective j →
    (∀ x, j (s x) = σ (j x)) → (∀ x, j (algebraMap O S x) = algebraMap k R (i x)) →
    ∀ (n : ℕ) (a a' : GL (Fin n) S) (γ : GL (Fin n) O), (cp γ).Separable → nm s q a = up S γ →
    ∀ x : GL (Fin n) R, sgConj σ x (Matrix.GeneralLinearGroup.map j a) = Matrix.GeneralLinearGroup.map j a' →
    ∃ (t : GL (Fin n) k) (u : GL (Fin n) S), Commute t (Matrix.GeneralLinearGroup.map i γ) ∧
      x = up R t * Matrix.GeneralLinearGroup.map j u

def NmAlg : Prop :=
  ∀ (F E k : Type) [Field F] [Field E] [Algebra F E] [Field k] [Algebra F k] (σ : E ≃ₐ[F] E) (q : ℕ), IsGal σ q →
    ∀ (n : ℕ) (γ : GL (Fin n) F), (cp γ).Separable →
    ((∃ δ : GL (Fin n) (k ⊗[F] E), cp (nm (ext k σ) q δ) = (cp γ).map ((inc k).comp (algebraMap F E))) ↔
      IsNm F E ((1 : k) ⊗ₜ[F] AdjoinRoot.root (cp γ))) ∧
    ((∃ a : GL (Fin n) E, nm σ q a = up E γ ∧ Commute a (up E γ)) ↔ IsNm F E (AdjoinRoot.root (cp γ)))

def NormProd : Prop :=
  ∀ (k R : Type) [CommRing k] [CommRing R] [Algebra k R] [Module.Free k R] (σ : R ≃ₐ[k] R) (q : ℕ), IsGal σ q → ∀ r : R,
    algebraMap k R (Algebra.norm k r) = ∏ i ∈ Finset.range q, (σ ^ i) r

end UpperTheory.ConvolutionTheory.D
