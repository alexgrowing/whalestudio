import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTChart (A K : Type) [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (p R N : ℕ)
    (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] where

  om : Submodule A Ω
  om_lat : om.IsLattice K
  om_proj : Module.Projective A om

  ρΩ : 𝓞 E →+* Module.End K Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)
  alt : ∀ x, e x x = 0
  adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)
  e_surj : ∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ
  e_inj : ∀ x, e x = 0 → ∃ x', x = (p ^ R) • x'

  h : (Fin N → 𝓞 E) →+ Ω
  h_mem : ∀ x, h x ∈ om
  h_lin : ∀ (a : 𝓞 E) (x : Fin N → 𝓞 E), ∃ y ∈ om, h (a • x) = ρΩ a (h x) + (p ^ R) • y

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

def om' : Submodule A Ω :=
  Submodule.span A (Set.range D.h) ⊔ D.om.map (((p : A) ^ R) • LinearMap.id)

def omHT (σ : E →+* K) : Submodule A Ω := eigQuot D.ρΩ σ D.om'

def q (σ : E →+* K) (x : Fin N → A) : Ω := ∑ i, x i • eigProj D.ρΩ σ (D.h (Pi.single i 1))

def gram (σ : E →+* K) (d : A) (i j : Fin N) : K :=
  ∑ k, algebraMap A K d * σ (dualInt E k) *
    ((D.e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : K)

def IsDualMap (σ : E →+* K) (d : A) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  ∀ (w : Module.Dual A (D.omHT (σ.comp c.toRingHom))) (j : Fin N)
    (y : D.omHT (σ.comp c.toRingHom)),
    (y : Ω) = eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)) →
      ∃ z : A, ∑ l, algebraMap A K (i w l) * D.gram σ d l j = algebraMap A K (w y + (p : A) ^ m * z)

def ExactMod (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) : Prop :=
  (∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)),
    ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w') ∧
  (∀ x : Fin N → A, (∃ y ∈ D.omHT σ, D.q σ x = ((p : A) ^ m) • y) ↔
    ∃ w, ∃ x' : Fin N → A, x = i w + ((p : A) ^ m) • x') ∧
  ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y'

structure ReducesTo {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ N V Ω') (ι : D.om →ₛₗ[φ] Ω') : Prop where
  span_eq : Submodule.span O (Set.range ι) = P.om
  rank_eq : Module.finrank K Ω = Module.finrank C Ω'
  lin : ∀ (a : 𝓞 E) (x : D.om), ι ⟨D.ρΩ a x, D.om_stable a x x.2⟩ = P.ρΩ a (ι x)
  ht_eq : ∀ x, ∃ y ∈ P.om, ι ⟨D.h x, D.h_mem x⟩ = P.ht (P.tate x) + (p ^ R) • y
  e_eq : ∀ x y, ∃ z : O, P.e (P.tate x) (P.tate y) =
    algebraMap O C (((D.e x y).val : O) + (p : O) ^ R * z)

def HasTestPoints (κ : A) : Prop :=
  ∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 →
    ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : Algebra O C)
      (v : Valuation C NNReal) (φ : A →+* O)
      (V Ω' : Type) (_ : AddCommGroup V) (_ : Module C V) (_ : Module O V) (_ : IsScalarTower O C V)
      (_ : AddCommGroup Ω') (_ : Module C Ω') (_ : Module O Ω') (_ : IsScalarTower O C Ω')
      (P : HTPoint C O c (φ κ) N V Ω') (ι : D.om →ₛₗ[φ] Ω'),
      v.Integers O ∧ Function.Injective φ ∧ (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1) ∧
        D.ReducesTo φ P ι

end HTChart

def GeneratesDiff {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E]
    [NumberField E] (σ : E →+* K) (d : A) : Prop :=
  Submodule.span A {algebraMap A K d} =
    Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}

end GlobalTheory.CompanionTheory.Ar.HT
