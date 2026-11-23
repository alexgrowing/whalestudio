import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues

noncomputable section

namespace GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.TensorOrderReduction

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
open scoped TensorProduct

def valSpec {A B : Type} [CommRing A] [CommRing B] (u : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (f : A) : B :=
  (Spec.preimage u).hom f

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def IsHomEmb (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∀ (B : Type) [CommRing B] (β : R →+* B) (y z : Over.mk (Spec.map (CommRingCat.ofHom β)) ⟶ Γ.G)
    (f : A) (m : ℕ) (a b : Fin m → A),
    (∀ s t : T, (f : T → R) (s * t) = ∑ k, (a k : T → R) s * (b k : T → R) t) →
      valSpec (B := B) ((y * z).left ≫ j) f =
        ∑ k, valSpec (B := B) (y.left ≫ j) (a k) * valSpec (B := B) (z.left ≫ j) (b k)

def InducesOnPts (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} (i : Γ.G.left ⟶ G.left) (a : G ⟶ G)
    (aT : T →* T) : Prop :=
  ∀ t, (Γ.pt (aT t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left

def IsRedTan (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
    (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ) (e : L)
    (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
      (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
    v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left

abbrev OmegaMod (R L : Type) [CommRing R] [AddCommGroup L] [Module R L] (N : ℕ) : Type :=
  Module.Dual R L ⧸ (Ideal.span {(N : R)} • (⊤ : Submodule R (Module.Dual R L)))

def IsOmegaIso (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
    (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)
    (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A))
    (θ : OmegaMod R L N ≃ₗ[R] omega A) : Prop :=
  (∀ (w : Module.Dual R L) (f : augIdeal A),
      θ (Submodule.Quotient.mk w) = (augIdeal A).toCotangent f ↔
        ∀ e : L, ∃ v, IsRedTan Γ i M N e v ∧
          valSpec (B := DualNumber (R ⧸ Ideal.span {(N : R)})) (v ≫ j) (f : A) =
            TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))) ∧
    ∀ (χ : T →* Rˣ) (w : Module.Dual R L),
      Γ.IsHT i M N χ w ↔ (fun t => ((χ t : Rˣ) : R)) ∈ A ∧ θ (Submodule.Quotient.mk w) = dlogChar A χ

def IsTensorOrder {R' : Type} [CommRing R'] [Algebra R R'] (A : Subalgebra R (T → R))
    (A' : Subalgebra R' (T → R')) : Prop :=
  ∃ ε : R' ⊗[R] A ≃ₐ[R'] A', ∀ (r : R') (f : A) (t : T),
    (ε (r ⊗ₜ[R] f) : T → R') t = r * algebraMap R R' ((f : T → R) t)

def Conclusion (Γ : QFGroup R T) {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S)
    (N : ℕ) (i : Γ.G.left ⟶ G.left) : Prop :=

  IsHopfOrder (Γ.btOrder ⊤) ∧
  (∃ j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)),

    Γ.IsEmb (Γ.btOrder ⊤) j ∧ IsOpenImmersion j ∧ IsHomEmb Γ (Γ.btOrder ⊤) j ∧
    Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ ∧

    (IsProper (pullback.snd G.hom x) → IsIso j) ∧

    ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L),
      ∃ θ : OmegaMod R L N ≃ₗ[R] omega (Γ.btOrder ⊤), IsOmegaIso Γ i M N (Γ.btOrder ⊤) j θ) ∧

  (IsUnit (N : R) → Γ.btOrder ⊤ = ⊤) ∧

  (∀ a : G ⟶ G, IsMonHom a → ∃ aT : T →* T, InducesOnPts Γ i a aT ∧
    ∀ f ∈ Γ.btOrder ⊤, (fun t => f (aT t)) ∈ Γ.btOrder ⊤) ∧

  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R'] [Algebra R R'] (Γ' : QFGroup R' T)
    (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F →
      IsTensorOrder (Γ.btOrder ⊤) (Γ'.btOrder ⊤)

def LemmaBT : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T]
    (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left),
      Γ.IsTorsionAlong G x N i → Conclusion Γ G x N i

theorem InducesOnPts.unique {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (hi : Γ.IsTorsionAlong G x N i)
    {a : G ⟶ G} {b c : T →* T} (hb : InducesOnPts Γ i a b) (hc : InducesOnPts Γ i a c) : b = c := by
  ext t
  have h := hi.inj _ (Γ.pt (b t)) (Γ.pt (c t)) ((hb t).trans (hc t).symm)
  let p : Spec (CommRingCat.of (FractionRing R)) := (⊥ : PrimeSpectrum (FractionRing R))
  exact Γ.pt_inj _ _ p p (by rw [h])

end GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.TensorOrderReduction
