import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Pbf

private theorem const_comp_single {A B : Type} [Monoid A] [Monoid B] (G : SingleObj A ⥤ SingleObj B) (J : Type) [Category J] :
    (Functor.const J).obj (SingleObj.star A) ⋙ G = (Functor.const J).obj (SingleObj.star B) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun a b h => by simp)

def triv (E : Spc) (N : ℕ) : E ⟶ ofCat (glCat N) where
  app k :=
    { app := fun T => TypeCat.ofHom fun _ =>
        (show Fin (k.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(T.unop, ⊤)) from (Functor.const _).obj (SingleObj.star _))
      naturality := fun T T' f => by
        ext x
        exact (const_comp_single ((glCat N).map (Scheme.Γ.map f)).toFunctor _).symm }
  naturality m n f := by
    ext T x
    rfl

def LH (q : ℕ) {X E : Spc} (π : X ⟶ E) {m : ℕ} (d e : Fin m → ℤ) (c : ∀ j, Ht q X (d j) (e j)) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : ∀ j, Ht q E (n - d j) (i - e j) =>
    ∑ j, ((cup q (pull _ π _ _ (a j)) (c j)).cast (by ring) (by ring) : Ht q X n i)

def PBF (q : ℕ) (E : Spc) (N : ℕ) : Prop :=
  LH q (pullback.fst (triv E N) (PGL.pr N)) (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ))
    (fun j => cpow q (c1 q (pullback.snd (triv E N) (PGL.pr N) ≫ PGL.line N)) j)

def IsMVd {R : Type} [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (F : Shv R) (n : ℤ)
    (c : H R (pullback f g) F n) (x : H R E F (n + 1)) : Prop :=
  ∃ (γ : Cocycle ((chains R).obj (pullback f g)) (res R F) n) (ζ : Cocycle ((chains R).obj E) (res R F) (n + 1))
    (α : Cochain ((chains R).obj U) (res R F) n) (β : Cochain ((chains R).obj V) (res R F) n),
    CohomologyClass.mk γ = c ∧ CohomologyClass.mk ζ = x ∧
    (Cochain.ofHom ((chains R).map (pullback.fst f g))).comp α (zero_add n) -
      (Cochain.ofHom ((chains R).map (pullback.snd f g))).comp β (zero_add n) = γ.1 ∧
    δ n (n + 1) α = (Cochain.ofHom ((chains R).map f)).comp ζ.1 (zero_add (n + 1)) ∧
    δ n (n + 1) β = (Cochain.ofHom ((chains R).map g)).comp ζ.1 (zero_add (n + 1))

abbrev LqR (q : ℕ) : Type := LaurentPolynomial (Localization.Away (q : ℤ))

abbrev Gq (q : ℕ) : Scheme.{0} := Spec (CommRingCat.of (LqR q))

abbrev A1 : Scheme.{0} := Spec (CommRingCat.of (Polynomial ℤ))

def tR (q : ℕ) : (LqR q)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

def tq (q : ℕ) : (Γ(Gq q, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom.toMonoidHom (tR q)

def kappa (q : ℕ) : Ht q (sch.obj (Gq q)) 1 1 := kum q (tq q)

def IsTrivBy {X : Spc} (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx X 0 T → (Γ(T, ⊤))ˣ) : Prop :=
  (∀ {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx X 0 T), w T' (x.res g) = Units.map g.appTop.hom.toMonoidHom (w T x)) ∧
  ∀ (T : Scheme.{0}) (x : Sx X 1 T), lineUnit L x * w T (x.face 0) = w T (x.face 1)

end UpperTheory.Pbf

end
