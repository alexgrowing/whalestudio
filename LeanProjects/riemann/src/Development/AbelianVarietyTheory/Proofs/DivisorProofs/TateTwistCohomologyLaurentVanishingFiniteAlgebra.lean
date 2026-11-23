import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.LaurentFinite

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h : g.comp f = RingHom.id A) : spMap g ≫ spMap f = 𝟙 (sp A) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  simp

theorem subsingleton_of_retract (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (h : g.comp f = RingHom.id A)
    (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q (sp A) n i, pull _ (spMap g) _ _ (pull _ (spMap f) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp_eq_id f g h, pull_id]
  rw [← key x, ← key y, Subsingleton.elim (pull _ (spMap f) _ _ x) (pull _ (spMap f) _ _ y)]

theorem subsingleton_of_ringEquiv (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) :=
  subsingleton_of_retract q n i e.toRingHom e.symm.toRingHom (by ext x; simp) hB

theorem subsingleton_of_subsingleton (q : ℕ) (n i : ℤ) (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (Ht q (sp T) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q T T n i).2 (a, b)
  simp only [Prod.mk.injEq] at hx
  rw [← hx.1, ← hx.2, hfs]

instance laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_one (LaurentPolynomial.C (R := T)), Subsingleton.elim (1 : T) 0, map_zero]

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

noncomputable def laurentProd (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    LaurentPolynomial (T₁ × T₂) →+* LaurentPolynomial T₁ × LaurentPolynomial T₂ :=
  RingHom.prod (AddMonoidAlgebra.mapRingHom ℤ (RingHom.fst T₁ T₂))
    (AddMonoidAlgebra.mapRingHom ℤ (RingHom.snd T₁ T₂))

theorem laurentProd_C_mul_T (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] (c : T₁ × T₂) (n : ℤ) :
    laurentProd T₁ T₂ (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      (LaurentPolynomial.C c.1 * LaurentPolynomial.T n, LaurentPolynomial.C c.2 * LaurentPolynomial.T n) := by
  simp only [← LaurentPolynomial.single_eq_C_mul_T, laurentProd, RingHom.prod_apply,
    AddMonoidAlgebra.mapRingHom_single, RingHom.coe_fst, RingHom.coe_snd]

theorem laurentProd_injective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Injective (laurentProd T₁ T₂) := by
  intro x y h
  simp only [laurentProd, RingHom.prod_apply, Prod.mk.injEq] at h
  ext m
  all_goals
    have h1 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.1
    have h2 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.2
    simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.coe_fst, RingHom.coe_snd] at h1 h2
    assumption

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

theorem laurentProd_surjective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Surjective (laurentProd T₁ T₂) := by
  have hl : ∀ f : LaurentPolynomial T₁, (f, 0) ∈ (laurentProd T₁ T₂).range := by
    intro f
    induction f using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (a, 0) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  have hr : ∀ g : LaurentPolynomial T₂, (0, g) ∈ (laurentProd T₁ T₂).range := by
    intro g
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (0, a) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  rintro ⟨f, g⟩
  have := add_mem (hl f) (hr g)
  simpa using this

theorem subsingleton_laurent_prod (q : ℕ) (n i : ℤ) (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (h₁ : Subsingleton (Ht q (sp (LaurentPolynomial T₁)) n i))
    (h₂ : Subsingleton (Ht q (sp (LaurentPolynomial T₂)) n i)) :
    Subsingleton (Ht q (sp (LaurentPolynomial (T₁ × T₂))) n i) := by
  let e := RingEquiv.ofBijective (laurentProd T₁ T₂)
    ⟨laurentProd_injective T₁ T₂, laurentProd_surjective T₁ T₂⟩
  refine subsingleton_of_ringEquiv q n i e ⟨fun x y => ?_⟩
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q _ _ n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end GlobalTheory.EtC.LaurentFinite

open GlobalTheory.EtC.LaurentFinite in

theorem GlobalTheory.EtC.laurent_vanishing_finite : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  intro q _ n hyp A _ _ hA hq
  refine GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun T _ _ => ∀ s i : ℤ, 2 ≤ s → s < n →
      Subsingleton (Ht q (sp (LaurentPolynomial T)) s i)) ?_ ?_ ?_ ?_
  · intro T T' _ _ _ _ e hT s i h2 hs
    exact subsingleton_of_ringEquiv q s i
      (AddMonoidAlgebra.mapRingEquiv ℤ e.symm.toRingEquiv) (hT s i h2 hs)
  · intro T _ _ _ s i _ _
    exact subsingleton_of_subsingleton q s i _
  · intro T₁ T₂ _ _ _ _ _ _ h₁ h₂ s i h2 hs
    exact subsingleton_laurent_prod q s i T₁ T₂ (h₁ s i h2 hs) (h₂ s i h2 hs)
  · intro T _ _ hfin hT s i h2 hs
    haveI : IsNoetherian A T := isNoetherian_of_isNoetherianRing_of_finite A T
    haveI : IsNoetherianRing T := isNoetherian_of_tower A inferInstance
    have hqT : IsUnit (q : T) := by
      simpa using hq.map (algebraMap A T)
    exact hyp T hT hqT s i h2 hs
