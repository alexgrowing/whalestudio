import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MayerVietoris

theorem cpull_add {R : Type} [CommRing R] {K L : Cx R} (f g : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (f + g) I n x = cpull f I n x + cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_add, Cochain.add_comp]

theorem cpull_neg {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull (-f) I n x = -cpull f I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, ← CohomologyClass.mk_neg]
  congr 1; apply Cocycle.ext; simp [zcomp, Cochain.ofHom_neg, Cochain.neg_comp]

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := (GlobalTheory.EtC.ZcFun.main R).2.1 f g I n x

theorem cpull_lift {R : Type} [CommRing R] {K L M : Cx R} (a : M ⟶ K) (b : M ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y = cpull a I n (cpull biprod.inl I n y) + cpull b I n (cpull biprod.inr I n y) := by
  rw [biprod.lift_eq, cpull_add, cpull_comp, cpull_comp]

def mvS (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]
      simp)

theorem mvS_exact (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS R f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

def mvMap (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS R f g ⟶ mvS R f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext <;> simp [mvS, ← Functor.map_comp] <;> congr 1 <;> first | exact pullback.lift_fst _ _ _ | exact pullback.lift_snd _ _ _ | simp [pullback.map]
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [mvS, ← Functor.map_comp, hu, hv]

end GlobalTheory.EtC.MayerVietoris
end

theorem GlobalTheory.EtC.mayerVietoris : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun f g h n => D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e1, e2, e3⟩ := hex _ (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n
    have bij := fun m => GlobalTheory.EtC.cpull_biprod_bijective R ((chains R).obj U) ((chains R).obj V) (res R F) m

    have hg : ∀ m (x : H R E F m), cpull biprod.inl (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R f F m x ∧
        cpull biprod.inr (res R F) m (cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) m x) = pull R g F m x := by
      intro m x
      constructor
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj U) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inl (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inl_desc]; rfl
      · refine (GlobalTheory.EtC.MayerVietoris.cpull_comp (K := (chains R).obj V) (L := (chains R).obj U ⊞ (chains R).obj V) biprod.inr (biprod.desc ((chains R).map f) ((chains R).map g)) _ m x).symm.trans ?_
        rw [biprod.inr_desc]; rfl
    have hf : ∀ y, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
      intro y
      have := GlobalTheory.EtC.MayerVietoris.cpull_lift (K := (chains R).obj U) (L := (chains R).obj V) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) (res R F) n y
      rw [GlobalTheory.EtC.MayerVietoris.cpull_neg] at this
      rw [sub_eq_add_neg]; exact this
    have k1 : ∀ y, (pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) - pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) = 0) ↔ ∃ x, cpull (GlobalTheory.EtC.MayerVietoris.mvS R f g).g (res R F) n x = y :=
      fun y => (Iff.of_eq (congrArg (· = 0) (hf y))).symm.trans (e1 y)
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (bij n).2 (a, b)
      simp only [Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      refine sub_eq_zero.symm.trans ((k1 y).trans ⟨?_, ?_⟩)
      · rintro ⟨x, rfl⟩; exact ⟨x, (hg n x).1.symm, (hg n x).2.symm⟩
      · rintro ⟨x, h1, h2⟩
        exact ⟨x, (bij n).1 (Prod.ext ((hg n x).1.trans h1) ((hg n x).2.trans h2))⟩
    · intro c
      show D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = 0 ↔ _
      refine (e2 c).trans ⟨?_, ?_⟩
      · rintro ⟨y, rfl⟩; exact ⟨_, _, hf y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (bij n).2 (a, b)
        simp only [Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        exact ⟨y, hf y⟩
    · intro x
      show _ ↔ ∃ c, D (GlobalTheory.EtC.MayerVietoris.mvS R f g) (GlobalTheory.EtC.MayerVietoris.mvS_exact R f g h) n c = x
      refine Iff.trans ?_ (e3 x)
      constructor
      · rintro ⟨h1, h2⟩
        apply (bij (n + 1)).1
        exact Prod.ext (((hg (n + 1) x).1.trans h1).trans (map_zero _).symm) (((hg (n + 1) x).2.trans h2).trans (map_zero _).symm)
      · intro h0
        refine ⟨(hg (n + 1) x).1.symm.trans ?_, (hg (n + 1) x).2.symm.trans ?_⟩ <;> rw [h0] <;> exact map_zero _
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ _ _ (GlobalTheory.EtC.MayerVietoris.mvMap R f g f' g' p u v hu hv) n c
