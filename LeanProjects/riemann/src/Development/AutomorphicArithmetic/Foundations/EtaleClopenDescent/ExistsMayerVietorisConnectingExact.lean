import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.MV

variable {R : Type} [CommRing R]

private theorem cpull_comp' {K L M I : Cx R} (a : K ⟶ L) (b : L ⟶ M) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (a ≫ b) I n x = cpull a I n (cpull b I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem cpull_add' {K L I : Cx R} (a b : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (a + b) I n x = cpull a I n x + cpull b I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem cpull_neg' {K L I : Cx R} (a : K ⟶ L) (n : ℤ)
    (x : CohomologyClass L I n) : cpull (-a) I n x = - cpull a I n x := by
  have h : cpull (-a + a) I n x = 0 := by
    rw [neg_add_cancel]
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpre_mk]
    have : zcomp (Cocycle.ofHom (0 : K ⟶ L)) x (zero_add n) = 0 := by
      refine Cocycle.ext ?_
      simp [zcomp]
    rw [this]
    exact CohomologyClass.mk_zero _ _ _
  rw [cpull_add'] at h
  exact eq_neg_of_add_eq_zero_left h

private noncomputable def mvS {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : ShortComplex (Cx R) :=
  ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
        pullback.condition, add_neg_cancel])

private theorem mvS_exact {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) :
    (mvS (R := R) f g).ShortExact := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact R f g h
  exact hw

private noncomputable def mvMap {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
    (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') :
    mvS (R := R) f g ⟶ mvS f' g' where
  τ₁ := (chains R).map (pullback.map f g f' g' u v p hu hv)
  τ₂ := biprod.map ((chains R).map u) ((chains R).map v)
  τ₃ := (chains R).map p
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [mvS, Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc,
        ← Functor.map_comp, pullback.lift_fst, pullback.map]
    · simp only [mvS, Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc,
        Preadditive.neg_comp, Preadditive.comp_neg, ← Functor.map_comp, pullback.lift_snd, pullback.map]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [mvS, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, ← Functor.map_comp, hu]
    · simp only [mvS, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, ← Functor.map_comp, hv]

private theorem cpull_inl_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inl : K ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull a I n x := by
  rw [← cpull_comp', biprod.inl_desc]

private theorem cpull_inr_desc {K L M I : Cx R} (a : K ⟶ M) (b : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (biprod.inr : L ⟶ K ⊞ L) I n (cpull (biprod.desc a b) I n x) = cpull b I n x := by
  rw [← cpull_comp', biprod.inr_desc]

private theorem cpull_lift {K L P I : Cx R} (a : P ⟶ K) (b : P ⟶ L) (n : ℤ) (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a b) I n y =
      cpull a I n (cpull (biprod.inl : K ⟶ K ⊞ L) I n y) + cpull b I n (cpull (biprod.inr : L ⟶ K ⊞ L) I n y) := by
  rw [biprod.lift_eq, cpull_add', cpull_comp', cpull_comp']

end UpperTheory.Cb.MV

theorem UpperTheory.Cb.exists_mayerVietoris_connecting_exact :
    ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  intro R _ F
  obtain ⟨D, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (fun n => by dsimp only [res]; infer_instance)
  have hbij := fun (K L : Cx R) (n : ℤ) => GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective R K L (res R F) n

  have hf : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (n : ℤ) (y : CohomologyClass (((chains R).obj U) ⊞ ((chains R).obj V)) (res R F) n),
      cpull (UpperTheory.Cb.MV.mvS (R := R) f g).f (res R F) n y =
        pull R (pullback.fst f g) F n (cpull biprod.inl (res R F) n y) -
          pull R (pullback.snd f g) F n (cpull biprod.inr (res R F) n y) := by
    intro U V E f g n y
    refine (UpperTheory.Cb.MV.cpull_lift (I := res R F) ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) n y).trans ?_
    rw [UpperTheory.Cb.MV.cpull_neg', sub_eq_add_neg]
    rfl
  refine ⟨fun {U V E} f g h n => D (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n, ?_, ?_⟩
  · intro U V E f g h n
    obtain ⟨e₁, e₂, e₃⟩ := hex (UpperTheory.Cb.MV.mvS f g) (UpperTheory.Cb.MV.mvS_exact f g h) n
    have hi := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inl_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    have hr := fun (m : ℤ) (x : H R E F m) => UpperTheory.Cb.MV.cpull_inr_desc (I := res R F) ((chains R).map f) ((chains R).map g) m x
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
      have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
      have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
      have key := e₁ y
      rw [hf, hya, hyb] at key
      refine (sub_eq_zero.symm.trans key).trans ?_
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, (hi n x).symm.trans hya, (hr n x).symm.trans hyb⟩
      · rintro ⟨x, hxa, hxb⟩
        refine ⟨x, (hbij ((chains R).obj U) ((chains R).obj V) n).1 ?_⟩
        exact Prod.ext ((hi n x).trans (hxa.trans hya.symm)) ((hr n x).trans (hxb.trans hyb.symm))
    · intro c
      refine (e₂ c).trans ?_
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, _, hf f g n y⟩
      · rintro ⟨a, b, rfl⟩
        obtain ⟨y, hy⟩ := (hbij ((chains R).obj U) ((chains R).obj V) n).2 (a, b)
        have hya : cpull biprod.inl (res R F) n y = a := congrArg Prod.fst hy
        have hyb : cpull biprod.inr (res R F) n y = b := congrArg Prod.snd hy
        refine ⟨y, ?_⟩
        rw [hf, hya, hyb]
    · intro x
      constructor
      · rintro ⟨h1, h2⟩
        refine (e₃ x).1 ((hbij ((chains R).obj U) ((chains R).obj V) (n + 1)).1 ?_)
        have z1 : cpull (biprod.inl : (chains R).obj U ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        have z2 : cpull (biprod.inr : (chains R).obj V ⟶ (chains R).obj U ⊞ (chains R).obj V) (res R F) (n + 1) 0 = 0 := map_zero _
        exact Prod.ext ((hi (n + 1) x).trans (h1.trans z1.symm)) ((hr (n + 1) x).trans (h2.trans z2.symm))
      · intro hc
        have h0 : cpull (biprod.desc ((chains R).map f) ((chains R).map g)) (res R F) (n + 1) x = 0 := (e₃ x).2 hc
        have h1 := hi (n + 1) x
        have h2 := hr (n + 1) x
        rw [h0, map_zero] at h1 h2
        exact ⟨h1.symm, h2.symm⟩
  · intro U V E U' V' E' f g f' g' p u v hu hv h h' n c
    exact hnat _ _ (UpperTheory.Cb.MV.mvS_exact f g h) (UpperTheory.Cb.MV.mvS_exact f' g' h')
      (UpperTheory.Cb.MV.mvMap f g f' g' p u v hu hv) n c
