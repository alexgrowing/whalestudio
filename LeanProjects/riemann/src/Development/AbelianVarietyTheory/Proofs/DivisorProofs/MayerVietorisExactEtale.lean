import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainComplexExactSquare
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.EtC.ExcisionNat

abbrev C (R : Type) [CommRing R] (B : Type) [CommRing B] : Cx R := (chains R).obj (sp B)

abbrev Cm (R : Type) [CommRing R] {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') : C R B' ⟶ C R B :=
  (chains R).map (spMap g)

theorem spMap_comp {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B) (g : B →+* B') :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem Cm_comp (R : Type) [CommRing R] {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B)
    (g : B →+* B') : Cm R g ≫ Cm R h = Cm R (g.comp h) := by
  rw [← Functor.map_comp, spMap_comp]

theorem awayMap_comp_algebraMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
  IsLocalization.map_comp _

theorem awayHom_comp_awayMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (Localization.awayMap (algebraMap A A') f) = Localization.awayMap (algebraMap A A'') f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, awayMap_comp_algebraMap, ← RingHom.comp_assoc, awayHom_comp_algebraMap,
    awayMap_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

def exSC (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    ShortComplex (Cx R) :=
  ShortComplex.mk
    (biprod.lift (Cm R (Localization.awayMap (algebraMap A A') f))
      (-Cm R (algebraMap A' (Localization.Away (algebraMap A A' f)))))
    (biprod.desc (Cm R (algebraMap A (Localization.Away f))) (Cm R (algebraMap A A')))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Cm_comp, Cm_comp, awayMap_comp_algebraMap, add_neg_cancel])

theorem exSC_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A) (hN : IsNbhd A A' f) : (exSC R A A' f).ShortExact := by
  refine GlobalTheory.T.chain_complex_exact_square R _ _ _ _ ?_ (exSC R A A' f).zero (GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f hN ?_)
  all_goals
    simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayMap_comp_algebraMap, add_neg_cancel]

def exMap (R : Type) [CommRing R] {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) : exSC R A A'' f ⟶ exSC R A A' f where
  τ₁ := Cm R (awayHom φ f)
  τ₂ := biprod.map (𝟙 _) (Cm R φ.toRingHom)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [exSC, Category.assoc, biprod.lift_fst, biprod.map_fst, Category.comp_id, Cm_comp, awayHom_comp_awayMap]
    · simp only [exSC]
      rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
        Preadditive.comp_neg, Preadditive.neg_comp, Cm_comp, Cm_comp, awayHom_comp_algebraMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [exSC, biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc, Category.comp_id]
    · simp only [exSC, biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, Cm_comp]
      congr 2
      exact RingHom.ext fun a => φ.commutes a

theorem excision_natural : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  intro q A A' _ _ _ _ f hN n i
  have hI : ∀ k, Injective ((res (ZMod q) (tw q i)).X k) := fun k =>
    inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X k))
  obtain ⟨d, hex, hnat⟩ := longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) hI
  have hS := exSC_shortExact (ZMod q) A A' f hN
  refine ⟨d (exSC (ZMod q) A A' f) hS n, ?_, ?_⟩
  · intro x
    refine Iff.trans ?_ ((hex _ hS n).2.2 x)
    have hb := (cpull_biprod_bijective (ZMod q) (C (ZMod q) (Localization.Away f)) (C (ZMod q) A')
      (res (ZMod q) (tw q i)) (n + 1)).1
    have e1 : pull (ZMod q) (spMap (algebraMap A (Localization.Away f))) (tw q i) (n + 1) x =
        cpull (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A (Localization.Away f)) := biprod.inl_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    have e2 : pull (ZMod q) (spMap (algebraMap A A')) (tw q i) (n + 1) x =
        cpull (biprod.inr : C (ZMod q) A' ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inr : C (ZMod q) A' ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A A') := biprod.inr_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    change (_, _) = ((0, 0) : _ × _) ↔ _
    rw [e1, e2]
    obtain ⟨y, hy⟩ : ∃ y : CohomologyClass (C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') (res (ZMod q) (tw q i)) (n + 1),
      y = cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x := ⟨_, rfl⟩
    rw [← hy]
    constructor
    · intro h
      apply hb
      dsimp only
      rw [h]
      exact Prod.ext (map_zero _).symm (map_zero _).symm
    · intro h
      rw [h]
      exact Prod.ext (map_zero _) (map_zero _)
  · intro A'' _ _ _ φ hN'' z hz
    have hS'' := exSC_shortExact (ZMod q) A A'' f hN''
    have h := hnat _ _ hS'' hS (exMap (ZMod q) φ f) n z
    have hz' : cpull (exMap (ZMod q) φ f).τ₁ (res (ZMod q) (tw q i)) n z = 0 := hz
    rw [hz', map_zero] at h
    have hid : cpull (exMap (ZMod q) φ f).τ₃ (res (ZMod q) (tw q i)) (n + 1) (d _ hS n z) = d _ hS n z :=
      ZcFun.cpull_id _ _ _ _
    rw [hid] at h
    exact h

end GlobalTheory.EtC.ExcisionNat
