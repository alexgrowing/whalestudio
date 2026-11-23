import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductMapBijectiveFiniteStrictHStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelOne

variable {R : Type} [CommRing R]

theorem pull_iso_bijective' {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar B) = laurentVar C := by
  ext
  simp only [laurentVar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have h := congrArg (fun g => g.hom (LaurentPolynomial.T 1 : LaurentPolynomial B))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [laurentMap_T] at h
  exact h.symm

end GlobalTheory.EtC.GmStep.LevelOne

namespace GlobalTheory.EtC.GmStep.LevelOne

theorem rowOne_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (rowOne A A' q i k) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, h2⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr1 := GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap1 := congrArg (fun f => disc.map f) h1
  have hmap2 := congrArg (fun f => disc.map f) h2
  simp only [Functor.map_comp] at hmap1 hmap2
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.comp
      (LaurentPolynomial.C : A →+* LaurentPolynomial A))
    simpa using this
  have hkum : pull _ (disc.map e.hom) (tw q 1) 1 (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A))) =
      kum q (laurentVar (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) := by
    rw [← pull_comp, augK]
    erw [hmap2]
    have := (GlobalTheory.EtC.a6nat_holds q).2.2.2 (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A
      (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) (laurentVar A) hqL
    rw [laurentVar_map] at this
    exact this
  have hcst : ∀ a, pull _ (disc.map e.hom) (tw q (i - 1)) 0
      (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q (i - 1)) 0
        (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    rw [← pull_comp, hmap1, pull_comp]
    rfl
  have heq : ∀ a, pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1 (rowOne A A' q i k a) =
      gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    simp only [rowOne, gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [pull_cast, (GlobalTheory.EtC.a6nat_holds q).1, hcst, hkum]
    rfl
  have hcomp : (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) ∘ (rowOne A A' q i k) =
      (gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i) ∘ (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) :=
    pull_iso_bijective' (disc.mapIso e) (tw q i) 1
  have he0 : Function.Bijective (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    pull_iso_bijective' (disc.mapIso e0) (tw q (i - 1)) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr1.comp he0

end GlobalTheory.EtC.GmStep.LevelOne
