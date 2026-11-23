import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisLocallyConstantTupleRingTensorPowerUniversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionFinitarySheafSectionLocallyConstantStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open Simplicial

namespace GlobalTheory.EtC.GalSec

theorem freePresheaf_map_freeMk {R : Type} [CommRing R] (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  exact ModuleCat.free_map_apply (uliftFunctor.{1, 0}.map (P.map g)) (ULift.up x)

theorem val_nat {R : Type} [CommRing R] {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) {U V : Scheme.{0}} (g : V ⟶ U)
    (x : P.obj (op U)) : val s V (P.map g.op x) = Sec.res g (val s U x) := by
  unfold val freeGen
  calc _ = (s.hom.app (op V)).hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
        ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)))) := by
          rw [freePresheaf_map_freeMk]; rfl
    _ = _ := ?_
  have e1 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  have e2 := congrArg
    (fun φ => φ.hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))))
    (s.hom.naturality g.op)
  simp only [ModuleCat.hom_comp] at e1 e2
  exact (congrArg (fun z => (s.hom.app (op V)).hom z) e1).trans e2

theorem cechPt_nat {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X)
    (y : Fin (k + 1) → (U ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i]) := by
  unfold cechPt
  have hL : yoneda.map g ≫ WidePullback.lift (yoneda.map x) (fun i => yoneda.map (y i))
      (fun i => by rw [← Functor.map_comp, h i]) =
      WidePullback.lift (yoneda.map (g ≫ x)) (fun i => yoneda.map (g ≫ y i))
      (fun i => by rw [← Functor.map_comp, Category.assoc, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, Functor.map_comp]
    · rw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, Functor.map_comp]
  erw [← NatTrans.naturality_apply]
  rw [← hL]
  simp
  rfl

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x') (hy : y = y') :
    cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx hy
  rfl

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (t : Sec F U) :
    Sec.res (a ≫ b) t = Sec.res a (Sec.res b t) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (t : Sec F U) : Sec.res (𝟙 U) t = t := by
  simp [Sec.res]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem ofHom_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] :
    CommRingCat.ofHom (((1 : Ω ≃ₐ[K] Ω) : Ω ≃ₐ[K] Ω) : Ω →+* Ω) = 𝟙 (CommRingCat.of Ω) := by
  ext a
  rfl

theorem tailG_cons_one (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    tailG K Ω k (Fin.cons 1 g) = g := by
  funext i
  simp [tailG]

theorem mul_cons_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    (fun i => σ 0 * (Fin.cons 1 (tailG K Ω k σ) : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) i) = σ := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [tailG]

theorem continuous_tailG (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (k : ℕ) : Continuous (tailG K Ω k) := by
  unfold tailG
  exact continuous_pi fun i => ((continuous_apply 0).inv).mul (continuous_apply i.succ)

private theorem gal_sec_of_lemma {R : Type} [CommRing R] {F : Shv R} (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (k : ℕ)
    (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F)
    (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) :
    val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) =
      Sec.res (Spec.map (CommRingCat.ofHom ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω)))
        (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ))))
          (val s (Spec (CommRingCat.of (LCRing K Ω k)))
            (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k)))
              (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i)))
              (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) := by
  have hb : (ptHom K Ω k σ).comp (baseHom K Ω k) = algebraMap K Ω := by
    rw [← legHom_comp K Ω k 0, ← RingHom.comp_assoc, ptHom_legHom]
    exact RingHom.ext fun a => (σ 0).commutes a
  rw [← res_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ)) = ptHom K Ω k σ from rfl,
    ← val_nat, cechPt_nat]
  congr 1
  apply cechPt_congr
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  · funext i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ptHom_legHom]

theorem gal_sec_of (TopsChoicePartA : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (B : Type) [CommRing B] (g : Fin (k + 1) → (Ω →+* B)) (c : K →+* B), (∀ i, (g i).comp (algebraMap K Ω) = c) → ∃! u : GlobalTheory.EtC.GalSec.LCRing K Ω k →+* B, u.comp (GlobalTheory.EtC.GalSec.baseHom K Ω k) = c ∧ ∀ i, u.comp (GlobalTheory.EtC.GalSec.legHom K Ω k i) = g i) (TopsChoiceSecondBound : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])))) (S2 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x) (S3 : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Sec F (Spec (CommRingCat.of Ω))), IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω => Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x)) : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ := by
  intro R _ F hF K Ω _ _ _ _ k
  obtain ⟨hlim⟩ := TopsChoiceSecondBound (k + 1) K Ω (LCRing K Ω k) (algebraMap K Ω) (baseHom K Ω k) (legHom K Ω k)
    (legHom_comp K Ω k) (TopsChoicePartA K Ω k)
  have hbij := GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ _ k _ _ _ _ hlim
  obtain ⟨hloc, hinj, hsurj⟩ := S2 R F hF (Fin k → (Ω ≃ₐ[K] Ω)) Ω
  refine ⟨?_, ?_, ?_⟩
  · intro s s' hss
    apply hbij.1
    apply hinj
    funext g
    have e := congrFun hss (Fin.cons 1 g)
    simp only at e
    rw [gal_sec_of_lemma, gal_sec_of_lemma] at e
    simpa [tailG_cons_one, ofHom_one, res_id] using e
  · intro s
    rw [IsLocallyConstant.iff_eventually_eq]
    intro σ
    have h1 := (continuous_tailG K Ω k).continuousAt (x := σ) |>.eventually
      ((IsLocallyConstant.iff_eventually_eq _).mp (hloc (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))) (tailG K Ω k σ))
    have h2 := (continuous_apply 0 : Continuous fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => σ 0).continuousAt (x := σ)
      |>.eventually ((IsLocallyConstant.iff_eventually_eq _).mp
        (S3 R F hF K Ω (Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom (tailG K Ω k σ)))) (val s (Spec (CommRingCat.of (LCRing K Ω k))) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (baseHom K Ω k))) (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])))))
        (σ 0))
    filter_upwards [h1, h2] with τ e1 e2
    rw [gal_sec_of_lemma, gal_sec_of_lemma, e1]
    exact e2
  · intro φ hφ heq
    have hψ : IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => φ (Fin.cons 1 g)) :=
      hφ.comp_continuous (continuous_const.finCons continuous_id)
    obtain ⟨t, ht⟩ := hsurj _ hψ
    obtain ⟨s, hs⟩ := hbij.2 t
    refine ⟨s, fun σ => ?_⟩
    rw [gal_sec_of_lemma]
    simp only at hs
    rw [hs, ht, ← heq, mul_cons_tailG]

end GlobalTheory.EtC.GalSec

namespace GlobalTheory.EtC.GalSec

theorem gal_sec : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ), Function.Injective (fun (s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x))) ∧ (∀ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, IsLocallyConstant (fun σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω) => val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)))) ∧ ∀ φ : (Fin (k + 1) → (Ω ≃ₐ[K] Ω)) → Sec F (Spec (CommRingCat.of Ω)), IsLocallyConstant φ → (∀ (τ : Ω ≃ₐ[K] Ω) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)), φ (fun i => τ * σ i) = Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) (φ σ)) → ∃ s : (free R).obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) ⟶ F, ∀ σ, val s (Spec (CommRingCat.of Ω)) (cechPt (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) k (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (fun i => Spec.map (CommRingCat.ofHom ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; congr 2; exact RingHom.ext fun x => (σ i).commutes x)) = φ σ :=
  gal_sec_of GlobalTheory.T.galoisLocallyConstantTupleRing_tensorPower_universal GlobalTheory.T.spec_widePushout_isLimit_widePullback GlobalTheory.T.sec_exists_of_isLocallyConstant_locallyConstant GlobalTheory.T.galoisAction_finitarySheafSection_locallyConstant

end GlobalTheory.EtC.GalSec

end
