import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsoWidePullbackYoneda
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem T_eq_unit_zpow (B : Type) [CommRing B] (m : ℤ) :
    (LaurentPolynomial.T m : LaurentPolynomial B) =
      ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) := by
  have h := laurentMap_T (RingHom.id B) m
  rw [laurentMap, LaurentPolynomial.eval₂_T] at h
  exact h.symm

theorem laurent_ringHom_ext {B R : Type} [CommRing B] [CommRing R] {φ ψ : LaurentPolynomial B →+* R}
    (hC : φ.comp LaurentPolynomial.C = ψ.comp LaurentPolynomial.C)
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have hu : Units.map φ.toMonoidHom (laurentVarUnit B) = Units.map ψ.toMonoidHom (laurentVarUnit B) :=
    Units.ext hT
  have e : ∀ (χ : LaurentPolynomial B →+* R) (m : ℤ),
      χ ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) =
        ((Units.map χ.toMonoidHom (laurentVarUnit B) ^ m : Rˣ) : R) := by
    intro χ m
    rw [← map_zpow]
    rfl
  have hTm : ∀ m : ℤ, φ (LaurentPolynomial.T m) = ψ (LaurentPolynomial.T m) := fun m => by
    rw [T_eq_unit_zpow, e φ, e ψ, hu]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | C_mul_T n b => rw [map_mul, map_mul, hTm n, ← RingHom.comp_apply, hC, RingHom.comp_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) :=
  laurent_ringHom_ext (RingHom.ext fun a => by simp [laurentMap_C])
    (by rw [RingHom.comp_apply, laurentMap_T, laurentMap_T, laurentMap_T])

theorem tensorPow_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem laurent_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (LaurentPolynomial B →+* R))
    (hg : ∀ j, (g j).comp (laurentMap a) = (g 0).comp (laurentMap a)) :
    ∃! φ : LaurentPolynomial T →+* R, ∀ j, φ.comp (laurentMap (ι j)) = g j := by
  have hT : ∀ j, g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := fun j => by
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    rwa [RingHom.comp_apply, RingHom.comp_apply, laurentMap_T] at this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp LaurentPolynomial.C) (fun j => by
    refine RingHom.ext fun x => ?_
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C x)
    simpa [laurentMap_C] using this)
  let u : Rˣ := Units.map (g 0).toMonoidHom (laurentVarUnit B)
  refine ⟨LaurentPolynomial.eval₂ ψ u, fun j => ?_, fun φ hφ => ?_⟩
  · apply laurent_ringHom_ext
    · refine RingHom.ext fun b => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, laurentMap_C, LaurentPolynomial.eval₂_C]
      exact RingHom.congr_fun (hψ j) b
    · rw [RingHom.comp_apply, laurentMap_T, LaurentPolynomial.eval₂_T, zpow_one, hT j]
      rfl
  · have hC : φ.comp LaurentPolynomial.C = ψ := hψu _ (fun j => by
      refine RingHom.ext fun b => ?_
      have := RingHom.congr_fun (hφ j) (LaurentPolynomial.C b)
      simpa [laurentMap_C] using this)
    apply laurent_ringHom_ext
    · refine RingHom.ext fun t => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.eval₂_C, ← hC]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      have := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
      rw [RingHom.comp_apply, laurentMap_T] at this
      rw [this]
      rfl

end GlobalTheory.EtC.GmStep.LevelIso

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem level_iso : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  intro A A' _ _ _ k
  let ι : Fin (k + 1) → (A' →+* PiTensorProduct A (fun _ : Fin (k + 1) => A')) := fun j =>
    (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).toRingHom
  have hιA : ∀ j, (ι j).comp (algebraMap A A') = algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    fun j => RingHom.ext fun x => (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).commutes x
  have hι : ∀ j, (ι j).comp (algebraMap A A') = (ι 0).comp (algebraMap A A') := fun j => by rw [hιA, hιA]
  have hu := tensorPow_univ A A' k
  obtain ⟨e0, he0⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback A A' _ (algebraMap A A') k ι hι hu
  have hι' : ∀ j, (laurentMap (ι j)).comp (laurentMap (algebraMap A A')) =
      (laurentMap (ι 0)).comp (laurentMap (algebraMap A A')) := by
    intro j; rw [laurentMap_comp, laurentMap_comp, hι j]
  obtain ⟨e, he⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback (LaurentPolynomial A) (LaurentPolynomial A')
    (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) (laurentMap (algebraMap A A')) k
    (fun j => laurentMap (ι j)) hι' (laurent_univ A A' _ (algebraMap A A') k ι (fun R _ g hg => hu R g hg))
  refine ⟨e0, e, ?_, ?_⟩
  · change e.hom ≫ WidePullback.lift _ _ _ = _
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, WidePullback.lift_π, Arrow.mk_hom, laurentHom, baseHom]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he j)).trans ?_)
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (he0 j)).symm
      simp only [constSq, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
    · simp only [Category.assoc, WidePullback.lift_base, Arrow.mk_hom, laurentHom, baseHom]
      rw [← WidePullback.π_arrow _ 0]
      simp only [Category.assoc]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he 0)).trans ?_)
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) (((congrArg (· ≫ yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (he0 0)).symm.trans (Category.assoc _ _ _)).trans (congrArg (e0.hom ≫ ·) (WidePullback.π_arrow _ 0)))).trans (Category.assoc _ _ _).symm)
      simp only [constSq, Arrow.homMk_right, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
      congr 3
      exact RingHom.ext fun x => by simp [laurentMap_C]
  · change e.hom ≫ WidePullback.base _ = _
    rw [← WidePullback.π_arrow _ 0, ← Category.assoc, he 0]
    simp only [laurentHom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, laurentMap_comp, hιA 0]

end GlobalTheory.EtC.GmStep.LevelIso
