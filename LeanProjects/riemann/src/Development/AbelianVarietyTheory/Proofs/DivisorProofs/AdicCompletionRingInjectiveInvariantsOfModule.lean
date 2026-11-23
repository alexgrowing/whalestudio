import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg

section CompletionTransfer

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem pow_smul_top_eq_restrictScalars (n : ℕ) :
    (J ^ n • ⊤ : Submodule A B) =
      ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  ext x
  simp [smul_eq_mul, Ideal.mul_top]

def levelEquiv (n : ℕ) :
    (B ⧸ (J ^ n • ⊤ : Submodule A B)) ≃ₗ[A] (B ⧸ ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_restrictScalars J n)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

theorem levelEquiv_transitionMap {m n : ℕ} (hmn : m ≤ n) (q : B ⧸ (J ^ n • ⊤ : Submodule A B)) :
    levelEquiv J m (AdicCompletion.transitionMap J B hmn q) =
      AdicCompletion.transitionMap (J.map (algebraMap A B)) B hmn (levelEquiv J n q) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def complEquivFun (x : AdicCompletion J B) : AdicCompletion (J.map (algebraMap A B)) B :=
  ⟨fun n => levelEquiv J n (x.val n), fun {m n} hmn => by
    rw [← levelEquiv_transitionMap, x.property hmn]⟩

theorem complEquivFun_val (x : AdicCompletion J B) (n : ℕ) :
    (complEquivFun J x).val n = levelEquiv J n (x.val n) := rfl

theorem complEquivFun_injective : Function.Injective (complEquivFun (B := B) J) := by
  intro x y h
  refine AdicCompletion.ext fun n => (levelEquiv J n).injective ?_
  have := congrArg (fun z : AdicCompletion (J.map (algebraMap A B)) B => z.val n) h
  simpa only [complEquivFun_val] using this

theorem complEquivFun_surjective : Function.Surjective (complEquivFun (B := B) J) := by
  intro z
  refine ⟨⟨fun n => (levelEquiv J n).symm (z.val n), fun {m n} hmn => ?_⟩, ?_⟩
  · apply (levelEquiv J m).injective
    rw [levelEquiv_transitionMap, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact z.property hmn
  · refine AdicCompletion.ext fun n => ?_
    exact LinearEquiv.apply_symm_apply (levelEquiv J n) (z.val n)

end CompletionTransfer

theorem val_eq_mk_of_evalₐ {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b) :
    y.val n = Submodule.Quotient.mk b := by
  have hle : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.eval_apply, ← AdicCompletion.factor_evalₐ_eq_eval I y hle, h]
  rfl

theorem evalₐ_eq_mk_of_val {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : y.val n = Submodule.Quotient.mk b) :
    AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b := by
  have hle : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I y hle, AdicCompletion.eval_apply, h]
  rfl

theorem cmap_transfer : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  intro A B _ _ _ J Γ g hinj hrange
  have h1 : ∀ x, complEquivFun J (AdicCompletion.map J (Algebra.linearMap A B) x) =
      cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl x := by
    intro x
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← ha]
    symm
    apply val_eq_mk_of_evalₐ
    rw [evalₐ_cmap, evalₐ_eq_mk_of_val J x n a ha.symm, Ideal.quotientMap_mk]
    rfl
  have h2 : ∀ σ z, complEquivFun J (AdicCompletion.map J (g σ).toLinearMap z) =
      cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (map_algebraMap_le (g σ) J) (complEquivFun J z) := by
    intro σ z
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← hb]
    symm
    apply val_eq_mk_of_evalₐ
    refine (evalₐ_cmap _ _ _ _ n _).trans ?_
    rw [evalₐ_eq_mk_of_val _ (complEquivFun J z) n b
      (by rw [complEquivFun_val, ← hb]; rfl), Ideal.quotientMap_mk]
    rfl
  refine ⟨fun x y hxy => hinj (complEquivFun_injective J (by rw [h1, h1, hxy])), fun y => ?_⟩
  obtain ⟨z, rfl⟩ := complEquivFun_surjective J y
  constructor
  · rintro ⟨x, hx⟩ σ
    have hz : z ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) :=
      ⟨x, complEquivFun_injective J (by rw [h1, hx])⟩
    rw [← h2, (hrange z).1 hz σ]
  · intro h
    obtain ⟨x, hx⟩ := (hrange z).2 fun σ => complEquivFun_injective J (by rw [h2, h σ])
    exact ⟨x, by rw [← h1, hx]⟩

end GlobalTheory.InvAlg
