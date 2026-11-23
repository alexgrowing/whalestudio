import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.ParPt

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def derHom (δ : Ω[B⁄R] →ₗ[B] B) : B →ₐ[R] DualNumber B where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (δ (D R B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).fst = b := by simp [derHom]

theorem snd_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).snd = δ (D R B b) := by simp [derHom]

theorem eq_of_derHom_eq {δ₁ δ₂ : Ω[B⁄R] →ₗ[B] B} (h : ∀ b, derHom δ₁ b = derHom δ₂ b) : δ₁ = δ₂ := by
  have h' : ∀ b, δ₁ (D R B b) = δ₂ (D R B b) := fun b ↦ by
    rw [← snd_derHom, ← snd_derHom, h]
  exact Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext h')

end Alg

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem eq_of_affPt_eq {δ₁ δ₂ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1}
    (h : spMap (derHom δ₁ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U =
      spMap (derHom δ₂ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U) : δ₁ = δ₂ := by
  have := GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 h
  exact eq_of_derHom_eq fun b ↦ RingHom.congr_fun this b

theorem exists_derHom (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (he : spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom ≫ y = affPt s U) :
    ∃ δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1,
      spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y := by
  have hsurj : Surjective (spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom) := by
    refine ⟨fun x ↦ ?_⟩
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker
        (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom : Set (DualNumber (Sec s U.1))) :=
      fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        have h2 : a * a = 0 := by ext <;> simp [ha']
        exact x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, h2]; exact zero_mem _)
    rw [← range_comap_of_surjective _ _ (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)] at hx
    exact hx
  have htop : ⊤ ≤ y ⁻¹ᵁ U.1 := by
    intro p _
    obtain ⟨q, rfl⟩ := hsurj.surj p
    change ((spMap _ ≫ y).base q) ∈ U.1
    rw [he]
    have k := IsAffineOpen.range_fromSpec U.2
    rw [Set.ext_iff] at k
    exact (k _).1 ⟨q, rfl⟩
  let α := GlobalTheory.CechKS.FormLocal.valHom y htop hy
  have hα : spMap (α : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.2 y htop hy
  have hfst : ∀ b, (α b).fst = b := by
    have k : (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom.comp
        (α : Sec s U.1 →+* DualNumber (Sec s U.1)) = RingHom.id _ := by
      refine GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 ?_
      change spMap _ ≫ affPt s U = spMap _ ≫ affPt s U
      rw [Cris.spMap_comp, Category.assoc, hα, he, Cris.spMap_id, Category.id_comp]
    exact fun b ↦ RingHom.congr_fun k b
  let d : Derivation R (Sec s U.1) (Sec s U.1) :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul]
        simp [MulOpposite.smul_eq_mul_unop, hfst]
        ring }
  refine ⟨d.liftKaehlerDifferential, ?_⟩
  have hd : derHom d.liftKaehlerDifferential = α := by
    ext b
    · rw [fst_derHom, hfst]
    · rw [snd_derHom, Derivation.liftKaehlerDifferential_comp_D]; rfl
  rw [hd, hα]
end Geo

section Val

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem snd_val_derHom (δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1) (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (e : spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).val y hy f.1) =
      δ (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt (Sec s U.1) (Sec s U.1) :=
    { toFun := fun c ↦ TrivSqZeroExt.inl c.fst + TrivSqZeroExt.inr (δ c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add, map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  let α₀ : Sec s U.1 →ₐ[R] Sec s U.1 := AlgHom.id R _
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π (Φ c) :=
    fun c ↦ by simp [Φ, α₀]
  have e₀ : spMap (α₀ : Sec s U.1 →+* Sec s U.1) ≫ affPt s U =
      spMap ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π : TrivSqZeroExt (Sec s U.1) (Sec s U.1) →+* Sec s U.1) ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    ext b
    simp [α₀, fst_derHom]
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R (Sec s U.1) (Sec s U.1)) Φ α₀ hπ hx
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv (Sec s U.1) _ ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt (Sec s U.1) (Sec s U.1)) y hy :=
    Thick.trivHom (derHom δ) e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).secHom
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy)
    (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).i (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change derHom δ c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, fst_derHom, fst_derSec]
      · simp [Φ, snd_derHom, snd_derSec]
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, hΦ]
  rfl

end Val

end GlobalTheory.ParPt
