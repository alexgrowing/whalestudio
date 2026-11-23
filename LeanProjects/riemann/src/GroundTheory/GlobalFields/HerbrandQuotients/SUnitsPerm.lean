import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.Permutation
import GroundTheory.GlobalFields.HerbrandQuotients.LatticeBridge
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois

namespace GroundTheory.Global

open MulAction NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

section FunPerm

variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]

def funPermRep : Representation k G (X → k) where
  toFun g := LinearMap.funLeft k k (fun x => g⁻¹ • x)
  map_one' := by
    ext f x
    simp [LinearMap.funLeft_apply]
  map_mul' g h := by
    ext f x
    simp [LinearMap.funLeft_apply, mul_smul]

variable {k G X}

@[simp]
theorem funPermRep_apply (g : G) (f : X → k) (x : X) : funPermRep k G X g f x = f (g⁻¹ • x) :=
  rfl

def funEquivMonoidAlgebra [Finite X] : (X → ℤ) ≃+ MonoidAlgebra ℤ X where
  toFun := permOfFun
  invFun f x := f.coeff x
  left_inv F := funext fun x => coeff_permOfFun F x
  right_inv f := by
    ext x
    exact coeff_permOfFun _ x
  map_add' F F' := by
    ext x
    simp

theorem funEquivMonoidAlgebra_funPermRep [Finite X] (g : G) (F : X → ℤ) :
    funEquivMonoidAlgebra (funPermRep ℤ G X g F) =
      Representation.ofMulAction ℤ G X g (funEquivMonoidAlgebra F) := by
  ext x
  change (permOfFun _).coeff x = _
  rw [coeff_permOfFun, Representation.coeff_ofMulAction]
  change _ = (permOfFun F).coeff _
  rw [coeff_permOfFun, funPermRep_apply]

theorem cycHerbrand_funPermRep [Fintype G] [Finite X] [Fintype (orbitRel.Quotient G X)] {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (funPermRep ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by
  rw [cycHerbrand_congr funEquivMonoidAlgebra funEquivMonoidAlgebra_funPermRep σ,
    ← cyclicHerbrand_eq_cycHerbrand, cyclicHerbrand_ofMulAction hσ]

end FunPerm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section Infinite

omit [NumberField L] in
open scoped Classical in

theorem prod_card_stabilizer_infinitePlace
    [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L))] :
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) (InfinitePlace L),
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ) := by
  classical
  refine Fintype.prod_equiv InfinitePlace.orbitRelEquiv _ _ fun ω => ?_
  have h1 : InfinitePlace.orbitRelEquiv ω = (Quotient.out ω).comap (algebraMap K L) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    rfl
  rw [h1, InfinitePlace.card_stabilizer, InfinitePlace.isUnramifiedIn_comap]
  split_ifs <;> simp

end Infinite

section Finite

def placeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, Ideal.under_ne_bot (𝓞 K) w.ne_bot⟩

instance (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (placeBelow (K := K) w).asIdeal :=
  ⟨rfl⟩

omit [NumberField K] [NumberField L] [IsGalois K L] in

theorem eq_placeBelow_of_liesOver {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.asIdeal.LiesOver v.asIdeal) : v = placeBelow w :=
  HeightOneSpectrum.ext h.over

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem placeBelow_smul (g : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    placeBelow (K := K) (g • w) = placeBelow w := by
  symm
  apply eq_placeBelow_of_liesOver
  change ((g • w.asIdeal : Ideal (𝓞 L))).LiesOver _
  infer_instance

variable (S : Set (HeightOneSpectrum (𝓞 L)))

@[reducible] def stableMulAction (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) : MulAction (L ≃ₐ[K] L) S where
  smul g w := ⟨g • w.1, hS g w.1 w.2⟩
  one_smul w := Subtype.ext (one_smul _ w.1)
  mul_smul g h w := Subtype.ext (mul_smul g h w.1)

theorem prod_card_stabilizer_finitePlace (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := stableMulAction S hS
    ∀ [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S)],
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) S,
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ) := by
  let := stableMulAction S hS
  intro _
  have hstab : ∀ x : S, Nat.card (stabilizer (L ≃ₐ[K] L) x) =
      (placeBelow (K := K) x.1).asIdeal.ramificationIdxIn (𝓞 L) *
        (placeBelow (K := K) x.1).asIdeal.inertiaDegIn (𝓞 L) := by
    intro x
    have h1 : stabilizer (L ≃ₐ[K] L) x = stabilizer (L ≃ₐ[K] L) x.1.asIdeal := by
      ext g
      rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
      exact ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
    rw [h1]
    exact Ideal.card_stabilizer_eq (placeBelow (K := K) x.1).asIdeal x.1.asIdeal
  rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
  refine finprod_mem_eq_of_bijOn (fun ω => placeBelow (K := K) (Quotient.out ω).1) ⟨?_, ?_, ?_⟩
    fun ω _ => by rw [hstab]
  · intro ω _
    exact ⟨(Quotient.out ω).1, (Quotient.out ω).2, inferInstance⟩
  · intro ω₁ _ ω₂ _ h
    simp only at h
    set x₁ := Quotient.out ω₁
    set x₂ := Quotient.out ω₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L)
      (⟨x₂.1, inferInstance⟩ : SemiLocal.PlacesOver L (placeBelow (K := K) x₂.1))
      ⟨x₁.1, by rw [← h]; infer_instance⟩
    rw [← Quotient.out_eq ω₁, ← Quotient.out_eq ω₂]
    have hg' : g • x₂.1 = x₁.1 := congrArg Subtype.val hg
    exact Quotient.sound ⟨g, Subtype.ext hg'⟩
  · rintro v ⟨w, hw, hlies⟩
    refine ⟨Quotient.mk _ ⟨w, hw⟩, Set.mem_univ _, ?_⟩
    obtain ⟨g, hg⟩ : Quotient.out (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩) ∈
        orbit (L ≃ₐ[K] L) (⟨w, hw⟩ : S) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩))
    simp only
    rw [← hg]
    change placeBelow (g • w) = v
    rw [placeBelow_smul, ← eq_placeBelow_of_liesOver hlies]

end Finite

end

end GroundTheory.Global
