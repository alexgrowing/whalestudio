import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

namespace CocCorr

variable {R : Type} [CommRing R] {I : Ideal R}

theorem mul_eq_zero_of_mem (hI : I ^ 2 = ⊥) {S : Type} [CommRing S] [Algebra R S] {x y : S}
    (hx : x ∈ I.map (algebraMap R S)) (hy : y ∈ I.map (algebraMap R S)) : x * y = 0 := by
  have h : I.map (algebraMap R S) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, h] at this
  exact (Submodule.mem_bot _).1 this

theorem map_mem {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →+* S')
    (hφ : ∀ r : R, φ (algebraMap R S r) = algebraMap R S' r) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) : φ x ∈ I.map (algebraMap R S') := by
  have h := Ideal.mem_map_of_mem φ hx
  rwa [Ideal.map_map, show φ.comp (algebraMap R S) = algebraMap R S' from RingHom.ext hφ] at h

end CocCorr

open CocCorr in
theorem cocycle_of_sqZero : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R) (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), PrimI I n₀ n₁ n₂ → ∀ (u : C1 F) (v : C0 F'), (∀ t t' a, IsUnit (u t t' a)) → In2 I F (mdef F u) → (∀ t, IsUnit (v t)) → MulRel I n₀ n₁ n₂ u v → ∃ u' : C1 F, In1 I F (u' - u) ∧ mdef F u' = 0 := by
  intro R _ I hI D T _ _ F F' n₀ n₁ n₂ hP u v hu hm hv hrel

  have hmpI : ∀ {t t' : D} (b : t ⟶ t') {x : F.obj t}, x ∈ I.map (algebraMap R (F.obj t)) →
      mp F b x ∈ I.map (algebraMap R (F.obj t')) := fun b x hx ↦
    map_mem (mp F b).toRingHom (fun r ↦ (mp F b).commutes r) hx
  have hmpI' : ∀ {t t' : T} (b : t ⟶ t') {x : F'.obj t}, x ∈ I.map (algebraMap R (F'.obj t)) →
      mp F' b x ∈ I.map (algebraMap R (F'.obj t')) := fun b x hx ↦
    map_mem (mp F' b).toRingHom (fun r ↦ (mp F' b).commutes r) hx
  have hαI : ∀ (n : CoefMap (RingHom.id R) F F') (t : T) {x : F.obj (n.G.obj t)},
      x ∈ I.map (algebraMap R (F.obj (n.G.obj t))) → n.α t x ∈ I.map (algebraMap R (F'.obj t)) := by
    intro n t x hx
    refine map_mem (n.α t) (fun r ↦ ?_) hx
    rw [Algebra.algebraMap_eq_smul_one, n.smul, map_one, RingHom.id_apply, Algebra.algebraMap_eq_smul_one]

  let z : C2 F := fun t t' t'' a b ↦ mdef F u t t' t'' a b * Ring.inverse (u t t'' (a ≫ b))
  have hzI : In2 I F z := fun t t' t'' a b ↦ Ideal.mul_mem_right _ _ (hm t t' t'' a b)
  have hz_eq : ∀ {t t' t'' : D} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F b (u t t' a) * u t' t'' b = u t t'' (a ≫ b) + u t t'' (a ≫ b) * z t t' t'' a b := by
    intro t t' t'' a b
    have h1 := Ring.mul_inverse_cancel _ (hu t t'' (a ≫ b))
    simp only [z, mdef]
    linear_combination (-(mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b))) * h1

  have hz2 : z ∈ Z2 F := by
    intro t t' t'' t''' a b c
    have e1 := congrArg (mp F c) (hz_eq a b)
    simp only [map_mul, map_add, ← mp_comp] at e1
    have e2 := hz_eq (a ≫ b) c
    have e3 := hz_eq a (b ≫ c)
    have e4 := hz_eq b c
    rw [Category.assoc] at e2
    have p1 := mul_eq_zero_of_mem hI (hmpI c (hzI _ _ _ a b)) (hzI _ _ _ (a ≫ b) c)
    have p2 := mul_eq_zero_of_mem hI (hzI _ _ _ a (b ≫ c)) (hzI _ _ _ b c)
    have hU : u t t''' (a ≫ b ≫ c) * (mp F c (z t t' t'' a b) + z t t'' t''' (a ≫ b) c
        - z t t' t''' a (b ≫ c) - z t' t'' t''' b c) = 0 := by
      linear_combination (-(u t'' t''' c)) * e1 - (1 + mp F c (z t t' t'' a b)) * e2
        + (1 + z t' t'' t''' b c) * e3 + mp F (b ≫ c) (u t t' a) * e4
        - u t t''' (a ≫ b ≫ c) * p1 + u t t''' (a ≫ b ≫ c) * p2
    have := ((hu _ _ _).mul_right_eq_zero).1 hU
    linear_combination this

  let U : CoefMap (RingHom.id R) F F' → C1 F' := fun n t t' a ↦ n.α t' (u _ _ (n.G.map a))
  let W : C1 F' := fun t t' a ↦ U n₁ t t' a * U n₂ t t' a * mp F' a (v t)
  let f : C1 F' := fun t t' a ↦ (U n₀ t t' a * v t' - W t t' a) * Ring.inverse (W t t' a)
  have hUu : ∀ n t t' a, IsUnit (U n t t' a) := fun n t t' a ↦ (hu _ _ _).map (n.α t')
  have hWu : ∀ t t' a, IsUnit (W t t' a) := fun t t' a ↦
    ((hUu n₁ t t' a).mul (hUu n₂ t t' a)).mul ((hv t).map (mp F' a))
  have hfI : In1 I F' f := fun t t' a ↦ Ideal.mul_mem_right _ _ (hrel t t' a)
  have hf_eq : ∀ {t t' : T} (a : t ⟶ t'), U n₀ t t' a * v t' =
      U n₁ t t' a * U n₂ t t' a * mp F' a (v t) + U n₁ t t' a * U n₂ t t' a * mp F' a (v t) * f t t' a := by
    intro t t' a
    have h1 := Ring.mul_inverse_cancel _ (hWu t t' a)
    simp only [f]
    linear_combination (-(U n₀ t t' a * v t' - W t t' a)) * h1
  have hUeq : ∀ (n : CoefMap (RingHom.id R) F F') {t t' t'' : T} (a : t ⟶ t') (b : t' ⟶ t''),
      mp F' b (U n t t' a) * U n t' t'' b = U n t t'' (a ≫ b) +
        U n t t'' (a ≫ b) * n.α t'' (z _ _ _ (n.G.map a) (n.G.map b)) := by
    intro n t t' t'' a b
    have h := congrArg (n.α t'') (hz_eq (n.G.map a) (n.G.map b))
    simp only [map_mul, map_add, n.naturality, ← Functor.map_comp] at h
    exact h
  have hd : d1 F' f = (n₀.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₁.pullbackTwoCocycle ⟨z, hz2⟩).1 - (n₂.pullbackTwoCocycle ⟨z, hz2⟩).1 := by
    funext t t' t'' a b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply]
    have ra := congrArg (mp F' b) (hf_eq a)
    simp only [map_mul, map_add, ← mp_comp] at ra
    have rb := hf_eq b
    have rab := hf_eq (a ≫ b)
    have h0 := hUeq n₀ a b
    have h1 := hUeq n₁ a b
    have h2 := hUeq n₂ a b
    set a0 := mp F' b (U n₀ t t' a)
    set a1 := mp F' b (U n₁ t t' a)
    set a2 := mp F' b (U n₂ t t' a)
    set b0 := U n₀ t' t'' b
    set b1 := U n₁ t' t'' b
    set b2 := U n₂ t' t'' b
    set c0 := U n₀ t t'' (a ≫ b)
    set c1 := U n₁ t t'' (a ≫ b)
    set c2 := U n₂ t t'' (a ≫ b)
    set V := mp F' (a ≫ b) (v t)
    set V' := mp F' b (v t')
    set V'' := v t''
    set F1 := mp F' b (f t t' a)
    set F2 := f t' t'' b
    set F3 := f t t'' (a ≫ b)
    set Z0 := n₀.α t'' (z _ _ _ (n₀.G.map a) (n₀.G.map b))
    set Z1 := n₁.α t'' (z _ _ _ (n₁.G.map a) (n₁.G.map b))
    set Z2' := n₂.α t'' (z _ _ _ (n₂.G.map a) (n₂.G.map b))
    have indexFFirst : F1 ∈ I.map (algebraMap R (F'.obj t'')) := hmpI' b (hfI _ _ a)
    have indexFSecond : F2 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ b
    have indexFThird : F3 ∈ I.map (algebraMap R (F'.obj t'')) := hfI _ _ (a ≫ b)
    have iZ0 : Z0 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₀ t'' (hzI _ _ _ _ _)
    have iZ1 : Z1 ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₁ t'' (hzI _ _ _ _ _)
    have iZ2 : Z2' ∈ I.map (algebraMap R (F'.obj t'')) := hαI n₂ t'' (hzI _ _ _ _ _)
    have hT : c1 * c2 * V * V' * ((1 + Z1) * (1 + Z2') * (1 + F1) * (1 + F2) - (1 + F3) * (1 + Z0)) = 0 := by
      linear_combination (-(a1 * a2 * V * (1 + F1))) * rb - b0 * V'' * ra
        - V * V' * (1 + F1) * (1 + F2) * (c1 * (1 + Z1) * h2 + a2 * b2 * h1) + (1 + Z0) * V' * rab + V' * V'' * h0
    have hK : IsUnit (c1 * c2 * V * V') :=
      (((hUu n₁ _ _ _).mul (hUu n₂ _ _ _)).mul ((hv t).map _)).mul ((hv t').map _)
    have hX := (hK.mul_right_eq_zero).1 hT
    linear_combination hX - (1 + F1 + F2 + F1 * F2) * mul_eq_zero_of_mem hI iZ1 iZ2
      - (1 + F2) * mul_eq_zero_of_mem hI iZ1 indexFFirst - mul_eq_zero_of_mem hI iZ1 indexFSecond
      - (1 + F2) * mul_eq_zero_of_mem hI iZ2 indexFFirst - mul_eq_zero_of_mem hI iZ2 indexFSecond
      - mul_eq_zero_of_mem hI indexFFirst indexFSecond + mul_eq_zero_of_mem hI indexFThird iZ0

  obtain ⟨f₀, hf₀I, hf₀⟩ := hP ⟨z, hz2⟩ f hzI hfI hd
  refine ⟨fun t t' a ↦ u t t' a * (1 - f₀ t t' a), fun t t' a ↦ ?_, ?_⟩
  · simp only [Pi.sub_apply]
    rw [show u t t' a * (1 - f₀ t t' a) - u t t' a = -(u t t' a * f₀ t t' a) by ring]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hf₀I t t' a))
  · funext t t' t'' a b
    simp only [mdef, Pi.zero_apply, map_mul, map_sub, map_one]
    have e := hz_eq a b
    have ed := congrFun (congrFun (congrFun (congrFun (congrFun hf₀ t) t') t'') a) b
    rw [d1_apply] at ed
    have iF := hmpI b (hf₀I t t' a)
    have iG := hf₀I t' t'' b
    have iz := hzI t t' t'' a b
    linear_combination (1 - mp F b (f₀ t t' a)) * (1 - f₀ t' t'' b) * e - u t t'' (a ≫ b) * ed
      + u t t'' (a ≫ b) * (1 + z t t' t'' a b) * mul_eq_zero_of_mem hI iF iG
      - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iF - u t t'' (a ≫ b) * mul_eq_zero_of_mem hI iz iG

end GlobalTheory.LBLift
