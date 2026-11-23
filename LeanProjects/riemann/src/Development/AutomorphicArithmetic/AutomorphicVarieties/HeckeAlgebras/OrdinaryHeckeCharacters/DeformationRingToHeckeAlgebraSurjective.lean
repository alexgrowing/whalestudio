import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.deformationRing_to_heckeAlgebra_surjective :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A T B : Type) [CommRing A] [CommRing T] [Algebra c.O T] [Algebra A T] [CommRing B] [Algebra c.O B] (gen : H.Op → T) (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ) (f : B →ₐ[c.O] T),
    (∀ (w : H.Wp) (P : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver P w.1 → IsFrob P (normV w.1) σ →
      (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    (∀ v (j : Fin n) (x : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (x : G L Ω) → H.art v x = unif _ →
      ((∏ i with i ≤ j, W.pushCh f.toRingHom (ψ₀ v i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ j : A → B, (∀ b, f (j b) = algebraMap A T b) → Algebra.adjoin A (Set.range gen) = ⊤ → Function.Surjective f := by
  intro L Ω _ _ _ _ _ l _ n c H hH A T B _ _ _ _ _ _ gen D₀ ψ₀ f h1 h2 j hj htop
  have hgen : ∀ i, gen i ∈ f.range := by
    rintro (⟨w, k⟩ | ⟨v, k⟩)
    · obtain ⟨P, hP⟩ := exists_isPlaceOver Ω w.1
      obtain ⟨σ, hσ⟩ := exists_isFrob hP
      have hq : IsUnit ((normV w.1 : ℕ) : c.O) := by
        have h0 := (cycZ L Ω l σ).isUnit.map (algebraMap ℤ_[l] c.O)
        rwa [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hP hσ, map_natCast] at h0
      obtain ⟨u, hu⟩ := hq.exists_left_inv
      have huT : algebraMap c.O T u * ((normV w.1 : ℕ) : T) = 1 := by
        rw [← map_natCast (algebraMap c.O T), ← map_mul, hu, map_one]
      have e := JEx.heckePol_coeff n (normV w.1)
        (fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) (k + 1) k.2
      rw [← h1 w P σ hP hσ, dif_pos ⟨Nat.succ_pos _, k.2⟩] at e
      have e2 : (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          (D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).map f.toRingHom := by
        rw [← (AlgebraTools.Det.mapApi D₀ _).1]
        simp
      rw [e2, coeff_map] at e
      have e3 : gen (.inl (w, k)) = algebraMap c.O T u ^ ((k + 1) * (k + 1 - 1) / 2 : ℕ) *
          ((-1) ^ ((k : ℕ) + 1) * f ((D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).coeff (n - (k + 1)))) := by
        refine Eq.trans ?_ (congrArg _ e.symm)
        rw [← mul_assoc, ← mul_pow, huT, one_pow, one_mul]
        rfl
      rw [e3]
      exact mul_mem (pow_mem (f.range.algebraMap_mem u) _)
        (mul_mem (pow_mem (neg_mem (one_mem _)) _) (f.mem_range_self _))
    · obtain ⟨y, hy⟩ := (hH.art_spec v).surj (unif _)
      rw [← h2 v k y (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) y) rfl hy, Units.coe_prod]
      refine prod_mem fun i _ => ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      exact mul_mem (f.mem_range_self _) (pow_mem (f.range.algebraMap_mem _) _)
  intro t
  have ht : t ∈ Algebra.adjoin A (Set.range gen) := htop ▸ Algebra.mem_top
  change t ∈ f.range
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | algebraMap r => exact ⟨j r, hj r⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
