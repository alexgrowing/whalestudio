import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.SumSumProd

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.Coch

open PositivityTheory.Rg.Cz

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def ent (τ : E →+* ℂ) (i j : Fin a) : Herm E a →ₗ[ℝ] ℂ where
  toFun X := coord τ (X.1 i j)
  map_add' X Y := by simp
  map_smul' c X := (coordL τ).map_smul c (X.1 i j)

theorem ent_apply (τ : E →+* ℂ) (i j : Fin a) (X : Herm E a) : ent τ i j X = coord τ (X.1 i j) := rfl

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {q N : ℕ}

def vec (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (I' I'' : Fin N → Fin a) : TV a M (Fin q) :=
  fun I => η (Sum.elim I (Sum.elim I' I''))

def mm (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) :
    MultilinearMap ℝ (fun _ : Fin N => Herm E a) (TV a M (Fin q)) :=
  ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a,
    ((LinearMap.toSpanSingleton ℂ _ (vec η I' I'')).restrictScalars ℝ).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ (Fin N) ℂ).compLinearMap fun k => ent (tl k) (I'' k) (I' k))

theorem mm_apply (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (X : Fin N → Herm E a)
    (I : Fin q → Fin a) : mm tl η X I = ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a,
      (∏ k, coord (tl k) ((X k).1 (I'' k) (I' k))) • η (Sum.elim I (Sum.elim I' I'')) := by
  simp [mm, Finset.sum_apply, vec, ent_apply]

def om (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) : Herm E a [⋀^Fin N]→ₗ[ℝ] TV a M (Fin q) :=
  MultilinearMap.alternatization (mm tl η)

theorem om_apply (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (X : Fin N → Herm E a)
    (I : Fin q → Fin a) :
    om tl η X I = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ)) • mm tl η (fun i => X (σ i)) I := by
  rw [om, MultilinearMap.alternatization_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, Units.smul_def, MultilinearMap.domDomCongr_apply]

theorem om_swap (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N))) (p p' : Fin q)
    (h : pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η) (X : Fin N → Herm E a) :
    pm (Equiv.swap p p') (om tl η X) = -om tl η X := by
  funext I
  rw [pm_apply, Pi.neg_apply, om_apply, om_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← smul_neg, mm_apply, mm_apply, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun I'' _ => ?_
  rw [← smul_neg]
  congr 1
  have e : Sum.elim (I ∘ Equiv.swap p p') (Sum.elim I' I'') =
      Sum.elim I (Sum.elim I' I'') ∘ Equiv.swap (Sum.inl p) (Sum.inl p') := by
    funext x
    rcases x with x | x
    · simp [Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · simp [Equiv.swap_apply_def]
  rw [e]
  exact congrFun h _

theorem intersection_update_fsHerm_neg_one (τ : E →+* ℂ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) (a' b : Fin a) :
    ∑ x, ∑ y, coord τ ((k.1 * X * star k.1) y x) * kap E a τ k x b * star (kap E a τ k y a') = coord τ (X a' b) := by
  set U := kap E a τ k with hUdef
  have hs : (star k.1).map (coord τ) = Uᴴ := by
    ext i j
    simp [U, kap, Matrix.star_apply, Matrix.conjTranspose_apply, J.coord_star]
  have hU : Uᴴ * U = 1 := by
    have h1 : star k.1 * k.1 = 1 := Matrix.UnitaryGroup.star_mul_self k
    have h2 := congrArg (fun m => m.map (coord τ)) h1
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    rw [hs] at h2
    exact h2
  have hm : (k.1 * X * star k.1).map (coord τ) = U * X.map (coord τ) * Uᴴ := by
    rw [Matrix.map_mul, Matrix.map_mul, hs]
    rfl
  have hc : ∀ y x, coord τ ((k.1 * X * star k.1) y x) = (U * X.map (coord τ) * Uᴴ) y x := fun y x => by
    rw [← hm]; rfl
  simp_rw [hc]
  have key : (Uᴴ * (U * X.map (coord τ) * Uᴴ) * U) a' b = coord τ (X a' b) := by
    rw [show Uᴴ * (U * X.map (coord τ) * Uᴴ) * U = (Uᴴ * U) * X.map (coord τ) * (Uᴴ * U) by
      simp only [Matrix.mul_assoc], hU, Matrix.one_mul, Matrix.mul_one, Matrix.map_apply]
  rw [← key]
  generalize U * X.map (coord τ) * Uᴴ = Z
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem kap_bar [IsTotallyComplex E] (τ : E →+* ℂ) (k : Kinf E a) (x y : Fin a) :
    kap E a (barE E τ) k x y = star (kap E a τ k x y) := by
  simp only [kap, Matrix.map_apply]
  exact J.coord_conjugate τ _

theorem eta_expand [IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ)) (ρ : Kinf E a → Module.End ℂ M)
    (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) (k : Kinf E a) (I : Fin q → Fin a) (I' I'' : Fin N → Fin a) :
    η (Sum.elim I (Sum.elim I' I'')) = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
      ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
        ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j)))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
  conv_lhs => rw [← h2 k]
  rw [actT_apply]
  let e : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)) ≃ (Fin q ⊕ (Fin N ⊕ Fin N) → Fin a) :=
    (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ _).symm).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
  refine (Fintype.sum_equiv e _ _ (fun w => ?_)).symm
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [lab3, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, kap_bar]
  rfl

theorem coef_id (tl : Fin N → (E →+* ℂ)) (k : Kinf E a) (Y : Fin N → Herm E a) (K : ℂ) (A' B' : Fin N → Fin a) :
    ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
      (K * ((∏ j, kap E a (tl j) k (I' j) (B' j)) * ∏ j, star (kap E a (tl j) k (I'' j) (A' j)))) =
      K * ∏ j, coord (tl j) ((Y j).1 (A' j) (B' j)) := by
  have h : ∀ I' I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
      (K * ((∏ j, kap E a (tl j) k (I' j) (B' j)) * ∏ j, star (kap E a (tl j) k (I'' j) (A' j)))) =
      K * ∏ j, (coord (tl j) ((k.1 * (Y j).1 * star k.1) (I'' j) (I' j)) * kap E a (tl j) k (I' j) (B' j) *
        star (kap E a (tl j) k (I'' j) (A' j))) := by
    intro I' I''
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [adHerm]
    ring
  simp_rw [h, ← Finset.mul_sum]
  congr 1
  rw [sum_sum_prod (fun j x y => coord (tl j) ((k.1 * (Y j).1 * star k.1) y x) * kap E a (tl j) k x (B' j) *
    star (kap E a (tl j) k y (A' j)))]
  exact Finset.prod_congr rfl fun j _ => intersection_update_fsHerm_neg_one (tl j) k (Y j).1 (A' j) (B' j)

theorem mm_equiv [IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ)) (ρ : Kinf E a → Module.End ℂ M)
    (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) (k : Kinf E a) (Y : Fin N → Herm E a) :
    mm tl η (fun i => adHerm k (Y i)) = actT lab (kap E a) ρ k (mm tl η Y) := by
  funext I
  rw [mm_apply, actT_apply]
  calc _ = ∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        ((∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
          ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
            ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j))))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun I'' _ => ?_
        rw [eta_expand lab tl ρ η h2 k I I' I'', Finset.smul_sum]
        simp_rw [smul_smul]
    _ = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        (∑ I' : Fin N → Fin a, ∑ I'' : Fin N → Fin a, (∏ j, coord (tl j) ((adHerm k (Y j)).1 (I'' j) (I' j))) *
          ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ((∏ j, kap E a (tl j) k (I' j) (w.2.1 j)) *
            ∏ j, star (kap E a (tl j) k (I'' j) (w.2.2 j))))) • ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        simp_rw [Finset.sum_smul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun I' _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ w : (Fin q → Fin a) × ((Fin N → Fin a) × (Fin N → Fin a)),
        ((∏ p, kap E a (lab p) k (I p) (w.1 p)) * ∏ j, coord (tl j) ((Y j).1 (w.2.2 j) (w.2.1 j))) •
          ρ k (η (Sum.elim w.1 (Sum.elim w.2.1 w.2.2))) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [coef_id]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J1 _ => ?_
        rw [mm_apply, map_sum, Finset.smul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun B' _ => ?_
        rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun A' _ => ?_
        rw [map_smul, smul_smul]

theorem om_cochain [IsTotallyComplex E] (lab : Fin q → (E →+* ℂ)) (tl : Fin N → (E →+* ℂ))
    (ρ : Kinf E a → Module.End ℂ M) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h2 : ∀ γ, actT (lab3 (barE E) lab tl) (kap E a) ρ γ η = η) :
    IsCochain (actT lab (kap E a) ρ) (om tl η) := by
  intro k X
  rw [om, MultilinearMap.alternatization_apply, MultilinearMap.alternatization_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, MultilinearMap.domDomCongr_apply, MultilinearMap.domDomCongr_apply]
  congr 1
  exact mm_equiv lab tl ρ η h2 k (fun i => X (σ i))

end PositivityTheory.Rg.Cz.Coch

end
