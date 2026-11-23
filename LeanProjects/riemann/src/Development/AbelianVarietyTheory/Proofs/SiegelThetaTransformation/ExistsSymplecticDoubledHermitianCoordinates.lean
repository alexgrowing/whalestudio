import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem cc_cc (a : E) : cc (cc a) = a := by
  unfold cc
  exact IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a := by
  unfold cc
  exact Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem sum_trace {ι : Type} [Fintype ι] (B : Module.Basis ι ℚ E) (b d : E) :
    ∑ j, Algebra.trace ℚ E (b * cc (B j)) * B.repr d j = Algebra.trace ℚ E (b * cc d) := by

  have hd : cc d = ∑ j, B.repr d j • cc (B j) := by
    conv_lhs => rw [← B.sum_repr d]
    unfold cc
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_rat_smul _ _ _
  rw [hd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

theorem vec_inl (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = y₁ a - y₂ a := by
  simp [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

theorem vec_inr (y₁ y₂ : Fin r → E) (a : Fin r) :
    (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) = X.κ0 / 4 * ∑ c, (y₁ c + y₂ c) * X.Gm c a := by
  simp only [dblT, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem split_form (y₁ y₂ z₁ z₂ : Fin r → E) :
    ∑ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inl a)) -
      ∑ a, cc ((Sum.elim z₁ z₂ ᵥ* dblT X) (Sum.inr a)) * (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) =
      -(X.κ0 / 2) * herm X.Gm y₂ z₂ - -(X.κ0 / 2) * herm X.Gm y₁ z₁ := by

  have hadd : ∀ a b : E, cc (a + b) = cc a + cc b := fun a b => by unfold cc; exact map_add _ a b
  have hsub : ∀ a b : E, cc (a - b) = cc a - cc b := fun a b => by unfold cc; exact map_sub _ a b
  have hsum : ∀ f : Fin r → E, cc (∑ c, f c) = ∑ c, cc (f c) := fun f => by
    unfold cc; exact map_sum _ _ _
  have hk : cc (X.κ0 / 4) = -(X.κ0 / 4) := by
    have h4 : cc (4 : E) = 4 := by unfold cc; exact map_ofNat _ 4
    have hd : cc (X.κ0 / 4) = cc X.κ0 / cc 4 := by unfold cc; exact map_div₀ _ _ _
    rw [hd, h4, DblPer.cc_kappa X, neg_div]
  simp only [vec_inl, vec_inr, cc_mul, hadd, hsub, hsum, hk, X.Gm_herm, herm]
  simp only [Finset.mul_sum, Finset.sum_mul]

  conv_lhs => arg 1; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

variable (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

noncomputable def dv (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) : Fin r ⊕ Fin r → E :=
  Sum.elim (vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)))
    (vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)))) ᵥ* dblT X

theorem dv_add (u v) : dv X bas (u + v) = dv X bas u + dv X bas v := by
  have h₁ : Sum.elim ((u + v).1 ∘ Sum.inl) ((u + v).2 ∘ Sum.inl) =
      Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) + Sum.elim (v.1 ∘ Sum.inl) (v.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((u + v).1 ∘ Sum.inr) (-((u + v).2 ∘ Sum.inr)) =
      Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) + Sum.elim (v.1 ∘ Sum.inr) (-(v.2 ∘ Sum.inr)) := by
    ext (i | i)
    · rfl
    · simp only [Sum.elim_inr, Pi.neg_apply, Function.comp_apply, Prod.snd_add, Pi.add_apply]
      ring
  unfold dv
  rw [h₁, h₂, vecQ_add, vecQ_add, ← Matrix.add_vecMul, Sum.elim_add_add]

theorem dv_smul (q : ℚ) (u) : dv X bas (q • u) = q • dv X bas u := by
  have h₁ : Sum.elim ((q • u).1 ∘ Sum.inl) ((q • u).2 ∘ Sum.inl) =
      q • Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl) := by
    ext (i | i) <;> rfl
  have h₂ : Sum.elim ((q • u).1 ∘ Sum.inr) (-((q • u).2 ∘ Sum.inr)) =
      q • Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr)) := by
    ext (i | i) <;> simp
  have h₃ : ∀ f g' : Fin r → E, Sum.elim (q • f) (q • g') = q • Sum.elim f g' := fun f g' => by
    ext (i | i) <;> rfl
  unfold dv
  rw [h₁, h₂, vecQ_smul, vecQ_smul, h₃, Matrix.smul_vecMul]

noncomputable def crdMap : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ]
    ((QI E r → ℚ) × (QI E r → ℚ)) where
  toFun u := (fun p => Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)),
    fun p => (Module.finBasis ℚ E).repr (dv X bas u (Sum.inl p.1)) p.2)
  map_add' u v := by
    ext p <;> simp [dv_add, add_mul]
  map_smul' q u := by
    ext p <;> simp [dv_smul]

theorem crdMap_pair (u v) : (crdMap X bas u).1 ⬝ᵥ (crdMap X bas v).2 =
    Algebra.trace ℚ E (∑ a, dv X bas u (Sum.inr a) * cc (dv X bas v (Sum.inl a))) := by
  have e₁ : ∀ p : QI E r, (crdMap X bas u).1 p =
      Algebra.trace ℚ E (dv X bas u (Sum.inr p.1) * cc (Module.finBasis ℚ E p.2)) := fun p => rfl
  have e₂ : ∀ p : QI E r, (crdMap X bas v).2 p =
      (Module.finBasis ℚ E).repr (dv X bas v (Sum.inl p.1)) p.2 := fun p => rfl
  simp only [dotProduct, e₁, e₂]
  rw [Fintype.sum_prod_type, map_sum (Algebra.trace ℚ E)]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  rw [sum_trace (Module.finBasis ℚ E) (dv X bas u (Sum.inr a)) (dv X bas v (Sum.inl a))]

theorem dbl_lat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ), IsSympl X bas → ∃ F : ((Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) →ₗ[ℚ] ((QI E r → ℚ) × (QI E r → ℚ)), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) ∧ ∀ (u : (Fin g ⊕ Fin g → ℚ) × (Fin g ⊕ Fin g → ℚ)) (y₁ y₂ : Fin r → E), y₁ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inl) (u.2 ∘ Sum.inl)) → y₂ = vecQ X bas (Sum.elim (u.1 ∘ Sum.inr) (-(u.2 ∘ Sum.inr))) → (∀ a, (Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inl a) = ∑ j, (F u).2 (a, j) • Module.finBasis ℚ E j) ∧ ∀ a j, (F u).1 (a, j) = Algebra.trace ℚ E ((Sum.elim y₁ y₂ ᵥ* dblT X) (Sum.inr a) * cc (Module.finBasis ℚ E j)) := by
  intro E _ _ _ r X g bas hs
  refine ⟨crdMap X bas, fun u v => ?_, fun u y₁ y₂ h₁ h₂ => ?_⟩
  ·
    have hsum : ∀ f : Fin r → E, cc (∑ a, f a) = ∑ a, cc (f a) := fun f => by
      unfold cc; exact map_sum _ _ _
    have hsw : (crdMap X bas u).2 ⬝ᵥ (crdMap X bas v).1 =
        Algebra.trace ℚ E (∑ a, cc (dv X bas v (Sum.inr a)) * dv X bas u (Sum.inl a)) := by
      rw [dotProduct_comm, crdMap_pair, ← trace_cc, hsum]
      simp only [cc_mul, cc_cc]
    rw [crdMap_pair, hsw, ← map_sub]
    unfold dv
    rw [split_form, map_sub, ← EF_def, ← EF_def, EF_vecQ hs, EF_vecQ hs]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
      Pi.neg_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_neg, neg_mul]
    ring
  · subst h₁ h₂
    exact ⟨fun a => ((Module.finBasis ℚ E).sum_repr _).symm, fun a j => rfl⟩

end GlobalTheory.SW.DblLat
