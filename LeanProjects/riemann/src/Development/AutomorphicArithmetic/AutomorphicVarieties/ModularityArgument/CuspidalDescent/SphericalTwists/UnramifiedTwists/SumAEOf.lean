import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.RowProps
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Desc.W

section Coeff

variable {T R : Type} [TopologicalSpace T] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

private theorem cc_prod {I : Type} (s : Finset I) (f : I → T → R[X]) (h : ∀ i j, Continuous fun t => (f i t).coeff j) :
    ∀ j, Continuous fun t => (∏ i ∈ s, f i t).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty => intro j; simpa using continuous_const
  | insert i s hi ih =>
    intro j
    simp only [Finset.prod_insert hi, coeff_mul]
    exact continuous_finset_sum _ fun x _ => (h i _).mul (ih _)

private theorem cc_charpoly {a : ℕ} (M : T → Matrix (Fin a) (Fin a) R) (hM : Continuous M) (j : ℕ) :
    Continuous fun t => (M t).charpoly.coeff j := by
  simp only [Matrix.charpoly, Matrix.det_apply, finset_sum_coeff, coeff_smul]
  refine continuous_finset_sum _ fun σ _ => ?_
  have h := cc_prod Finset.univ (fun i t => (M t).charmatrix (σ i) i) (fun i k => by
    simp only [Matrix.charmatrix_apply, coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact hM.matrix_elem _ _
    · exact continuous_const) j
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e
  · simpa [e] using h
  · simpa [e] using continuous_neg.comp' h

end Coeff

private theorem algSat_eq' (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton]

private theorem prod_algSat_sum (n q : ℕ) {I : Type} (s : Finset I) (B : I → Multiset ℂˣ) :
    ((algSat n q (∑ i ∈ s, B i)).map fun b => X - C b).prod = ∏ i ∈ s, ((algSat n q (B i)).map fun b => X - C b).prod := by
  classical
  simp only [algSat_eq']
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add, Multiset.map_add, Multiset.prod_add, ih]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a n : ℕ) (s t : ℝ)
    (h : ((a : ℝ) - 1) / 2 + -s = ((n : ℝ) - 1) / 2 + t) (B : Multiset ℂˣ) :
    algSat a (normV w) (B.map (· * qPow w (-s))) = algSat n (normV w) (B.map (· * qPow w t)) := by
  have key : ∀ x : ℝ, ((((normV w : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (qPow w x : ℂ) := fun x => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), coe_qPow, Complex.ofReal_natCast]
  simp only [algSat_eq', Multiset.map_map, key]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply]
  rw [← Units.val_mul, ← Units.val_mul, mul_left_comm, ← qPow_add, h, qPow_add, mul_left_comm]

theorem UpperTheory.V.Z.Desc.W.sumAEOf :
    UpperTheory.V.Z.Desc.W.SumAEOf := by
  intro hTw hG E Ω _ _ _ _ _ _ l _ ι n c a d P m ha hP hm he
  let s : (i : Fin c) → Fin (d i) → ℝ := fun i k => ((ex n (d i) k + a i - 1 : ℤ) : ℝ) / 2
  have hreg : ∀ i k, (CG.mk ((P i).twist (GlobalTheory.HeckeGal.Model.absPow E (s i k)))).IsRegAlg := fun i k => (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have hsC : (s i k : ℂ) = (ex n (d i) k : ℂ) / 2 + ((a i : ℂ) - 1) / 2 := by
      simp only [s]; push_cast; ring
    have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (s i k)
    have h1 := (hm i τ).twist (GlobalTheory.HeckeGal.Model.absPow E (s i k))
    rw [(InfType.expo_of_infType E _).2.1 (s i k) hν τ] at h1
    rw [CG.HasInfChar.infChar_eq (π := CG.mk _) h1]
    refine ⟨(he i k τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he i k τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  choose r hc hr using fun i k => hG E Ω l ι (a i) (ha i) (P i) (hP i) (s i k) (hreg i k)
  refine ⟨fun g => ∏ i, ∏ k, (r i k g⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly, ?_, ?_⟩
  · exact cc_prod _ _ fun i => cc_prod _ _ fun k =>
      cc_charpoly _ (Units.continuous_val.comp ((hc i k).comp continuous_inv))
  · intro w hw S hS A hA σ hσ
    have key : ∀ i k, (r i k σ⁻¹ : Matrix (Fin (a i)) (Fin (a i)) (Qbar l)).charpoly.map ι.toRingHom =
        ((algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2)))).map fun b => X - C b).prod := by
      intro i k
      rw [hr i k w hw _ (hTw E (a i) (P i) (s i k) w (S i) (hS i)) A hA σ hσ, algSat_shift w (a i) n (s i k)]
      simp only [s, ex]; push_cast; ring
    simp only [Polynomial.map_prod, key, satTot, prod_algSat_sum]
