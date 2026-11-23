import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AlgebraMapAEInjective

noncomputable section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem free_etale_sheaf_zmod_exists_hom_sending_generator (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (hε : ε * ε = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : IsUnit X.det) (e : AF F) (he : e * e = e)
    (heA : e • X.toBlocks₁₁ = e • (1 : Matrix (Fin n) (Fin n) (AE F E))) :
    ∃ t : Matrix (Fin n) (Fin n) (AE F E), tᵀ + ((ε : ℤ) : AE F E) • t.map (cA σ) = 0 ∧ e • t = 0 ∧
      IsUnit (X.toBlocks₁₁ - t * X.toBlocks₂₁).det := by
  classical
  set A := X.toBlocks₁₁ with hA
  set C := X.toBlocks₂₁ with hC
  have h1 : (1 : AF F) ∈ Submodule.span (AF F) {a : AF F | ∃ g, IsEH σ ε g ∧ algebraMap (AF F) (AE F E) a =
      (A - incM F g * C).det * cA σ (A - incM F g * C).det} := by
    have := span_top' hcm ε hε X hX
    change (1 : AF F) ∈ Ideal.span _
    rw [this]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hT
  have hg : ∀ i : T, ∃ g, IsEH σ ε g ∧ algebraMap (AF F) (AE F E) i.1 =
      (A - incM F g * C).det * cA σ (A - incM F g * C).det := fun i => hTS i.2
  choose g hgE hgN using hg
  obtain ⟨η, hηi, hηo, hη1, hηu⟩ := GlobalTheory.QSA.exists_idem_pick_unit F T (fun i => i.1) (fun i => f i.1) (by
    have : ∑ i : T, f i.1 * i.1 = 1 := by
      rw [← hf, ← Finset.sum_coe_sort T]; rfl
    rw [this]; exact isUnit_one)
  set t : Matrix (Fin n) (Fin n) (AE F E) := (1 - e) • ∑ i, η i • incM F (g i) with ht
  have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  refine ⟨t, ?_, ?_, ?_⟩
  · exact qs_smul ε _ (qs_sum ε _ _ fun i _ => qs_smul ε _ (qs_incM ε (hgE i)))
  · rw [ht, smul_smul, hee, zero_smul]
  · set ae := algebraMap (AF F) (AE F E) with hae
    let fo : Option T → AF F := fun o => o.elim e (fun i => (1 - e) * η i)
    let Mo : Option T → Matrix (Fin n) (Fin n) (AE F E) := fun o => o.elim A (fun i => A - incM F (g i) * C)
    have h1e : (1 - e) * (1 - e) = 1 - e := by
      rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
    have hfi : ∀ o, fo o * fo o = fo o := by
      rintro (_ | i)
      · exact he
      · change (1 - e) * η i * ((1 - e) * η i) = (1 - e) * η i
        calc _ = ((1 - e) * (1 - e)) * (η i * η i) := by ring
          _ = _ := by rw [h1e, hηi]
    have hfo : ∀ o o', o ≠ o' → fo o * fo o' = 0 := by
      rintro (_ | i) (_ | j) h
      · exact absurd rfl h
      · change e * ((1 - e) * η j) = 0
        rw [← mul_assoc, hee, zero_mul]
      · change (1 - e) * η i * e = 0
        rw [mul_comm, ← mul_assoc, hee, zero_mul]
      · change (1 - e) * η i * ((1 - e) * η j) = 0
        have hij : i ≠ j := fun h' => h (by rw [h'])
        calc _ = (1 - e) * (1 - e) * (η i * η j) := by ring
          _ = 0 := by rw [hηo i j hij, mul_zero]
    have hf1 : ∑ o, fo o = 1 := by
      rw [Fintype.sum_option]
      change e + ∑ i, (1 - e) * η i = 1
      rw [← Finset.mul_sum, hη1, mul_one, add_sub_cancel]
    have htC : t * C = ∑ i, ((1 - e) * η i) • (incM F (g i) * C) := by
      rw [ht, Matrix.smul_mul, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mul, smul_smul]
    have hsum : A - t * C = ∑ o, (ae (fo o)) • Mo o := by
      simp only [hae, algebraMap_smul]
      rw [Fintype.sum_option, htC]
      change A - _ = e • A + ∑ i, ((1 - e) * η i) • (A - incM F (g i) * C)
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.mul_sum, hη1, mul_one]
      rw [sub_smul, one_smul]
      abel
    have hdet := det_idem_sum (fun o => ae (fo o)) (fun o => by rw [← map_mul, hfi]) (fun o o' h => by
      rw [← map_mul, hfo o o' h, map_zero]) (by rw [← map_sum, hf1, map_one]) Mo
    rw [← hsum, Fintype.sum_option] at hdet
    have hAeq : A = ∑ b : Bool, (ae (if b then e else 1 - e)) • (if b then (1 : Matrix (Fin n) (Fin n) (AE F E)) else A) := by
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, hae, algebraMap_smul]
      rw [← heA, sub_smul, one_smul, add_sub_cancel]
    have hA2 := det_idem_sum (fun b : Bool => ae (if b then e else 1 - e)) (fun b => by
      rw [← map_mul]; cases b <;> simp [he, h1e]) (fun b b' h => by
      rw [← map_mul]
      cases b <;> cases b'
      · exact absurd rfl h
      · simp only [if_true, Bool.false_eq_true, if_false]; rw [mul_comm, hee, map_zero]
      · simp only [if_true, Bool.false_eq_true, if_false]; rw [hee, map_zero]
      · exact absurd rfl h) (by
      rw [Fintype.sum_bool]; simp) (fun b => if b then (1 : Matrix (Fin n) (Fin n) (AE F E)) else A)
    rw [← hAeq, Fintype.sum_bool] at hA2
    simp only [if_true, Bool.false_eq_true, if_false, Matrix.det_one, mul_one] at hA2
    have heA' : ae e * A.det = ae e := by
      calc ae e * A.det = ae e * (ae e + ae (1 - e) * A.det) := by rw [← hA2]
        _ = ae (e * e) + ae (e * (1 - e)) * A.det := by rw [map_mul, map_mul]; ring
        _ = ae e := by rw [he, hee, map_zero, zero_mul, add_zero]
    set zs := ∑ i, ae (η i) * (A - incM F (g i) * C).det with hzs
    have hcz : cA σ zs = ∑ i, ae (η i) * cA σ (A - incM F (g i) * C).det := by
      rw [hzs, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hae, AlgHom.commutes]
    have hzz : zs * cA σ zs = ae (∑ i, η i * i.1) := by
      rw [hcz, hzs, sum_idem_mul (fun i => ae (η i)) (fun i => by rw [← map_mul, hηi]) (fun i j h => by
        rw [← map_mul, hηo i j h, map_zero]), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hgN i]
    have hzu : IsUnit zs := isUnit_of_mul_isUnit_left (hzz ▸ hηu.map ae)
    have hfin : (A - t * C).det = ae e + ae (1 - e) * zs := by
      rw [hdet]
      change ae e * A.det + ∑ i, ae ((1 - e) * η i) * (A - incM F (g i) * C).det = _
      rw [heA', hzs, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      change ae ((1 - e) * η i) * _ = _
      rw [map_mul, mul_assoc]
    rw [hfin]
    obtain ⟨u, hu⟩ := hzu
    refine isUnit_iff_exists_inv.2 ⟨ae e + ae (1 - e) * ↑u⁻¹, ?_⟩
    have h1 : ae e * ae e = ae e := by rw [← map_mul, he]
    have h2 : zs * ↑u⁻¹ = 1 := by rw [← hu, Units.mul_inv]
    rw [map_sub, map_one]
    rw [map_sub, map_one] at *
    linear_combination (2 - ↑u⁻¹ - zs + (zs * ↑u⁻¹ - 1)) * h1 + (1 - ae e) * h2

end PositivityTheory.SiegelWeilFormula.KAway

end
