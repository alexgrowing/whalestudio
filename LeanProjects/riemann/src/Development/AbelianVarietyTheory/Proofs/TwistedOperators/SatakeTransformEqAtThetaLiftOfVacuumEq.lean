import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelMultiplicativeEqProdDiagonalValuationsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelatiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelInvariantFormUpperTriangularPairActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedModelSelfDualLatticeInvariantLinearFoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedFormTorusTranslateVacuumValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentativesStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem prodId1 : ∀ (n : ℕ) (qu : ℂˣ) (Y : ℂ), Y ≠ 0 → ∀ (α : Fin (n / 2) → ℂˣ) (d : Fin (n / 2) → ℤ), (∏ k, Y ^ d k) * ∏ r : Fin (n / 2), (Y * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ (-d r.rev) = ∏ k, ((α k : ℂ) * (qu : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n qu Y hY α d
  have hq := qu.ne_zero
  have hα : ∀ k, (α k : ℂ) ≠ 0 := fun k => (α k).ne_zero
  rw [← Equiv.prod_comp Fin.revPerm]
  conv_rhs => rw [← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.zpow_neg, ← div_eq_mul_inv, ← div_zpow]
  congr 1
  have e : ((n / 2 : ℕ) : ℤ) - 1 - ((k : ℕ) : ℤ) = ((k.rev : ℕ) : ℤ) := by
    have := k.isLt
    rw [Fin.val_rev]; omega
  rw [e, _root_.zpow_neg]
  have := hα k.rev
  have := zpow_ne_zero ((n : ℤ) - 1 - 2 * ((k.rev : ℕ) : ℤ)) hq
  field_simp

theorem prodId2 : ∀ (n n' : ℕ) (hn : n ≤ n') (qu : ℂˣ) (α : Fin (n / 2) → ℂˣ) (d : Fin (n' / 2) → ℤ), (∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ d k) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d ⟨n' / 2 - n / 2 + r.1, by omega⟩ = ∏ k, ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n n' hn qu α d
  have hq := qu.ne_zero
  have hfac : ∀ k : Fin (n' / 2), ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) =
      ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) * (if h : n' / 2 - n / 2 ≤ k.1 then
        ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ))) /
          (α (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩) : ℂ)) else 1) := by
    intro k
    unfold liftPar
    split_ifs with h1 h2 h2
    · omega
    · push_cast
      rw [mul_one, mul_assoc, ← zpow_add₀ hq]
      congr 2; ring
    · have e : (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩ : Fin (n / 2)) = ⟨n' / 2 - 1 - k.1, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [e]
      have e2 : (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ))) = (qu : ℂ) ^ (-(n : ℤ)) * ((qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ)))) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ hq]
        congr 1
        have := k.isLt
        omega
      rw [e2]
      push_cast
      rw [pow_add]
      have := (α ⟨n' / 2 - 1 - k.1, by omega⟩).ne_zero
      field_simp
    · omega
  simp only [hfac, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  symm
  rw [← Fin.prod_congr' _ (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega), Fin.prod_univ_add]
  rw [Finset.prod_eq_one (fun i _ => ?_), one_mul]
  · refine Finset.prod_congr rfl fun r _ => ?_
    have e : Fin.cast (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega) (Fin.natAdd (n' / 2 - n / 2) r) =
        ⟨n' / 2 - n / 2 + r.1, by omega⟩ := Fin.ext (by simp)
    rw [e, dif_pos (by simp)]
    simp only [Fin.val_mk, Nat.add_sub_cancel_left, Fin.eta]
  · rw [dif_neg (by simp; omega), _root_.one_zpow]

theorem satU_eq_satU_liftPar_of_heckeVec_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC hC' hnn h hh h' hh' hE qu hqu α
  have hU := hS.1.unr
  obtain ⟨ℓ, hℓs, hℓa, hℓ0, hℓu, hℓz⟩ := GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm L ϖ σ q δ ψ n n' M ρ ω s hS
  have hvac : LocVac ρ s := hS.2.2.1
  have hb1 : ∀ {N : ℕ}, IsBorelU (1 : GU σ N) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_gt hij)]
  have hmix := GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action L ϖ σ q δ ψ n n' M ρ ω s hS ℓ hℓa hℓu
  have hμ : ∀ b : GU σ n, IsBorelU b → ℓ (ω (b, 1) s) =
      ∏ k, ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n')) ^ ordL (b.1.1 (lo n k) (lo n k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n (fun g => ℓ (ω (g, 1) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (b * b', 1) s = ω (b, 1) (ω (b', 1) s) := by
        rw [show ((b * b', 1) : GU σ n × GU σ n') = (b, 1) * (b', 1) by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix b 1 hb hb1).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup L ϖ σ q δ ψ n n' M ρ ω s hS hC ℓ hℓs hℓa hℓ0 k t ht, hqu]
  have hμ' : ∀ b : GU σ n', IsBorelU b → ℓ (ω (1, b) s) =
      ∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ ordL (b.1.1 (lo n' k) (lo n' k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n' (fun g => ℓ (ω (1, g) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (1, b * b') s = ω (1, b) (ω (1, b') s) := by
        rw [show ((1, b * b') : GU σ n × GU σ n') = (1, b) * (1, b') by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix 1 b hb1 hb).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedForm_torusTranslate_vacuum_value L ϖ σ q δ ψ n n' M ρ ω s hS hC' ℓ hℓs hℓa hℓ0 k t ht, hqu]
  obtain ⟨ι, _, b, hb, hvec, hsat⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n h hh
  obtain ⟨κ, _, b', hb', hvec', hsat'⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n' h' hh'
  have E := hE
  rw [hvec M (ω.comp (MonoidHom.inl _ _)) s (fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac),
    hvec' M (ω.comp (MonoidHom.inr _ _)) s (fun k hk => hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)] at E
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at E
  obtain ⟨hbl1, hbl2⟩ := GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular L ϖ σ q hU n n' hnn
  choose U hU1 hU2 hU3 using fun i => hbl1 (b i) (hb i)
  choose V hVt hV2 hV3 using fun j => hbl2 (b' j) (hb' j)
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n / 2)) (Fin (n / 2)) L → Matrix (Fin (n' / 2)) (Fin (n / 2)) L,
      ∀ t, Z t = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0 :=
    ⟨_, fun _ => rfl⟩
  have hZmul : ∀ t A, Z t * A = Z (t * A) := by
    intro t A; ext r c
    simp only [hZ, Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hZint : ∀ t, Z t ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) ↔ t ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) := by
    intro t
    constructor
    · intro ht i j
      have := ht ⟨i.1, by omega⟩ j
      simpa [hZ] using this
    · intro ht i j
      simp only [hZ, Matrix.of_apply]
      split_ifs
      exacts [ht _ _, zero_mem _]
  have hlow1 : ∀ N : ℕ, lowBlock (((1 : GU σ N) : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) = 1 := by
    intro N
    simp only [OneMemClass.coe_one, Units.val_one, lowBlock]
    exact Matrix.submatrix_one _ (fun a b e => by simp [hi, Fin.ext_iff] at e; exact Fin.ext (by omega))
  have key : ∀ t : GL (Fin (n / 2)) L,
      ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) =
      ∑ j, (h' (b' j) * ℓ (ω (1, b' j) s)) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
    intro t
    have l1 : ∀ i, ℓ (ρ (embLow n' n (Z t.1)) (ω (b i, 1) s)) =
        ℓ (ω (b i, 1) s) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro i
      rw [(hmix (b i) 1 (hb i) hb1).2, inv_one, hlow1, Matrix.one_mul, ← hU1 i, hZmul, hℓz, hZint]
    have l2 : ∀ j, ℓ (ρ (embLow n' n (Z t.1)) (ω (1, b' j) s)) =
        ℓ (ω (1, b' j) s) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro j
      have e3 := hV3 j t.1
      simp only [← hZ] at e3
      rw [(hmix 1 (b' j) hb1 (hb' j)).2, hlow1, Matrix.mul_one, e3, hℓz, hZint]
    have := congrArg (fun v => ℓ (ρ (embLow n' n (Z t.1)) v)) E
    simp only [map_sum, map_smul, smul_eq_mul, l1, l2] at this
    simpa only [mul_assoc] using this
  have G := GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation L ϖ σ q hU (n / 2) ι κ _ _ U V hU2 hVt key
    (fun d => ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
      (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d r)
  have hY : ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') : ℂ) ≠ 0 := by
    have := qu.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ this)
  rw [hsat α, hsat' (liftPar qu n n' α)]
  simp only [← hqu]
  calc _ = ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
        (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ ordL ((U i).1 r r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμ _ (hb i), mul_assoc, ← prodId1 n qu _ hY α]
        simp only [hU3]
    _ = _ := G
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hμ' _ (hb' j), mul_assoc, ← prodId2 n n' hnn qu α]
        simp only [hV2]

end GlobalTheory.SphTheta
