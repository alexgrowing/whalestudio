import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponentsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeUStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerConditionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCong
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculusStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThHeckeU

theorem eval_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l σ x) = X.cls l n (Units.map σ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ x).val n = _
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, h]
  rw [Tower.cls, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  rfl

theorem cls_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (f g : X.Kˣ) : X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp only [Tower.cls, ← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add]
  rfl

theorem eval_sum_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (s : Finset ℕ) (σ : ℕ → (X.K ≃+* X.K)) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (∑ j ∈ s, X.kmap l (σ j) x) =
      X.cls l n (∏ j ∈ s, Units.map (σ j).toMonoidHom f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero, Finset.prod_empty]
    simp [Tower.cls]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add, ih, cls_mul, eval_kmap X l n _ x f h]

theorem isThB_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A) : IsThB X A N l 0 b ψ := by
  have hprim : Prim A (X.exp 1) := by
    rw [map_one]
    refine ⟨fun r => ?_, 0, by simp, by simp⟩
    by_cases h : r = 0
    · subst h; simp
    · simp [HahnSeries.coeff_one, h]
  refine ⟨1, fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩, hψ, 1, 1, 1, one_ne_zero, by simp,
    hprim, hprim, fun r => ⟨(ψ * X.exp 1 * X.exp 1).coeff r -
      (theta 1 (X.exp 1) * X.exp 1 - X.exp 1 * theta 1 (X.exp 1)).coeff r, ?_, by simp⟩⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) 0 (b ![1, 0]))
    rw [← hy, Tower.cls, Submodule.Quotient.eq]
    simp
  · simp only [map_one, mul_one, one_mul, sub_self, HahnSeries.coeff_zero, sub_zero]
    exact hψ r

theorem isThB_act_heckeU_same : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l,
    b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (hq ε l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hd hl b hb φ hφ h
  rw [GlobalTheory.T.diamond_commutes_hecke_U Ω ε X N l w d hd hl b hb]
  obtain ⟨f, hinv, hcls, hδ, hdl⟩ := h
  have hint : ∀ r, (hq ε l φ).coeff r ∈ A := by
    intro r
    rw [GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents Ω ε l (Nat.Prime.pos Fact.out) φ hφ r]
    split_ifs
    · exact hdl.1 _
    · exact A.zero_mem
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact isThB_zero X A N l _ _ hint
  set b' := X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b
  have hT : X.sl (ofSL ModularGroup.T) (f : X.K) = f := hinv _ (by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have hcoe : ((∏ j ∈ Finset.range l,
      Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K)
      = ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) (f : X.K) := by
    rw [Units.coe_prod]; rfl
  refine ⟨∏ j ∈ Finset.range l, Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f,
    ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant Ω ε X N l n hn _ hinv
  · have hv : X.heckeU l b' ![1, 0] = ∑ j ∈ Finset.range l,
        X.kmap l (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv (b' ![1, 0]) := by
      simp only [Tower.heckeU]
      rw [LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      show X.kmap l _ (b' _) = _
      congr 2
      ext i; fin_cases i <;> simp [mZl]
    rw [hv]
    exact eval_sum_kmap X l n (Finset.range l)
      (fun j => (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv) _ f hcls
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_preserves_delta_powerCondition Ω ε X N l n hn hl _ hinv hδ
  · rw [hcoe]; exact GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm Ω ε X A l n _ φ hT hφ hdl

theorem isThB_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hlA : (l : Ω) ∈ A.nonunits)
    (x : X.Fn l) (ψ ψ₂ : HahnSeries ℚ Ω) (h : IsThB X A N l n x ψ) (hint : ∀ r, ψ₂.coeff r ∈ A)
    (hc : ∀ r, CgA A l n (ψ.coeff r) (ψ₂.coeff r)) : IsThB X A N l n x ψ₂ := by
  obtain ⟨f, h1, h2, h3, h4⟩ := h
  obtain ⟨φ₀, han, hdiff⟩ := hj
  exact ⟨f, h1, h2, h3, (GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus ε X ⟨φ₀, hdiff, han⟩ l A hlA n 1 (f : X.K) (f : X.K) ψ ψ₂).2.2.1 h4 hint hc⟩

theorem isThB_act_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w →
    (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hAlg hj hl2 hN1 hw hlA hd hl b hb φ _ h
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, hAlg⟩
  have hl0 : 0 < l := Nat.Prime.pos Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl).symm
  obtain ⟨φ', h', hlat'⟩ := GlobalTheory.ThEx.of_lift GlobalTheory.ThLift.exists_invariant_lift Ω ε X A N l hAlg hj hl2 hl hN1 hlA n w hw _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w d hN1 hNl hd b hb)
  have hU := isThB_act_heckeU_same Ω ε X A N l n w d hd hl b hb _
    (fun r hr => by simpa using hlat' r hr) h'
  rw [Api.hq_eq_uq_of_isAlgClosed hl0 hlat'] at hU
  have hc := GlobalTheory.ThBCompat.isThB_succ_coeff_cong Ω ε X A N l hl2 hl hN1 hlA n _ φ _ h h'
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hdl⟩ := h
    exact hdl.1
  refine isThB_congr X A N l n hj hlA _ _ _ hU ?_ ?_
  · intro r
    rw [Api.coeff_uq hl0]
    split_ifs
    · exact hφA _
    · exact A.zero_mem
  · intro r
    rw [Api.coeff_uq hl0, Api.coeff_uq hl0]
    split_ifs
    · obtain ⟨z, hz, e⟩ := hc ((l : ℚ) * r)
      exact ⟨-z, A.neg_mem _ hz, by linear_combination -e⟩
    · exact ⟨0, A.zero_mem, by simp⟩

end GlobalTheory.ThHeckeU
