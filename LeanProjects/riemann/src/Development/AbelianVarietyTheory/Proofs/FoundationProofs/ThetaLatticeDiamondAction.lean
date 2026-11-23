import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrimeStatement

open scoped MatrixGroups
open Matrix GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.CyclotomicQExpansion.ThnEx

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_coe (σ : SL(2, ℤ)) : toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL σ := by
  have h : (0 : ℤ) < (σ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  unfold toGQ
  rw [dif_pos h]
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [ofSL]

theorem kmap_SL_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ : SL(2, ℤ)) :
    ∀ a ∈ X.A l, X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv a ∈ X.A l := by
  apply KmapA.kmap_mem_A
  intro W hW
  refine ⟨fun c => ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl _ (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl _ X.jK ∈ W
    rw [toGQ_coe, X.j_inv]; exact hW.2

private theorem exists_isDiam_of_coprime {N l d : ℕ} (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨e, heN, hel⟩ := Nat.chineseRemainder hNl d 1
  have hcop : Nat.Coprime e (N * l) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq heN]; exact hd
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hel]; simp
  have hbez := Nat.gcd_eq_gcd_ab e (N * l)
  rw [hcop.gcd_eq_one] at hbez
  refine ⟨⟨!![Nat.gcdA e (N * l), -Nat.gcdB e (N * l); ((N * l : ℕ) : ℤ), (e : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; push_cast at hbez ⊢; linear_combination -hbez
  · refine Subgroup.mem_inf.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr ?_, CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
    · simp
    · simp
  · simp only [en]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Int.cast_natCast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heN

private theorem conj_mem_Gamma1_of_mem_Gamma0 {N : ℕ} {σ γ : SL(2, ℤ)} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  have hg0 : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hγ0) (Subgroup.inv_mem _ hσ)
  have h1 : (⟨γ, hγ0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem]
    exact (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have h2 : (⟨σ * γ * σ⁻¹, hg0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N :=
    (CongruenceSubgroup.Gamma0Map N).normal_ker.conj_mem _ h1 ⟨σ, hσ⟩
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h2)

private theorem kmap_kmap_eq_kmap_trans (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.coe_restrictScalars]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  rfl

private theorem act_act_eq_act_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  funext u
  change X.kmap l (X.sl (toGQ (τ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ (mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))) =
    X.kmap l (X.sl (toGQ ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (b (mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
  have hm : mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) * mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) := by
    simp only [mZl, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  have hs : (X.sl (ofSL σ * ofSL τ)).toRingEquiv =
      (X.sl (ofSL σ)).toRingEquiv.trans (X.sl (ofSL τ)).toRingEquiv := by
    ext f; exact X.sl_mul _ _ f
  rw [kmap_kmap_eq_kmap_trans, toGQ_coe, toGQ_coe, toGQ_coe, map_mul, Matrix.mulVec_mulVec, hm, hs]

theorem diam_BSet (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.BSet N l w := by
  have hσ : IsDiam N l d (sgD N l d) := Classical.epsilon_spec (exists_isDiam_of_coprime hNl hd)
  obtain ⟨hpol, hinv⟩ := hb
  refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (kmap_SL_A X l (sgD N l d)) b hpol, ?_⟩
  intro γ hγ
  obtain ⟨hσN, hσl⟩ := Subgroup.mem_inf.mp hσ.1
  obtain ⟨hγN, hγl⟩ := Subgroup.mem_inf.mp hγ
  have hconj : sgD N l d * γ * (sgD N l d)⁻¹ ∈ Gam N l :=
    Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1_of_mem_Gamma0 hσN hγN,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσl hγl) (Subgroup.inv_mem _ hσl)⟩
  have hswap : sgD N l d * γ = sgD N l d * γ * (sgD N l d)⁻¹ * sgD N l d :=
    (inv_mul_cancel_right _ _).symm
  rw [act_act_eq_act_mul X l _ _ b, hswap, ← act_act_eq_act_mul X l (sgD N l d * γ * (sgD N l d)⁻¹) (sgD N l d) b,
    hinv _ hconj]

theorem diam_B (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  have hle : X.B N l w ≤ (X.B N l w).comap (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span (diam_BSet X N l w d hN hNl hd x hx))
  exact hle hb

end GlobalTheory.CyclotomicQExpansion.ThnEx

namespace GlobalTheory.CyclotomicQExpansion

theorem thN_isThB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime],
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧
      IsLat 1 (thN X A N l n d b) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : l.Prime := Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hb' := ThnEx.diam_B X N l w d (by omega) hNl hd b hb
  exact thN_spec X A N l n d b (GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l (IsAlgClosure.isAlgebraic (R := ℚ)) hj hl2 hlN (by omega) hlA n w hw _ hb')

end GlobalTheory.CyclotomicQExpansion
