import Formalism.LagrangeIdealLifts.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.LIFT

namespace CocyclePolynomialSubmodules

theorem aeval_pres {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (f : E →ₗ[R] E)
    (S : Submodule R E) (hf : ∀ y ∈ S, f y ∈ S) (p : Polynomial R) :
    ∀ y ∈ S, Polynomial.aeval f p y ∈ S := by
  intro y hy
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    apply S.smul_mem
    induction n with
    | zero =>
      rw [pow_zero, Module.End.one_apply]
      exact hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hf _ ih

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)

def QS : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, WD.QInv, smul_add] at *
    exact W.N.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, WD.QInv, smul_zero]
    exact W.N.zero_mem
  smul_mem' c y hy := by
    simp only [Set.mem_ofPred_eq, WD.QInv] at *
    rw [smul_smul, mul_comm, mul_smul]
    exact W.N.smul_mem c hy

theorem mem_QS {y : D} : y ∈ QS W ↔ W.QInv y := Iff.rfl

def CS : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := by
    rintro a b ⟨y1, h1, rfl⟩ ⟨y2, h2, rfl⟩
    exact ⟨y1 + y2, (QS W).add_mem h1 h2, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (QS W).zero_mem, (smul_zero _).symm⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    exact ⟨c • y, (QS W).smul_mem c hy, by rw [smul_smul, smul_smul, mul_comm]⟩

theorem mem_CS {ω : D} : ω ∈ CS W ↔ W.C2 ω := Iff.rfl

theorem N_le_QS : W.N ≤ QS W := by
  intro y hy
  refine (mem_QS W).mpr ?_
  unfold WD.QInv
  exact W.N.smul_mem _ hy

theorem CS_le_QS : CS W ≤ QS W := by
  intro ω hω
  obtain ⟨y, hy, rfl⟩ := (mem_CS W).mp hω
  exact (QS W).smul_mem B.X ((mem_QS W).mpr hy)

theorem γ_mem_N {n : D} (hn : n ∈ W.N) : W.γ n ∈ W.N := by
  obtain ⟨x', hx', h⟩ := W.γ_N n hn
  rw [← sub_add_cancel (W.γ n) n, h]
  exact W.N.add_mem (W.N.smul_mem _ hx') hn

theorem γ_mem_QS {y : D} (hy : y ∈ QS W) : W.γ y ∈ QS W := by
  rw [mem_QS] at hy ⊢
  unfold WD.QInv at hy ⊢
  obtain ⟨t, ht, hQ⟩ := B.9
  have h1 := γ_mem_N W hy
  rw [W.γ_smul, map_pow, hQ, mul_pow, mul_comm (B.Q ^ M), mul_smul] at h1
  obtain ⟨v, hv⟩ := ht.pow M
  have h2 := W.N.smul_mem (↑v⁻¹ : A) h1
  rwa [← hv, smul_smul, Units.inv_mul, one_smul] at h2

theorem γ_mem_CS {ω : D} (hω : ω ∈ CS W) : W.γ ω ∈ CS W := by
  rw [mem_CS] at hω ⊢
  obtain ⟨y, hy, rfl⟩ := hω
  obtain ⟨t, ht⟩ := B.8
  refine ⟨((algebraMap ℤ_[ℓ] A) ↑B.u + B.X * t) • W.γ y,
    (mem_QS W).mp ((QS W).smul_mem _ (γ_mem_QS W ((mem_QS W).mpr hy))), ?_⟩
  rw [W.γ_smul, ht, mul_smul]

theorem aeval_mem_N (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ W.N) :
    Polynomial.aeval W.γ p y ∈ W.N := aeval_pres W.γ (W.N.restrictScalars ℤ_[ℓ]) (fun _ h => γ_mem_N W h) p y hy

theorem aeval_mem_QS (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ QS W) :
    Polynomial.aeval W.γ p y ∈ QS W := aeval_pres W.γ ((QS W).restrictScalars ℤ_[ℓ]) (fun _ h => γ_mem_QS W h) p y hy

theorem aeval_mem_CS (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ CS W) :
    Polynomial.aeval W.γ p y ∈ CS W := aeval_pres W.γ ((CS W).restrictScalars ℤ_[ℓ]) (fun _ h => γ_mem_CS W h) p y hy

theorem cocyclePolynomialDivision_φ_mem_fact {n : D} (hn : n ∈ W.N) : W.φ (B.X ^ (M + 1) • n) ∈ W.N := by
  have e : (B.X * B.Q) ^ (M + 1) = (B.X ^ (M + 1) * B.Q) * B.Q ^ M := by ring
  rw [W.φ_smul, map_pow, B.7, e, mul_smul]
  exact W.N.smul_mem _ (W.φ_N n hn)

theorem tors_free (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N)
    {c : ℤ_[ℓ]} (hc : c ≠ 0) {y : D} (hy : y ∈ QS W) (hcy : c • y ∈ W.N) : y ∈ W.N := by
  have key : ∀ k : ℕ, ∀ z ∈ QS W, ((ℓ : ℤ_[ℓ]) ^ k) • z ∈ W.N → z ∈ W.N := by
    intro k
    induction k with
    | zero =>
      intro z _ hz
      simpa using hz
    | succ k ih =>
      intro z hz hkz
      apply ih z hz
      apply h4 _ ((mem_QS W).mp ((QS W).smul_of_tower_mem _ hz))
      rwa [smul_smul, ← pow_succ']
  obtain ⟨k, u, hcu⟩ : ∃ (k : ℕ) (u : ℤ_[ℓ]ˣ), c = u * (ℓ : ℤ_[ℓ]) ^ k := by
    first
      | exact IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      | exact DiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      | exact ⟨_, _, PadicInt.unitCoeff_spec hc⟩
  rw [hcu, mul_comm, mul_smul] at hcy
  have h5 := key k _ ((QS W).smul_of_tower_mem (u : ℤ_[ℓ]) hy) hcy
  have h6 := W.N.smul_of_tower_mem (↑u⁻¹ : ℤ_[ℓ]) h5
  rwa [smul_smul, Units.inv_mul, one_smul] at h6

theorem main (P : Polynomial ℤ_[ℓ]) (cG : ℤ_[ℓ]) (hcG : cG ≠ 0)
    (hU : ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ n' ∈ W.N,
      cG • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (M + 1) • n')
    (h1 : ∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z))
    (h2 : ∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N)
    (h3 : ∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) * P) y ∈ W.N)
    (h4 : ∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) :
    W.TorsKilled (P.eval 1 * cG) := by
  rintro ω hω ⟨k, y, z, ⟨hyQ, n, hn, rfl⟩, hk⟩
  obtain ⟨x, hx, n', hn', hxe⟩ := hU n hn
  have hm : B.X ^ (M + 1) • n' ∈ W.N := W.N.smul_mem _ hn'
  have hφm : W.φ (B.X ^ (M + 1) • n') - B.X ^ (M + 1) • n' ∈ W.N :=
    W.N.sub_mem (cocyclePolynomialDivision_φ_mem_fact W hn') hm
  have hXx : B.X • x ∈ W.N := W.N.smul_mem _ hx
  have hYQ : cG • y - (W.φ (B.X • x) - B.X • x) ∈ QS W :=
    (QS W).sub_mem ((QS W).smul_of_tower_mem _ hyQ)
      ((QS W).sub_mem (W.φ_N _ hXx) (N_le_QS W hXx))
  have key : (cG * (ℓ : ℤ_[ℓ]) ^ k) • ω =
      (W.γ (cG • y - (W.φ (B.X • x) - B.X • x)) - (cG • y - (W.φ (B.X • x) - B.X • x))) -
        (W.φ (B.X ^ (M + 1) • n') - B.X ^ (M + 1) • n') := by
    rw [mul_smul, hk, WD.d1]
    have e1 : cG • W.φ (B.X • n) = W.φ (cG • (B.X • n)) := (map_smul _ _ _).symm
    have e2 : cG • W.γ y = W.γ (cG • y) := (map_smul _ _ _).symm
    rw [smul_sub, smul_sub, smul_sub, e1, e2, hxe]
    simp only [map_sub, map_add, W.comm]
    abel
  have hω' : ω ∈ CS W := hω
  set p := Polynomial.aeval W.γ P with hp
  have hpQ : p ω ∈ QS W := aeval_mem_QS W P (CS_le_QS W hω')
  have hγ1 : ∀ Y : D, p (W.γ Y - Y) = Polynomial.aeval W.γ ((Polynomial.X - 1) * P) Y := by
    intro Y
    rw [mul_comm, map_mul, Module.End.mul_apply]
    congr 1
    simp
  have hcp : (cG * (ℓ : ℤ_[ℓ]) ^ k) • p ω ∈ W.N := by
    rw [← map_smul, key, map_sub, hγ1]
    exact W.N.sub_mem (h3 _ hYQ) (aeval_mem_N W P hφm)
  have hn0 : p ω ∈ W.N :=
    tors_free W h4 (mul_ne_zero hcG (pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))) hpQ hcp
  obtain ⟨y₀, hy₀Q, hy₀e⟩ : p ω ∈ CS W := aeval_mem_CS W P hω'
  have hy₀ : y₀ ∈ W.N := h2 y₀ hy₀Q (hy₀e ▸ hn0)
  obtain ⟨x₀, hx₀, n₀', hn₀', e0⟩ := hU y₀ hy₀
  obtain ⟨z₀, hz₀, e1⟩ := h1 n₀' hn₀'
  obtain ⟨S, hS⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := P) (a := 1)
  have eS : P.eval 1 • ω = p ω - (W.γ (Polynomial.aeval W.γ S ω) - Polynomial.aeval W.γ S ω) := by
    have := congrArg (fun q => Polynomial.aeval W.γ q ω) hS
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_one,
      LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.End.one_apply] at this
    rw [← hp] at this
    rw [← this]
    abel
  have hSQ : Polynomial.aeval W.γ S ω ∈ QS W := aeval_mem_QS W S (CS_le_QS W hω')
  refine ⟨cG • (-(Polynomial.aeval W.γ S ω)) + B.X • x₀, B.X ^ (M + 1) • z₀,
    ⟨(QS W).add_mem ((QS W).smul_of_tower_mem _ ((QS W).neg_mem hSQ))
      (N_le_QS W (W.N.smul_mem _ hx₀)),
      ⟨B.X ^ M • z₀, W.N.smul_mem _ hz₀, by rw [pow_succ', mul_smul]⟩⟩, ?_⟩
  rw [mul_comm, mul_smul, eS, hy₀e, smul_sub, e0, e1, WD.d1]
  simp only [map_add, map_neg, map_smul, smul_sub, smul_neg]
  abel

end CocyclePolynomialSubmodules

theorem uClaim_of (hU : UGraded) (_hG : GradedStep) : UClaim := by
  intro ℓ _ A _ _ B M D _ _ _ _ W s J hs hs2 hv hJ h1 h2 h3 h4
  have hcG : (∏ i ∈ Finset.Icc 1 M, ((B.u : ℤ_[ℓ]) ^ i - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hi0 : (i : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    have := (Formalism.WindowSums.valuation_zpow_sub_one ℓ B.u s hs hs2 hv (i : ℤ) hi0).1
    simpa using this
  have hP : Polynomial.eval 1
      (∏ j ∈ J, (Polynomial.X - Polynomial.C (((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) =
      ∏ j ∈ J, (1 - ((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    simp [Polynomial.eval_prod]
  rw [← hP]
  exact CocyclePolynomialSubmodules.main W _ _ hcG (hU ℓ A B M D W M) h1 h2 h3 h4

end Formalism.LIFT
