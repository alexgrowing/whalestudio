import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneUnramifiedPeriod

noncomputable section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem zpow_fix {Q R : Type} [Field Q] [CommRing R] [Algebra Q R] (f : R →ₐ[Q] R) (T : Rˣ) (c : Qˣ)
    (h : (c : Q) • f (T : R) = T) (m : ℤ) : ((c ^ m : Qˣ) : Q) • f ((T ^ m : Rˣ) : R) = ((T ^ m : Rˣ) : R) := by
  have e : Units.map (algebraMap Q R : Q →* R) c * Units.map (f : R →* R) T = T := by
    ext; simpa [Algebra.smul_def] using h
  have e' : Units.map (algebraMap Q R : Q →* R) (c ^ m) * Units.map (f : R →* R) (T ^ m) = T ^ m := by
    rw [map_zpow, map_zpow, ← mul_zpow, e]
  rw [Algebra.smul_def]
  exact congrArg Units.val e'

private theorem smul_mul_tmul {Q A R : Type} [Field Q] [Field A] [CommRing R] [Algebra Q R] [Algebra Q A]
    (c : Q) (x : A ⊗[Q] R) (b : R) : algebraMap Q A c • (x * (1 : A) ⊗ₜ[Q] b) = x * (1 : A) ⊗ₜ[Q] (c • b) := by
  rw [algebraMap_smul, tmul_smul, mul_smul_comm]

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

private theorem stRep_mul (κ η : ↥(GK K) →* (↥L.1)ˣ) (g : ↥(GK K)) (a : ↥L.1) (h : (κ g : ↥L.1) = a * η g)
    (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    stRep P (UpperTheory.V.Loc.chRep κ) g (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      a • (stRep P (UpperTheory.V.Loc.chRep η) g u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] actSt P (g : GQ l) b) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, stRep_tmul, stRep_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      map_mul (actSt P (g : GQ l)), smul_tmul']
    congr 1
    simp [UpperTheory.V.Loc.chRep, h, mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy, smul_add]

private theorem phiV_mul (u : ↥L.1 ⊗[ℚ_[l]] Bst P) (b : Bst P) :
    phiV P ↥L.1 ↥L.1 (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) = phiV P ↥L.1 ↥L.1 u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiSt P b := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, phiV_tmul, phiV_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_mul]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

private theorem phiV_pow_mul (c : ℚ_[l]) (b : Bst P) (hb : c • phiSt P b = b) (k : ℕ) (u : ↥L.1 ⊗[ℚ_[l]] Bst P) :
    (algebraMap ℚ_[l] ↥L.1 c) ^ k • (phiV P ↥L.1 ↥L.1 ^ k) (u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) =
      (phiV P ↥L.1 ↥L.1 ^ k) u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] b := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, mul_smul, ← map_smul, phiV_mul, smul_mul_tmul, hb, ih]

theorem UpperTheory.weilDeligne_character_twist_period :
    UpperTheory.V.Af.Wd.TwistPer := by
  intro l _ K L κ χ η m hκ hc hη
  have hu := UpperTheory.weilDeligne_unramified_period l K L η hc hη
  unfold UpperTheory.V.Af.Wd.cycL at hκ
  generalize UpperTheory.V.Loc.PP l = P at hu hκ ⊢
  obtain ⟨u, hu0, hu1, hu2⟩ := hu
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  let T : (Bst P)ˣ := Units.map (C : P.R.B →+* Bst P) (isUnit_tB P).unit⁻¹
  have hT : (T : Bst P) = C (tInv P) := rfl
  have h1 : ∀ g : GQ l, ((P.χQ g ^ m : ℚ_[l]ˣ) : ℚ_[l]) • actSt P g ((T ^ m : (Bst P)ˣ) : Bst P) = ((T ^ m : (Bst P)ˣ) : Bst P) :=
    fun g => zpow_fix (actSt P g) T (P.χQ g) (by rw [hT, actSt_C, smul_C, smul_actQ_tInv]) m
  have h2 := zpow_fix (phiSt P) T (Units.mk0 _ hl) (by rw [hT, phiSt_C, smul_C, Units.val_mk0, smul_phiB_tInv]) m
  refine ⟨u * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] ((T ^ m : (Bst P)ˣ) : Bst P), fun h0 => hu0 ?_, fun g => ?_, fun g k hk => ?_⟩
  · have := congrArg (· * (1 : ↥L.1) ⊗ₜ[ℚ_[l]] (((T ^ m)⁻¹ : (Bst P)ˣ) : Bst P)) h0
    simpa only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one, zero_mul,
      ← Algebra.TensorProduct.one_def] using this
  · rw [stRep_mul P κ η g ((χ g : ↥L.1) * algebraMap ℚ_[l] ↥L.1 ((P.χQ (g : GQ l) ^ m : ℚ_[l]ˣ) : ℚ_[l])) ?_, hu1,
      mul_smul, smul_mul_tmul, h1]
    rw [hκ g, Units.val_mul, Units.val_mul, mul_comm (χ g : ↥L.1)]
    simp
  · have e : (l : ↥L.1) ^ (m * k) = (algebraMap ℚ_[l] ↥L.1 ((Units.mk0 _ hl ^ m : ℚ_[l]ˣ) : ℚ_[l])) ^ k := by
      simp [zpow_mul]
    rw [e, mul_smul, phiV_pow_mul P _ _ h2, ← smul_mul_assoc, hu2 g k hk]
