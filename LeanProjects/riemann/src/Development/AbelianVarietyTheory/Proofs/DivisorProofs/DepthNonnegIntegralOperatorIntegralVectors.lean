import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLogStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthNonneg

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def intSub (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, v.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, v.map_neg]
    exact ha

theorem mem_intSub {x : C} : x ∈ intSub v ↔ IsIntV v x := Iff.rfl

def HurInt (v : AddValuation C (WithTop ℝ)) {σ : Type} (g : MvPowerSeries σ C) : Prop :=
  ∀ α, mfact α * coeff α g ∈ intSub v

theorem mfact_fintype {σ : Type} [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : C) = ∏ i, ((α i).factorial : C) :=
  Finsupp.prod_fintype _ _ (by simp)

theorem mfact_mem {σ : Type} (α : σ →₀ ℕ) : (mfact α : C) ∈ intSub v :=
  Subring.prod_mem _ fun _ _ => natCast_mem _ _

theorem mvIsInt_iff {σ : Type} (g : MvPowerSeries σ C) : MvIsInt v g ↔ ∀ α, coeff α g ∈ intSub v :=
  Iff.rfl

theorem mvIsInt_mul {σ : Type} {g h : MvPowerSeries σ C} (hg : MvIsInt v g) (hh : MvIsInt v h) :
    MvIsInt v (g * h) := by
  classical
  intro α
  rw [← mem_intSub, coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hg _) (hh _)

theorem mvIsInt_sum {σ ι : Type} (s : Finset ι) {g : ι → MvPowerSeries σ C}
    (hg : ∀ i, MvIsInt v (g i)) : MvIsInt v (∑ i ∈ s, g i) := by
  intro α
  rw [← mem_intSub, map_sum]
  exact Subring.sum_mem _ fun i _ => hg i α

theorem hurInt_of_mvIsInt {σ : Type} {g : MvPowerSeries σ C} (hg : MvIsInt v g) : HurInt v g :=
  fun α => Subring.mul_mem _ (mfact_mem α) (hg α)

theorem hurInt_add {σ : Type} {g h : MvPowerSeries σ C} (hg : HurInt v g) (hh : HurInt v h) :
    HurInt v (g + h) := fun α => by
  rw [map_add, mul_add]; exact Subring.add_mem _ (hg α) (hh α)

theorem hurInt_zero {σ : Type} : HurInt v (0 : MvPowerSeries σ C) := fun α => by simp

theorem hurInt_one {σ : Type} : HurInt v (1 : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_one]
  split_ifs with h
  · subst h; simp [mfact]
  · simp

theorem hurInt_sum {σ ι : Type} (s : Finset ι) {g : ι → MvPowerSeries σ C}
    (hg : ∀ i ∈ s, HurInt v (g i)) : HurInt v (∑ i ∈ s, g i) := by
  intro α
  rw [map_sum, Finset.mul_sum]
  exact Subring.sum_mem _ fun i hi => hg i hi α

theorem hurInt_C_mul {σ : Type} {c : C} (hc : c ∈ intSub v) {g : MvPowerSeries σ C}
    (hg : HurInt v g) : HurInt v (MvPowerSeries.C c * g) := fun α => by
  rw [coeff_C_mul, mul_left_comm]; exact Subring.mul_mem _ hc (hg α)

theorem hurInt_mul {σ : Type} [Fintype σ] {g h : MvPowerSeries σ C} (hg : HurInt v g)
    (hh : HurInt v h) : HurInt v (g * h) := by
  classical
  intro α
  rw [coeff_mul, Finset.mul_sum]
  refine Subring.sum_mem _ fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have key : (mfact α : C) * (coeff p.1 g * coeff p.2 h) =
      (∏ i, (((p.1 i + p.2 i).choose (p.2 i) : ℕ) : C)) *
        ((mfact p.1 * coeff p.1 g) * (mfact p.2 * coeff p.2 h)) := by
    rw [mfact_fintype, mfact_fintype, mfact_fintype, ← hp]
    have : ∀ i, (((p.1 + p.2) i).factorial : C) =
        (((p.1 i + p.2 i).choose (p.2 i) : ℕ) : C) * ((p.1 i).factorial : C) * ((p.2 i).factorial : C) := by
      intro i
      rw [Finsupp.add_apply, ← Nat.add_choose_mul_factorial_mul_factorial (p.1 i) (p.2 i)]
      push_cast; ring
    simp_rw [this, Finset.prod_mul_distrib]
    ring
  rw [key]
  exact Subring.mul_mem _ (Subring.prod_mem _ fun i _ => natCast_mem _ _)
    (Subring.mul_mem _ (hg _) (hh _))

theorem hurInt_pow {σ : Type} [Fintype σ] {g : MvPowerSeries σ C} (hg : HurInt v g) (n : ℕ) :
    HurInt v (g ^ n) := by
  induction n with
  | zero => simpa using hurInt_one
  | succ n ih => rw [pow_succ]; exact hurInt_mul ih hg

theorem hurInt_finsuppProd' {σ τ : Type} [Fintype τ] (g : σ → ℕ → MvPowerSeries τ C)
    (hg : ∀ s e, HurInt v (g s e)) (d : σ →₀ ℕ) : HurInt v (d.prod g) :=
  Finset.prod_induction _ (HurInt v) (fun _ _ h1 h2 => hurInt_mul h1 h2) hurInt_one
    (fun s _ => hg s _)

theorem hurInt_finsuppProd {σ τ : Type} [Fintype τ] (a : σ → MvPowerSeries τ C)
    (ha : ∀ s, HurInt v (a s)) (d : σ →₀ ℕ) : HurInt v (d.prod fun s e => a s ^ e) :=
  hurInt_finsuppProd' _ (fun s e => hurInt_pow (ha s) e) d

theorem hurInt_subst {σ τ : Type} [Fintype τ] {a : σ → MvPowerSeries τ C} (hS : HasSubst a)
    (ha : ∀ s, HurInt v (a s)) {f : MvPowerSeries σ C} (hf : MvIsInt v f) :
    HurInt v (subst a f) := by
  intro α
  rw [coeff_subst hS]
  refine finsum_induction (fun x => (mfact α : C) * x ∈ intSub v) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact Subring.add_mem _ hx hy) (fun d => ?_)
  simp only [smul_eq_mul]
  rw [mul_left_comm]
  exact Subring.mul_mem _ (hf d) (hurInt_finsuppProd a ha d α)

theorem constantCoeff_subst_mem {σ τ : Type} {a : σ → MvPowerSeries τ C} (hS : HasSubst a)
    (ha : ∀ s, constantCoeff (a s) ∈ intSub v) {f : MvPowerSeries σ C} (hf : MvIsInt v f) :
    constantCoeff (subst a f) ∈ intSub v := by
  rw [constantCoeff_subst hS]
  refine finsum_induction (· ∈ intSub v) (Subring.zero_mem _)
    (fun x y hx hy => Subring.add_mem _ hx hy) (fun d => ?_)
  simp only [smul_eq_mul]
  refine Subring.mul_mem _ (hf d) ?_
  rw [map_finsuppProd]
  exact Subring.prod_mem _ fun s _ => by show constantCoeff (a s ^ d s) ∈ _; rw [map_pow]; exact Subring.pow_mem _ (ha s) _

section CharZero

variable [CharZero C]

theorem mvIsInt_X {σ : Type} (s : σ) : MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  rw [← mem_intSub, coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hurInt_subst_expOf {d : ℕ} (G : LogFGL v d) {f : MvPowerSeries (Fin d) C}
    (hf : MvIsInt v f) : HurInt v (subst (expOf G) f) := by
  classical
  obtain ⟨D, hD, hJ⟩ := GlobalTheory.T.exists_integral_invariant_derivation_log C v d G
  have hS : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  suffices h : ∀ n, ∀ α : Fin d →₀ ℕ, ∑ i, α i = n → ∀ f : MvPowerSeries (Fin d) C,
      MvIsInt v f → (mfact α : C) * coeff α (subst (expOf G) f) ∈ intSub v from
    fun α => h _ α rfl f hf
  intro n
  induction n with
  | zero =>
    intro α hα f hf
    have : α = 0 := by
      ext i; exact (Finset.sum_eq_zero_iff.mp hα) i (Finset.mem_univ i)
    subst this
    rw [coeff_zero_eq_constantCoeff]
    simp only [mfact, Finsupp.prod_zero_index, one_mul]
    exact constantCoeff_subst_mem hS
      (fun s => by rw [(isExp_expOf G).1 s]; exact Subring.zero_mem _) hf
  | succ n ih =>
    intro α hα f hf
    obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
      by_contra h; push Not at h; simp [h] at hα
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single k 1 := ⟨α - Finsupp.single k 1, by
      ext i
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · omega⟩
    have hsum : ∑ i, β i = n := by
      have : ∑ i, (β + Finsupp.single k 1 : Fin d →₀ ℕ) i = ∑ i, β i + 1 := by
        simp [Finset.sum_add_distrib, Finsupp.single_apply]
      omega
    have hm : (mfact (β + Finsupp.single k 1) : C) = mfact β * ((β k : C) + 1) := by
      rw [mfact_fintype, mfact_fintype]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
      have : ∀ i ∈ Finset.univ.erase k,
          (((β + Finsupp.single k 1 : Fin d →₀ ℕ) i).factorial : C) = ((β i).factorial : C) := by
        intro i hi
        simp [Finsupp.single_apply, Ne.symm (Finset.ne_of_mem_erase hi)]
      rw [Finset.prod_congr rfl this]
      simp [Nat.factorial_succ]
      ring
    rw [hm, mul_assoc, hJ f k β]
    refine ih β hsum _ ?_
    refine mvIsInt_sum _ fun l => mvIsInt_mul (hD k l) fun γ => ?_
    show ((γ l : C) + 1) * coeff (γ + Finsupp.single l 1) f ∈ intSub v
    exact Subring.mul_mem _ (Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _)) (hf _)

def dpow {σ : Type} (n : ℕ) (x : MvPowerSeries σ C) : MvPowerSeries σ C :=
  MvPowerSeries.C ((n.factorial : C)⁻¹) * x ^ n

theorem pow_eq_dpow {σ : Type} (n : ℕ) (x : MvPowerSeries σ C) :
    x ^ n = MvPowerSeries.C (n.factorial : C) * dpow n x := by
  rw [dpow, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast n.factorial_ne_zero), map_one, one_mul]

theorem dpow_add {σ : Type} (n : ℕ) (x y : MvPowerSeries σ C) :
    dpow n (x + y) = ∑ m ∈ Finset.range (n + 1), dpow m x * dpow (n - m) y := by
  rw [dpow, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  simp only [dpow]
  have h1 : (n.choose m : C) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  have h2 : (m.factorial : C) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h3 : ((n - m).factorial : C) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have hc : ((n.factorial : C))⁻¹ * (n.choose m : C) =
      ((m.factorial : C))⁻¹ * (((n - m).factorial : C))⁻¹ := by
    rw [← Nat.choose_mul_factorial_mul_factorial hmn]
    push_cast
    field_simp
  rw [show ((n.choose m : ℕ) : MvPowerSeries σ C) = MvPowerSeries.C (n.choose m : C) from
    (map_natCast _ _).symm]
  calc _ = MvPowerSeries.C ((n.factorial : C)⁻¹ * (n.choose m : C)) * (x ^ m * y ^ (n - m)) := by
        rw [map_mul]; ring
    _ = _ := by rw [hc, map_mul]; ring

theorem hurInt_dpow_smul_X {σ : Type} [Fintype σ] {c : C} (hc : c ∈ intSub v) (a : σ) (n : ℕ) :
    HurInt v (dpow n (c • (X a : MvPowerSeries σ C))) := by
  classical
  intro α
  rw [dpow, smul_eq_C_mul, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst h
    have hm : (mfact (Finsupp.single a n) : C) = n.factorial := by
      simp [mfact, Finsupp.prod_single_index]
    rw [hm, mul_one, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
    exact Subring.pow_mem _ hc n
  · simp

theorem hurInt_dpow_linear {σ ι : Type} [Fintype σ] (s : Finset ι) (c : ι → C)
    (hc : ∀ i, c i ∈ intSub v) (x : ι → σ) :
    ∀ n, HurInt v (dpow n (∑ i ∈ s, c i • (X (x i) : MvPowerSeries σ C))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    cases n with
    | zero => simpa [dpow] using (hurInt_one (v := v) (σ := σ))
    | succ n => simpa [dpow] using (hurInt_zero (v := v) (σ := σ))
  | insert i s hi ih =>
    intro n
    rw [Finset.sum_insert hi, dpow_add]
    exact hurInt_sum _ fun m _ => hurInt_mul (hurInt_dpow_smul_X (hc i) _ _) (ih _)

theorem hurInt_subst_dpow {σ τ : Type} [Fintype τ] {ℓ : σ → MvPowerSeries τ C} (hS : HasSubst ℓ)
    (hℓ : ∀ s n, HurInt v (dpow n (ℓ s))) {h : MvPowerSeries σ C} (hh : HurInt v h) :
    HurInt v (subst ℓ h) := by
  intro α
  rw [coeff_subst hS]
  refine finsum_induction (fun x => (mfact α : C) * x ∈ intSub v) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact Subring.add_mem _ hx hy) (fun d => ?_)
  simp only [smul_eq_mul]
  have hp : (d.prod fun s e => ℓ s ^ e) =
      MvPowerSeries.C (mfact d : C) * d.prod fun s e => dpow e (ℓ s) := by
    simp only [pow_eq_dpow]
    rw [mfact, map_finsuppProd, ← Finsupp.prod_mul]
  rw [hp, coeff_C_mul]
  have : (mfact α : C) * (coeff d h * (mfact d * coeff α (d.prod fun s e => dpow e (ℓ s)))) =
      (mfact d * coeff d h) * (mfact α * coeff α (d.prod fun s e => dpow e (ℓ s))) := by ring
  rw [this]
  exact Subring.mul_mem _ (hh d) (hurInt_finsuppProd' _ (fun s e => hℓ s e) d α)

end CharZero

theorem depth_nonneg : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), (∀ b a e, IsIntV v (u b a e)) → (∀ α, IsIntV v (P.coeff α)) → 0 ≤ depth G u P := by
  intro C _ _ v κ _ _ d G ι _ _ u P hu hP
  classical
  have hℓS : ∀ b, HasSubst (fun e : Fin (d b) =>
      ∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) :=
    fun b => hasSubst_of_constantCoeff_zero (fun e => by simp)
  have hexp : ∀ b (e : Fin (d b)), HurInt v (expOf (G b) e) := fun b e => by
    have := hurInt_subst_expOf (G b) (mvIsInt_X (v := v) e)
    rwa [subst_X (hasSubst_of_constantCoeff_zero (isExp_expOf (G b)).1)] at this
  have hE : ∀ x, HurInt v (expAlong G u x) := fun x =>
    hurInt_subst_dpow (hℓS x.1)
      (fun e n => hurInt_dpow_linear Finset.univ _ (fun a => hu x.1 a e) _ n) (hexp x.1 x.2)
  have hE0 : ∀ x, constantCoeff (expAlong G u x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hℓS x.1) (fun e => by simp) ((isExp_expOf (G x.1)).1 x.2)
  have hES : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero hE0
  unfold depth
  refine le_iInf fun f => ?_
  have hg := hurInt_subst hES hE f.2
  have hmem : derivAt0 P (subst (expAlong G u) f.1) ∈ intSub v :=
    Subring.sum_mem _ fun α _ => by
      rw [mul_assoc]; exact Subring.mul_mem _ (hP α) (hg α)
  exact WithBot.coe_le_coe.mpr hmem

end

end GlobalTheory.DepthNonneg
