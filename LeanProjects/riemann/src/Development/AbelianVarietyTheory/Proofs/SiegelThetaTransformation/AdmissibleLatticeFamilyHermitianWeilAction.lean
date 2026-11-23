import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionCommPositiveUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLattice
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.WeilAdm

open WeilLevel Base

noncomputable section

theorem sum_quot_comp {A V : Type} [AddCommGroup A] [AddCommMonoid V] (B : AddSubgroup A)
    [Fintype (A ⧸ B)] (f : A → V) (hf : ∀ x y, x - y ∈ B → f x = f y) (α : A → A)
    (hα : ∀ x y, α x - α y ∈ B → x - y ∈ B) :
    ∑ q : A ⧸ B, f (α q.out) = ∑ q : A ⧸ B, f q.out := by
  have hinj : Function.Injective fun q : A ⧸ B => ((α q.out : A) : A ⧸ B) := by
    intro q q' h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact hα _ _ (QuotientAddGroup.eq_iff_sub_mem.1 h)
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun q => ?_
  exact hf _ _ (QuotientAddGroup.eq_iff_sub_mem.1 (QuotientAddGroup.out_eq' _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}

omit [IsCMField E] in
theorem isSB_add {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    IsSB (φ + ψ) := by
  obtain ⟨R, hR, h1, h2⟩ := hφ
  obtain ⟨S, hS, h3, h4⟩ := hψ
  have k : ∀ (m : ℕ) (y : Matrix (Fin n) (Fin N) E), IntM y → IntM ((m : E) • y) :=
    fun m y hy i j => (isIntegral_natCast (R := ℤ) m).mul (hy i j)
  refine ⟨R * S, by positivity, fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases h : φ x = 0
    · rw [Pi.add_apply, h, zero_add] at hx
      rw [Nat.cast_mul, mul_smul]; exact k _ _ (h3 x hx)
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact k _ _ (h1 x h)
  · have e1 := h2 x _ (k S y hy)
    have e2 := h4 x _ (k R y hy)
    rw [smul_smul] at e1 e2
    rw [Pi.add_apply, Pi.add_apply, Nat.cast_mul, e1, mul_comm, e2]

theorem phase_one (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    {b y : Matrix (Fin n) (Fin N) E} (hb : ColsIn Λ b) (hy : ColsIn Λ y) :
    cexp (π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, 2 * (b k a * cc (y k a))) : ℚ) : ℂ)) = 1 := by
  have hw : IsIntegral ℤ (∑ a, herm 1 (bᵀ a) (yᵀ a)) :=
    IsIntegral.sum _ fun a _ => (hΛ _).1 (hb a) _ (hy a)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) hw)
  have e2 : ∑ k, ∑ a, 2 * (b k a * cc (y k a)) = (2 : ℚ) • ∑ a, herm 1 (bᵀ a) (yᵀ a) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [herm_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Rat.smul_def]
  rw [e2, map_smul, ← hk]
  have : (π : ℂ) * I * (((2 : ℚ) • algebraMap ℤ ℚ k : ℚ) : ℂ) = k * (2 * π * I) := by
    simp; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

def rho (R : ℕ) (X : Matrix (Fin n) (Fin N ⊕ Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Matrix (Fin n) (Fin N) E → ℂ :=
  heisH (((2 * R : ℕ) : E) • X.toCols₁) (((2 * R : ℕ) : E) • X.toCols₂) φ

def cols (Λ : Lt E n) (N : ℕ) : AddSubgroup (Matrix (Fin n) (Fin N ⊕ Fin N) E) where
  carrier := {X | ∀ i, Xᵀ i ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy i => Λ.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => Λ.neg_mem (hx i)

theorem rho_add (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (R : ℕ)
    {X Y : Matrix (Fin n) (Fin N ⊕ Fin N) E} (hX : X ∈ cols Λ N) (hY : Y ∈ cols Λ N)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) : rho R (Y + X) φ = rho R Y (rho R X φ) := by
  funext x
  have p1 := phase_one hΛ (b := ((2 * R * R : ℕ) : E) • X.toCols₂) (y := Y.toCols₁)
    (colsIn_smul _ fun a => hX (Sum.inr a)) (fun a => hY (Sum.inl a))
  have p2 := phase_one hΛ (b := -(((2 * R * R : ℕ) : E) • Y.toCols₂)) (y := X.toCols₁)
    (fun a => Λ.neg_mem (colsIn_smul _ (fun a => hY (Sum.inr a)) a)) (fun a => hX (Sum.inl a))
  simp only [rho, heisH]
  rw [mul_assoc (φ _), ← Complex.exp_add, ← mul_one (cexp (_ + _)), ← p1, ← Complex.exp_add,
    ← mul_one (cexp (_ + _)), ← p2, ← Complex.exp_add]
  congr 1
  · congr 1
    ext k a
    simp [toCols₁]
    ring
  · congr 1
    rw [← mul_add, ← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Rat.cast_add,
      ← map_add, ← map_add, ← map_add]
    simp only [← Finset.sum_add_distrib]
    congr 3
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, toCols₁, toCols₂,
      Matrix.of_apply, Matrix.add_apply, cc_sub, cc_mul, cc_nat, cc_add]
    push_cast
    ring

theorem rho_sum {ι : Type} (s : Finset ι) (R : ℕ) (X : Matrix (Fin n) (Fin N ⊕ Fin N) E)
    (f : ι → Matrix (Fin n) (Fin N) E → ℂ) : rho R X (∑ i ∈ s, f i) = ∑ i ∈ s, rho R X (f i) := by
  funext x
  simp only [rho, heisH, Finset.sum_apply, Finset.sum_mul]

omit [IsCMField E] in
theorem colsIn_of_coprime {s t : ℕ} (h : s.Coprime t) {x : Matrix (Fin n) (Fin N) E}
    (h1 : ColsIn Λ ((s : E) • x)) (h2 : ColsIn Λ ((t : E) • x)) : ColsIn Λ x :=
  fun a => mem_of_coprime Λ h (h1 a) (h2 a)

omit [IsCMField E] in

theorem colsIn_transfer {s R m : ℕ} (hs : s.Coprime (m * R)) (h1 : ∀ v ∈ Λ, (s : E) • v ∈ Λ')
    {x : Matrix (Fin n) (Fin N) E} (hx : ColsIn Λ ((R : E) • x))
    (hx' : ColsIn Λ' (((m * R : ℕ) : E) • x)) : ColsIn Λ' ((R : E) • x) := by
  refine colsIn_of_coprime (Nat.Coprime.coprime_mul_right_right hs) (fun a => h1 _ (hx a)) ?_
  rwa [Nat.cast_mul, mul_smul] at hx'

open Classical in

theorem rho_apply (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R m : ℕ}
    (hs : s.Coprime (m * (2 * R))) (h1 : ∀ v ∈ Λ, (s : E) • v ∈ Λ')
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    {X : Matrix (Fin n) (Fin N ⊕ Fin N) E} (hX : X ∈ cols Λ' N) {x : Matrix (Fin n) (Fin N) E}
    (hx : ColsIn Λ (((m * (2 * R) : ℕ) : E) • x)) (hx' : ColsIn Λ' (((m * (2 * R) : ℕ) : E) • x)) :
    rho R X φ x = (if ColsIn Λ X.toCols₁ then 1 else 0) * φ x := by
  have hd' : ColsIn Λ' X.toCols₁ := fun a => hX (Sum.inl a)
  have hb' : ColsIn Λ' X.toCols₂ := fun a => hX (Sum.inr a)
  simp only [rho, heisH]
  split_ifs with hd
  · have e1 : φ (x - ((2 * R : ℕ) : E) • X.toCols₁) = φ x := by
      rw [← hφ.2 x (-(((2 : ℕ) : E) • X.toCols₁)) fun a => Λ.neg_mem (colsIn_smul 2 hd a)]
      congr 1
      rw [smul_neg, smul_smul, sub_eq_add_neg, Nat.cast_mul, mul_comm]
    rw [e1, one_mul]
    by_cases h0 : φ x = 0
    · rw [h0, zero_mul]
    have h3 : ColsIn Λ' ((R : E) • x) :=
      colsIn_transfer (m := m * 2) (by rwa [mul_assoc]) h1 (hφ.1 x h0) (by rwa [mul_assoc])
    have p := phase_one hΛ' hb' (y := ((2 : ℕ) : E) • ((R : E) • x) - ((2 * R * R : ℕ) : E) • X.toCols₁)
      fun a => Λ'.sub_mem (colsIn_smul 2 h3 a) (colsIn_smul _ hd' a)
    rw [← mul_one (φ x), mul_assoc, one_mul, ← p]
    congr 5
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, cc_sub, cc_mul, cc_nat]
    push_cast
    ring
  · rw [zero_mul, mul_eq_zero]
    left
    by_contra h0
    apply hd
    have h3 := colsIn_smul (m * 2) (hφ.1 _ h0)
    refine colsIn_of_coprime (t := (m * (2 * R)) * (2 * R))
      (Nat.Coprime.mul_right hs (Nat.Coprime.coprime_mul_left_right hs)) (fun a => h2 _ (hd' a))
      fun a => ?_
    convert Λ.sub_mem (hx a) (h3 a) using 1
    ext k
    simp
    ring

abbrev Quo (Λ : Lt E n) (N s : ℕ) : Type :=
  cols Λ N ⧸ ((cols Λ N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ N)

omit [IsCMField E] in
theorem mem_sub {s : ℕ} (x : cols Λ N) :
    x ∈ ((cols Λ N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ N) ↔
      ∃ y ∈ cols Λ N, (s : E) • y = x.1 := by
  simp [AddSubgroup.mem_addSubgroupOf, Nat.cast_smul_eq_nsmul]

theorem rho_congr (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R : ℕ}
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    (x y : cols Λ' N)
    (h : x - y ∈ ((cols Λ' N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ' N)) :
    rho R x.1 φ = rho R y.1 φ := by
  obtain ⟨z, hz, e⟩ := (mem_sub _).1 h
  have e1 : x.1 = y.1 + (x - y).1 := by simp
  have e2 : rho R (x - y).1 φ = φ := by
    rw [← e]
    exact heisH_fix hΛ hφ (fun a => h2 _ (hz (Sum.inl a))) (fun a => h2 _ (hz (Sum.inr a)))
  rw [e1, rho_add hΛ' R (x - y).2 y.2, e2]

omit [IsCMField E] in
theorem mul_mem_cols {X : Matrix (Fin n) (Fin N ⊕ Fin N) E} (hX : X ∈ cols Λ N) {g : M2 E N}
    (hg : IntM g) : X * g ∈ cols Λ N := fun i => by
  have := cols_mul (Λ := Λ) (d := X.toCols₁) (b := X.toCols₂) (fun a => hX (Sum.inl a))
    (fun a => hX (Sum.inr a)) hg i
  rwa [Matrix.fromCols_toCols] at this

theorem sum_rho_mul (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R c : ℕ} (hs0 : 0 < s)
    (hs : s.Coprime c) [Fintype (Quo Λ' N s)]
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    {g g' : M2 E N} (hg : IntM g) (hg' : IntM g') (e : g * g' = (c : E) • 1) :
    ∑ q : Quo Λ' N s, rho R (q.out.1 * g) φ = ∑ q : Quo Λ' N s, rho R q.out.1 φ := by
  refine sum_quot_comp _ (fun x : cols Λ' N => rho R x.1 φ) (rho_congr hΛ hΛ' h2 hφ)
    (fun x => ⟨x.1 * g, mul_mem_cols x.2 hg⟩) fun x y h => ?_
  obtain ⟨z, hz, ez⟩ := (mem_sub _).1 h
  have hsE : (s : E) ≠ 0 := by exact_mod_cast hs0.ne'
  refine (mem_sub _).2 ⟨(s : E)⁻¹ • (x - y).1, fun i => mem_of_coprime Λ' hs ?_ ?_,
    smul_inv_smul₀ hsE _⟩
  · have : (s : E) • ((s : E)⁻¹ • (x - y).1)ᵀ i = (x - y).1ᵀ i := smul_inv_smul₀ hsE _
    rw [this]; exact (x - y).2 i
  · have e3 : (s : E) • z = (x - y).1 * g := by
      rw [ez]; exact (Matrix.sub_mul _ _ _).symm
    have e4 : z * g' = (c : E) • (s : E)⁻¹ • (x - y).1 := by
      rw [smul_comm, eq_inv_smul_iff₀ hsE, ← Matrix.smul_mul, e3, Matrix.mul_assoc, e,
        Matrix.mul_smul, Matrix.mul_one]
    have := mul_mem_cols hz hg' i
    rwa [e4] at this

theorem levelL_sum (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R : ℕ} [Fintype (Quo Λ' N s)]
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ) :
    LevelL Λ' ((NumberField.discr E).natAbs * (2 * R)) (∑ q : Quo Λ' N s, rho R q.out.1 φ) := by
  refine levelL_of_fix hΛ' fun d b hd hb => ?_
  have hY : Matrix.fromCols d b ∈ cols Λ' N := by
    rintro (i | i)
    · exact hd i
    · exact hb i
  change rho R (Matrix.fromCols d b) _ = _
  rw [rho_sum, ← sum_quot_comp _ (fun x : cols Λ' N => rho R x.1 φ) (rho_congr hΛ hΛ' h2 hφ)
    (fun x => ⟨_, hY⟩ + x) fun x y h => by rwa [add_sub_add_left_eq_sub] at h]
  exact Finset.sum_congr rfl fun q _ => (rho_add hΛ' R q.out.2 hY φ).symm

omit [IsCMField E] in

theorem eq_of_agree {s L : ℕ} (hs : s.Coprime L) (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ' L φ) (hψ : LevelL Λ' L ψ)
    (h : ∀ x, ColsIn Λ ((L : E) • x) → ColsIn Λ' ((L : E) • x) → φ x = ψ x) : φ = ψ := by
  funext x
  by_cases hx : ColsIn Λ' ((L : E) • x)
  · obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) ((L * L : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_right hs hs)
    have hab' : (a : E) * s + b * (L * L) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    have z : ∀ (Γ : Lt E n) (k : ℤ) (y : Matrix (Fin n) (Fin N) E), ColsIn Γ y →
        ColsIn Γ ((k : E) • y) := fun Γ k y hy i => by
      have := Γ.toAddSubgroup.zsmul_mem (hy i) k
      rwa [← Int.cast_smul_eq_zsmul E] at this
    have hy := z Λ' (-b) _ hx
    have e : (L : E) • (x + (L : E) • ((-b : ℤ) : E) • (L : E) • x) =
        (a : E) • (s : E) • (L : E) • x := by
      ext k i
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      push_cast
      linear_combination (-(L : E) * x k i) * hab'
    rw [← hφ.2 x _ hy, ← hψ.2 x _ hy]
    refine h _ ?_ ?_ <;> rw [e]
    · exact z _ _ _ fun i => h2 _ (hx i)
    · exact z _ _ _ (colsIn_smul _ hx)
  · rw [not_not.1 fun h => hx (hφ.1 x h), not_not.1 fun h => hx (hψ.1 x h)]

omit [IsCMField E] in
theorem intM_mul {A B : M2 E N} (hA : IntM A) (hB : IntM B) : IntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]; exact IsIntegral.sum _ fun k _ => (hA i k).mul (hB k j)

omit [IsCMField E] in
theorem intM_J : IntM (Matrix.J (Fin N) E) := by
  rintro (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [Matrix.J, h, isIntegral_one, isIntegral_zero, isIntegral_one.neg]

omit [IsCMField E] in
theorem intM_nat (c : ℕ) : IntM ((c : E) • (1 : M2 E N)) := fun i j => by
  by_cases h : i = j <;> simp [h, isIntegral_zero, isIntegral_natCast]

end

end GlobalTheory.SW.WeilAdm

namespace GlobalTheory.SW

open WeilAdm WeilLevel Base in

theorem weil_admissible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ c R : ℕ, 0 < c → ∃ R' : ℕ, ∀ (M : ℕ) (φ : Fam E n N), admitted M R φ → ∀ γ ∈ UU E N, Den c γ → admitted M R' (fun Λ => weil Ψ γ (φ Λ)) := by
  classical
  intro E _ _ _ Ψ hΨ n N hn c R hc
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact ⟨1, fun M φ h => (lt_irrefl _ h.pos.2).elim⟩
  obtain ⟨R₀, C, hR₀, hlev⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hR
  have hD : 0 < (NumberField.discr E).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  set D := (NumberField.discr E).natAbs with hDdef
  refine ⟨c * D * (2 * (R₀ * R)), fun M φ hφ γ hγ hden => ?_⟩
  have l0 : ∀ Λ ∈ Vset E n M, LevelL Λ R (φ Λ) := fun Λ hΛ => ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩
  have sb : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := fun Λ hΛ => (hlev M Λ hΛ γ hγ hden _ (l0 Λ hΛ)).1
  have l1 : ∀ Λ ∈ Vset E n M, LevelL Λ (R₀ * R) (φ Λ) := fun Λ hΛ => levelL_mul (l0 Λ hΛ) _
  have l2 : ∀ Λ ∈ Vset E n M, LevelL Λ (R₀ * R) (weil Ψ γ (φ Λ)) := fun Λ hΛ => by
    rw [mul_comm]; exact levelL_mul (hlev M Λ hΛ γ hγ hden _ (l0 Λ hΛ)).2.1 _
  have up : ∀ (Λ : Lt E n) (f : Matrix (Fin n) (Fin N) E → ℂ), LevelL Λ (R₀ * R) f →
      LevelL Λ (c * D * (2 * (R₀ * R))) f := fun Λ f hf => by
    rw [← mul_assoc]; exact levelL_mul hf _
  refine ⟨⟨hφ.pos.1, by positivity⟩, fun h hh Λ hΛ Λ' hΛ' hm x => ?_,
    fun Λ hΛ => (up Λ _ (l2 Λ hΛ)).1, fun Λ hΛ => (up Λ _ (l2 Λ hΛ)).2, ?_⟩
  · have e : φ Λ = fun x => φ Λ' (h * x) := funext fun x => (hφ.equiv h hh Λ hΛ Λ' hΛ' hm x).symm
    change weil Ψ γ (φ Λ') (h * x) = weil Ψ γ (φ Λ) x
    rw [e]
    exact (congrFun ((GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup E Ψ hΨ n N hn h hh.1 _ (sb Λ' hΛ')).2.1 γ hγ) x).symm
  rintro Λ hΛ Λ' hΛ' ⟨s, hs0, hsM, h1, h2⟩ x hx hx'
  have hs : s.Coprime (c * D * (2 * (R₀ * R))) := Nat.Coprime.coprime_mul_right_right hsM
  have hsc : s.Coprime c := hs.of_dvd_right ⟨D * (2 * (R₀ * R)), by ring⟩
  have hag : Agree (R * M) Λ Λ' :=
    ⟨s, hs0, hsM.of_dvd_right ⟨c * D * (2 * R₀), by ring⟩, h1, h2⟩
  obtain ⟨t, ht0, -, ht, -⟩ := hΛ'.2.2
  haveI : Fintype (Quo Λ' N s) := by
    have := (relIndex_nsmul (cols Λ' N) ht0 (fun X hX k i => (mem_stdL _).1 (ht _ (hX i)) k) hs0).1
    haveI : Finite (Quo Λ' N s) := Nat.finite_of_card_ne_zero this
    exact Fintype.ofFinite _
  set κ : ℂ := ∑ q : Quo Λ' N s, if ColsIn Λ q.out.1.toCols₁ then 1 else 0 with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, Finset.sum_boole, Nat.cast_ne_zero, Finset.card_ne_zero]
    refine ⟨((0 : cols Λ' N) : Quo Λ' N s), Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a => ?_⟩⟩
    obtain ⟨y, hy, e⟩ := (mem_sub _).1 (QuotientAddGroup.eq_iff_sub_mem.1
      (QuotientAddGroup.out_eq' ((0 : cols Λ' N) : Quo Λ' N s)))
    rw [sub_zero] at e
    rw [← e]
    exact h2 _ (hy (Sum.inl a))
  have val : ∀ f : Matrix (Fin n) (Fin N) E → ℂ, LevelL Λ (R₀ * R) f → ∀ y,
      ColsIn Λ (((c * D * (2 * (R₀ * R)) : ℕ) : E) • y) →
      ColsIn Λ' (((c * D * (2 * (R₀ * R)) : ℕ) : E) • y) →
      (∑ q : Quo Λ' N s, rho (R₀ * R) q.out.1 f) y = κ * f y := fun f hf y hy hy' => by
    rw [Finset.sum_apply, hκ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => rho_apply hΛ'.2.1 hs h1 h2 hf q.out.2 hy hy'
  have main : ∑ q : Quo Λ' N s, rho (R₀ * R) q.out.1 (φ Λ) = κ • φ Λ' := by
    refine eq_of_agree hs h2 ?_ ?_ fun y hy hy' => ?_
    · rw [mul_assoc]; exact levelL_mul (levelL_sum hΛ.2.1 hΛ'.2.1 h2 (l1 Λ hΛ)) c
    · have := up _ _ (l1 Λ' hΛ')
      exact ⟨fun y hy => this.1 y (right_ne_zero_of_mul hy),
        fun y z hz => congrArg (κ * ·) (this.2 y z hz)⟩
    · rw [val _ (l1 Λ hΛ) y hy hy', Pi.smul_apply, smul_eq_mul]
      congr 1
      have e : c * D * (2 * (R₀ * R)) = c * D * (2 * R₀) * R := by ring
      rw [e] at hs hy hy'
      by_cases hR1 : ColsIn Λ ((R : E) • y)
      · exact hφ.loc Λ hΛ Λ' hΛ' hag y hR1 (colsIn_transfer hs h1 hR1 hy')
      · rw [not_not.1 fun h => hR1 (hφ.supp Λ hΛ y h),
          not_not.1 fun h => hR1 (colsIn_transfer hs h2 (hφ.supp Λ' hΛ' y h) hy)]
  obtain ⟨hdet, -, -, hinv, -⟩ := (GlobalTheory.T.unitary_act_halfSpace_alt E Ψ N γ hγ).1
  have hden' : IntM ((c : E) • γ⁻¹) := by
    have e : (c : E) • γ⁻¹ = -(Matrix.J (Fin N) E * ccT ((c : E) • γ) * Matrix.J (Fin N) E) := by
      have : ccT ((c : E) • γ) = (c : E) • ccT γ := by
        ext i j; simp [ccT, cc_mul, cc_nat]
      rw [hinv, this, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    rw [e]
    exact fun i j => (intM_mul (intM_mul intM_J fun i j => isIntegral_cc (hden j i)) intM_J i j).neg
  have hscc : s.Coprime (c * c) := Nat.Coprime.mul_right hsc hsc
  have s1 := sum_rho_mul hΛ.2.1 hΛ'.2.1 hs0 hscc h2 (l1 Λ hΛ) hden hden' (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hdet, Nat.cast_mul])
  have s2 := sum_rho_mul hΛ.2.1 hΛ'.2.1 hs0 hscc h2 (l2 Λ hΛ) (intM_nat c) (intM_nat c) (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Nat.cast_mul])
  have term : ∀ X : Matrix (Fin n) (Fin N ⊕ Fin N) E, IsSB (rho (R₀ * R) (X * ((c : E) • γ)) (φ Λ)) ∧
      weil Ψ γ (rho (R₀ * R) (X * ((c : E) • γ)) (φ Λ)) =
        rho (R₀ * R) (X * ((c : E) • (1 : M2 E N))) (weil Ψ γ (φ Λ)) := fun X => by
    obtain ⟨a1, -, a2⟩ := GlobalTheory.T.hermitianHeisenbergOperator_laws E Ψ hΨ n N hn
      (((2 * (R₀ * R) : ℕ) : E) • (X * ((c : E) • γ)).toCols₁)
      (((2 * (R₀ * R) : ℕ) : E) • (X * ((c : E) • γ)).toCols₂) _ (sb Λ hΛ)
    refine ⟨a1, (a2 γ hγ).trans ?_⟩
    have h4 : ∀ Y : Matrix (Fin n) (Fin N ⊕ Fin N) E,
        Matrix.fromCols (((2 * (R₀ * R) : ℕ) : E) • Y.toCols₁)
          (((2 * (R₀ * R) : ℕ) : E) • Y.toCols₂) = ((2 * (R₀ * R) : ℕ) : E) • Y := fun Y => by
      ext k (j | j) <;> rfl
    rw [h4, Matrix.smul_mul, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hdet]
    rfl
  have wsum : ∀ (u : Finset (Quo Λ' N s)) (f : Quo Λ' N s → Matrix (Fin n) (Fin N) E → ℂ),
      (∀ q, IsSB (f q)) → IsSB (∑ q ∈ u, f q) ∧
        weil Ψ γ (∑ q ∈ u, f q) = ∑ q ∈ u, weil Ψ γ (f q) := fun u f hf => by
    induction u using Finset.induction_on with
    | empty =>
      have := (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ 0 isSB_zero).2.2.2.2.1 0
      rw [zero_smul, zero_smul] at this
      exact ⟨isSB_zero, this⟩
    | insert q u hq ih =>
      rw [Finset.sum_insert hq, Finset.sum_insert hq, ← ih.2]
      exact ⟨isSB_add (hf q) ih.1, ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (hf q)).2.2.2.1 _ ih.1).2⟩
  have fin := (wsum Finset.univ _ fun q => (term q.out.1).1).2
  simp only [fun X => (term X).2] at fin
  rw [s1, s2, main, (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (sb Λ' hΛ')).2.2.2.2.1 κ] at fin
  have fin2 := congrFun fin x
  rw [val _ (l2 Λ hΛ) x hx hx', Pi.smul_apply, smul_eq_mul] at fin2
  exact (mul_left_cancel₀ hκ0 fin2).symm

end GlobalTheory.SW
