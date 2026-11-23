import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LocLanglands.SphFac
open GlobalTheory.SplitRead GlobalTheory.StepData GlobalTheory.SmGL.DepthZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

private theorem exists_KO_eq_one_add_of_sq_eq_zero (N : Matrix n n k) (hN : IntM N) (h2 : N * N = 0) :
    ∃ κ ∈ KO k n, κ.val = 1 + N := by
  let κ : GL n k := ⟨1 + N, 1 - N, by rw [mul_sub, mul_one, add_mul, one_mul, h2]; simp,
    by rw [sub_mul, one_mul, mul_add, mul_one, h2]; simp⟩
  refine ⟨κ, GlobalTheory.StepData.mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩, rfl⟩
  · show (1 + N) i j ∈ 𝒪[k]
    rw [Matrix.add_apply, Matrix.one_apply]
    exact add_mem (by split_ifs <;> simp) (hN i j)
  · show (1 - N) i j ∈ 𝒪[k]
    rw [Matrix.sub_apply, Matrix.one_apply]
    exact sub_mem (by split_ifs <;> simp) (hN i j)

private theorem vv_pow_smul_mem_of_sen_eq_zero (C : Finset n) (i0 : n) (hi0 : i0 ∈ C) (X : Matrix n n k)
    (h1 : ∀ i ∉ C, ∀ j ∈ C, X i j = 0) :
    ∃ κ ∈ KO k n, (∀ i ∉ C, ∀ j, (X * κ.val) i j = X i j) ∧ ∀ j ∈ C, j ≠ i0 → (X * κ.val) i0 j = 0 := by
  have keep : ∀ (Y N : Matrix n n k), (∀ i ∉ C, ∀ j ∈ C, Y i j = 0) → (∀ l j, l ∉ C → N l j = 0) →
      ∀ i ∉ C, ∀ j, (Y * (1 + N)) i j = Y i j := by
    intro Y N hY hN i hi j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    by_cases hl : l ∈ C
    · rw [hY i hi l hl, zero_mul]
    · rw [hN l j hl, mul_zero]
  have rowf : ∀ (Y N : Matrix n n k) (j : n), (Y * (1 + N)) i0 j = Y i0 j + ∑ l, Y i0 l * N l j := by
    intro Y N j
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  obtain ⟨c, hc, hcmax⟩ := Finset.exists_max_image C (fun j => valuation k (X i0 j)) ⟨i0, hi0⟩
  classical
  let P : Prop := c ≠ i0 ∧ valuation k (X i0 i0) < valuation k (X i0 c)
  let N1 : Matrix n n k := Matrix.of fun l j => if l = c ∧ j = i0 ∧ P then 1 else 0
  have hN1s : ∀ l j, l ∉ C → N1 l j = 0 := by
    intro l j hl
    have : ¬ (l = c ∧ j = i0 ∧ P) := fun h => hl (h.1 ▸ hc)
    simp only [N1, Matrix.of_apply, if_neg this]
  have hN1i : IntM N1 := by
    intro l j
    simp only [N1, Matrix.of_apply]
    split_ifs <;> simp
  have hN1sq : N1 * N1 = 0 := by
    ext l j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [N1, Matrix.of_apply]
    split_ifs with ha hb
    · exact absurd (hb.1.symm.trans ha.2.1) ha.2.2.1
    all_goals simp
  obtain ⟨κ1, hκ1, hκ1v⟩ := exists_KO_eq_one_add_of_sq_eq_zero N1 hN1i hN1sq
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X * (1 + N1) := ⟨_, rfl⟩
  have hYkeep : ∀ i ∉ C, ∀ j, Y i j = X i j := fun i hi j => by rw [hY]; exact keep X N1 h1 hN1s i hi j
  have hY1 : ∀ i ∉ C, ∀ j ∈ C, Y i j = 0 := fun i hi j hj => by rw [hYkeep i hi j]; exact h1 i hi j hj
  have hYrow : ∀ j, Y i0 j = X i0 j + if j = i0 ∧ P then X i0 c else 0 := by
    intro j
    rw [hY, rowf]
    congr 1
    by_cases hj : j = i0 ∧ P
    · rw [if_pos hj, Finset.sum_eq_single c]
      · show X i0 c * (if c = c ∧ j = i0 ∧ P then (1 : k) else 0) = X i0 c
        rw [if_pos ⟨rfl, hj.1, hj.2⟩, mul_one]
      · intro l _ hl
        simp only [N1, Matrix.of_apply, if_neg (fun h : l = c ∧ j = i0 ∧ P => hl h.1), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c) h
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [N1, Matrix.of_apply, if_neg (fun h : l = c ∧ j = i0 ∧ P => hj ⟨h.2.1, h.2.2⟩), mul_zero]
  have hYmax : ∀ j ∈ C, valuation k (Y i0 j) ≤ valuation k (Y i0 i0) := by
    intro j hj
    by_cases hP : P
    · have e0 : Y i0 i0 = X i0 i0 + X i0 c := by rw [hYrow, if_pos ⟨rfl, hP⟩]
      have hv0 : valuation k (Y i0 i0) = valuation k (X i0 c) := by
        rw [e0]; exact (valuation k).map_add_eq_of_lt_right hP.2
      rw [hv0]
      by_cases hji : j = i0
      · rw [hji, hv0]
      · rw [hYrow, if_neg (fun h => hji h.1), add_zero]; exact hcmax j hj
    · have e : ∀ j, Y i0 j = X i0 j := fun j => by rw [hYrow, if_neg (fun h => hP h.2), add_zero]
      rw [e, e]
      refine (hcmax j hj).trans ?_
      by_cases hci : c = i0
      · rw [hci]
      · exact not_lt.1 fun h => hP ⟨hci, h⟩
  let N2 : Matrix n n k := Matrix.of fun l j => if l = i0 ∧ j ∈ C ∧ j ≠ i0 then -(Y i0 j / Y i0 i0) else 0
  have hN2s : ∀ l j, l ∉ C → N2 l j = 0 := by
    intro l j hl
    have : ¬ (l = i0 ∧ j ∈ C ∧ j ≠ i0) := fun h => hl (h.1 ▸ hi0)
    simp only [N2, Matrix.of_apply, if_neg this]
  have hN2i : IntM N2 := by
    intro l j
    simp only [N2, Matrix.of_apply]
    split_ifs with h
    · refine neg_mem ?_
      by_cases hz : Y i0 i0 = 0
      · rw [hz, div_zero]; exact zero_mem _
      · refine (Valuation.mem_integer_iff _ _).2 ?_
        rw [map_div₀]
        exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz))).2 (hYmax j h.2.1)
    · exact zero_mem _
  have hN2sq : N2 * N2 = 0 := by
    ext l j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [N2, Matrix.of_apply]
    split_ifs with ha hb
    · exact absurd hb.1 ha.2.2
    all_goals simp
  obtain ⟨κ2, hκ2, hκ2v⟩ := exists_KO_eq_one_add_of_sq_eq_zero N2 hN2i hN2sq
  refine ⟨κ1 * κ2, mul_mem hκ1 hκ2, fun i hi j => ?_, fun j hj hji => ?_⟩
  · rw [Units.val_mul, hκ1v, hκ2v, ← Matrix.mul_assoc, ← hY, keep Y N2 hY1 hN2s i hi j, hYkeep i hi j]
  · rw [Units.val_mul, hκ1v, hκ2v, ← Matrix.mul_assoc, ← hY, rowf, Finset.sum_eq_single i0]
    · show Y i0 j + Y i0 i0 * (if i0 = i0 ∧ j ∈ C ∧ j ≠ i0 then -(Y i0 j / Y i0 i0) else 0) = 0
      rw [if_pos ⟨rfl, hj, hji⟩]
      by_cases hz : Y i0 i0 = 0
      · have hj0 : Y i0 j = 0 := by
          have h := hYmax j hj
          rw [hz, map_zero, le_zero_iff, Valuation.zero_iff] at h
          exact h
        rw [hj0, hz]
        simp
      · rw [mul_neg, mul_div_cancel₀ _ hz, add_neg_cancel]
    · intro l _ hl
      simp only [N2, Matrix.of_apply, if_neg (fun h : l = i0 ∧ j ∈ C ∧ j ≠ i0 => hl h.1), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem exists_KO_mul_eq_zero_below_order (β : n → α) : ∀ (C : Finset n), (∀ i ∉ C, ∀ j ∈ C, β j ≤ β i) →
    ∀ X : Matrix n n k, (∀ i ∉ C, ∀ j ∈ C, X i j = 0) → (∀ i ∉ C, ∀ j ∉ C, β j < β i → X i j = 0) →
    ∃ κ ∈ KO k n, ∀ i j, β j < β i → (X * κ.val) i j = 0 := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro h3 X h1 h2
    rcases C.eq_empty_or_nonempty with hC | hC
    · subst hC
      exact ⟨1, one_mem _, fun i j hij => by
        rw [Units.val_one, Matrix.mul_one]; exact h2 i (by simp) j (by simp) hij⟩
    obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image C β hC
    obtain ⟨κ1, hκ1, hrow, hzero⟩ := vv_pow_smul_mem_of_sen_eq_zero C i0 hi0 X h1
    have hne : ∀ i, i ∉ C.erase i0 → i ≠ i0 → i ∉ C := fun i hi hii h => hi (Finset.mem_erase.2 ⟨hii, h⟩)
    have h3' : ∀ i ∉ C.erase i0, ∀ j ∈ C.erase i0, β j ≤ β i := by
      intro i hi j hj
      by_cases hii : i = i0
      · rw [hii]; exact hmax j (Finset.mem_of_mem_erase hj)
      · exact h3 i (hne i hi hii) j (Finset.mem_of_mem_erase hj)
    have h1' : ∀ i ∉ C.erase i0, ∀ j ∈ C.erase i0, (X * κ1.val) i j = 0 := by
      intro i hi j hj
      by_cases hii : i = i0
      · rw [hii]; exact hzero j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
      · rw [hrow i (hne i hi hii) j]; exact h1 i (hne i hi hii) j (Finset.mem_of_mem_erase hj)
    have h2' : ∀ i ∉ C.erase i0, ∀ j ∉ C.erase i0, β j < β i → (X * κ1.val) i j = 0 := by
      intro i hi j hj hij
      by_cases hii : i = i0
      · exfalso
        rw [hii] at hij
        by_cases hjj : j = i0
        · rw [hjj] at hij; exact lt_irrefl _ hij
        · exact not_lt.2 (h3 j (hne j hj hjj) i0 hi0) hij
      · rw [hrow i (hne i hi hii) j]
        by_cases hjj : j = i0
        · rw [hjj]; exact h1 i (hne i hi hii) i0 hi0
        · exact h2 i (hne i hi hii) j (hne j hj hjj) hij
    obtain ⟨κ2, hκ2, hT⟩ := ih (C.erase i0) (Finset.erase_ssubset hi0) h3' (X * κ1.val) h1' h2'
    refine ⟨κ1 * κ2, mul_mem hκ1 hκ2, fun i j hij => ?_⟩
    rw [Units.val_mul, ← Matrix.mul_assoc]
    exact hT i j hij

private theorem exists_parab_mul_KO_eq (e : (Σ a, m a) ≃ n) (x : GL n k) :
    ∃ p ∈ parab k e, ∃ κ ∈ KO k n, x = p * κ := by
  obtain ⟨κ, hκ, hT⟩ := exists_KO_mul_eq_zero_below_order (blk e) Finset.univ (by simp) x.val (by simp) (by simp)
  refine ⟨x * κ, mem_parab.2 fun i j hij => ?_, κ⁻¹, inv_mem hκ, (mul_inv_cancel_right x κ).symm⟩
  rw [Units.val_mul]
  exact hT i j hij

private theorem exists_fixed_ne_zero_of_piTensor_fixed {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (K : ∀ a, Subgroup (Γ a))
    {w : PiTensorProduct ℂ X} (hw0 : w ≠ 0) (hw : ∀ g : ∀ a, Γ a, (∀ a, g a ∈ K a) → piTensor ρ g w = w)
    (a : α) : ∃ v ∈ fixed (ρ a) (K a), v ≠ 0 := by
  let B : ∀ b, Module.Basis _ ℂ (X b) := fun b => Module.Basis.ofVectorSpace ℂ (X b)
  let Bt := Basis.piTensorProduct B
  obtain ⟨t, ht⟩ : ∃ t, Bt.repr w t ≠ 0 := by
    by_contra hcon
    apply hw0
    have : Bt.repr w = 0 := Finsupp.ext fun t => by
      by_contra h
      exact hcon ⟨t, h⟩
    simpa using congrArg Bt.repr.symm this
  let S : Finset α := Finset.univ.erase a
  have hSne : ∀ b ∈ S, b ≠ a := fun b hb => Finset.ne_of_mem_erase hb
  have hSmem : ∀ b, b ≠ a → b ∈ S := fun b hb => Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩
  let C : MultilinearMap ℂ X (X a) :=
    { toFun := fun x => (∏ b ∈ S, (B b).repr (x b) (t b)) • x a
      map_update_add' := by
        intro _ x i y z
        by_cases hi : i = a
        · subst hi
          have hp : ∀ [DecidableEq α] (u : X i),
              (∏ b ∈ S, (B b).repr (Function.update x i u b) (t b)) =
              ∏ b ∈ S, (B b).repr (x b) (t b) := fun u =>
            Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (hSne b hb)]
          rw [hp, hp, hp, Function.update_self, Function.update_self, Function.update_self, smul_add]
        · have hia : i ∈ S := hSmem i hi
          have hp : ∀ [DecidableEq α] (u : X i),
              (∏ b ∈ S, (B b).repr (Function.update x i u b) (t b)) =
              (B i).repr u (t i) * ∏ b ∈ S.erase i, (B b).repr (x b) (t b) := by
            intro _ u
            rw [← Finset.mul_prod_erase _ _ hia, Function.update_self]
            congr 1
            exact Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          rw [hp, hp, hp, Function.update_of_ne (Ne.symm hi), Function.update_of_ne (Ne.symm hi),
            Function.update_of_ne (Ne.symm hi), map_add, Finsupp.add_apply, add_mul, add_smul]
      map_update_smul' := by
        intro _ x i c y
        by_cases hi : i = a
        · subst hi
          have hp : ∀ [DecidableEq α] (u : X i),
              (∏ b ∈ S, (B b).repr (Function.update x i u b) (t b)) =
              ∏ b ∈ S, (B b).repr (x b) (t b) := fun u =>
            Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (hSne b hb)]
          rw [hp, hp, Function.update_self, Function.update_self, smul_comm]
        · have hia : i ∈ S := hSmem i hi
          have hp : ∀ [DecidableEq α] (u : X i),
              (∏ b ∈ S, (B b).repr (Function.update x i u b) (t b)) =
              (B i).repr u (t i) * ∏ b ∈ S.erase i, (B b).repr (x b) (t b) := by
            intro _ u
            rw [← Finset.mul_prod_erase _ _ hia, Function.update_self]
            congr 1
            exact Finset.prod_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
          rw [hp, hp, Function.update_of_ne (Ne.symm hi), Function.update_of_ne (Ne.symm hi), map_smul,
            Finsupp.smul_apply, smul_eq_mul, mul_assoc, mul_smul] }
  let C' := PiTensorProduct.lift C
  have hC : ∀ y, C' y = 0 → (Bt.repr y) t = 0 := by
    intro y hy
    have key : ∀ y, (B a).repr (C' y) (t a) = Bt.repr y t := by
      intro y
      induction y using PiTensorProduct.induction_on with
      | smul_tprod r x =>
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        congr 1
        simp only [C', PiTensorProduct.lift.tprod, Bt, Basis.piTensorProduct_repr_tprod_apply]
        show (B a).repr ((∏ b ∈ S, (B b).repr (x b) (t b)) • x a) (t a) = _
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ a)
      | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
    rw [← key, hy, map_zero, Finsupp.zero_apply]
  have hequi : ∀ (κ : Γ a) y, C' (piTensor ρ (Pi.mulSingle a κ) y) = ρ a κ (C' y) := by
    intro κ y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      simp only [map_smul, piTensor_tprod, C', PiTensorProduct.lift.tprod]
      congr 1
      show (∏ b ∈ S, (B b).repr (ρ b (Pi.mulSingle a κ b) (x b)) (t b)) •
          ρ a (Pi.mulSingle a κ a) (x a) = ρ a κ ((∏ b ∈ S, (B b).repr (x b) (t b)) • x a)
      rw [Pi.mulSingle_eq_same, map_smul]
      congr 1
      exact Finset.prod_congr rfl fun b hb => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb), map_one, Module.End.one_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  refine ⟨C' w, GlobalTheory.Parabolic.mem_fixed.2 fun κ hκ => ?_, fun h => ht (hC w h)⟩
  rw [← hequi]
  congr 1
  refine hw _ fun b => ?_
  by_cases hb : b = a
  · subst hb; simpa using hκ
  · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

theorem leviEmb_mem_KO' (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KO k (m a)) :
    leviEmb k e g ∈ KO k n :=
  GlobalTheory.LocGL.leviEmb_mem_KO e ((Subgroup.mem_pi _).2 fun a _ => hg a)

theorem deltaHalf_eq_one_of_KO {g : Levi k m} (hg : ∀ a, g a ∈ KO k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  ext
  rw [val_absPow, GlobalTheory.LGrp.nabs_det_of_mem_KO (hg a)]
  simp

theorem exists_fixed_of_parInd_KO (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KO k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KO k (m a)) → ρ g w = w := by
  have hfix : ∀ κ ∈ KO k n, ∀ x, f.1.1 (x * κ) = f.1.1 x := by
    intro κ hκ x
    rw [← parInd_apply e ρ κ x f, GlobalTheory.Parabolic.mem_fixed.1 hf κ hκ]
  refine ⟨f.1.1 1, fun h1 => h0 ?_, fun g hg => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    obtain ⟨p, hp, κ, hκ, rfl⟩ := exists_parab_mul_KO_eq e x
    have h2 := parInd_law e ρ f ⟨p, hp⟩ κ
    have h3 : f.1.1 κ = 0 := by simpa [h1] using hfix κ hκ 1
    show f.1.1 (p * κ) = 0
    rw [show p * κ = ((⟨p, hp⟩ : parab k e) : GL n k) * κ from rfl, h2, h3, map_zero, smul_zero]
  · have h1 := parInd_law e ρ f ⟨leviEmb k e g, leviEmb_mem_parab k e g⟩ 1
    have h2 : f.1.1 (leviEmb k e g) = f.1.1 1 := by simpa using hfix _ (leviEmb_mem_KO' e hg) 1
    simp only [mul_one, leviProj_leviEmb, deltaHalf_eq_one_of_KO hg, Units.val_one, one_smul] at h1
    rw [← h1, h2]

set_option maxHeartbeats 1000000 in
private theorem exists_parInd_fixed_ne_zero_of_subquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : GlobalTheory.SmGL.IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KO k n), v ≠ 0) :
    ∃ f ∈ fixed (parInd e (piTensor σ)) (KO k n), f ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := hv
  have hK : IsCompact (KO k n : Set (GL n k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hρ : IsSmooth (multiProd e σ) := isSmooth_parInd e _
  have hπ : IsSmooth π := GlobalTheory.SmGL.IsSubquotient.isSmooth h hρ
  obtain ⟨S, f, hf⟩ := h
  have hS : IsSmooth S.toRepresentation := by
    intro x
    have : {g | S.toRepresentation g x = x} = {g | (multiProd e σ) g x.1 = x.1} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hρ x.1
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨u', hu'⟩ : ∃ u', u' = GlobalTheory.LocGL.idem hS hK u := ⟨_, rfl⟩
  have hu'fix : u' ∈ fixed S.toRepresentation (KO k n) := hu' ▸ GlobalTheory.LocGL.idem_mem hS hK u
  have hfu'fix : f u' ∈ fixed π (KO k n) := GlobalTheory.Parabolic.mem_fixed.2 fun κ hκ => by
    rw [← f.isIntertwining, GlobalTheory.Parabolic.mem_fixed.1 hu'fix κ hκ]
  have hmap : ∀ y ∈ twKer S.toRepresentation (KO k n) 1, f y ∈ twKer π (KO k n) 1 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => f y ∈ twKer π (KO k n) 1) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨κ, x, rfl⟩
      refine Submodule.subset_span ⟨κ, f x, ?_⟩
      rw [map_sub, map_smul, f.isIntertwining]
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have h1 : u - u' ∈ twKer S.toRepresentation (KO k n) 1 := by
    rw [← GlobalTheory.LocGL.idem_eq_zero_iff hS hK, map_sub, GlobalTheory.LocGL.idem_of_mem hS hK hu'fix, ← hu', sub_self]
  have h2 : f u - f u' ∈ twKer π (KO k n) 1 := map_sub f u u' ▸ hmap _ h1
  have h4 : f u - f u' = 0 :=
    Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hπ hK).disjoint _ (sub_mem hv hfu'fix) h2
  have hfu : f u' = f u := (sub_eq_zero.1 h4).symm
  have hu'0 : u' ≠ 0 := fun h0 => hv0 (by rw [← hfu, h0, map_zero])
  have hfixI : (u' : IndSp e (piTensor σ)) ∈ fixed (parInd e (piTensor σ)) (KO k n) :=
    GlobalTheory.Parabolic.mem_fixed.2 fun κ hκ => by
      have happ : ((S.toRepresentation κ u' : S.toSubmodule) : IndSp e (piTensor σ)) = parInd e (piTensor σ) κ u' := rfl
      rw [← happ, GlobalTheory.Parabolic.mem_fixed.1 hu'fix κ hκ]
  exact ⟨_, hfixI, fun h0 => hu'0 (Subtype.ext h0)⟩

theorem fixed_KO_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : GlobalTheory.SmGL.IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KO k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KO k (m a)), v ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := exists_parInd_fixed_ne_zero_of_subquotient e σ h hv
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd_KO e (piTensor σ) hf hf0
  exact exists_fixed_ne_zero_of_piTensor_fixed σ (fun a => KO k (m a)) hw0 hw a

theorem isSpherical_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsSubquotient π (prodIrr x hd) → IsSpherical π → ∀ a, IsSpherical (x a).rep := by
  intro k _ _ _ _ _ h N x hd V _ _ π hsub hsph a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
  obtain ⟨w, hw, hw0⟩ := fixed_KO_of_isSubquotient (stdBlocks (fun a => (x a).1) hd) (fun a => (x a).rep) hsub
    ⟨v, hv, hv0⟩ a
  exact (Submodule.ne_bot_iff _).2 ⟨w, hw, hw0⟩

end GlobalTheory.LocLanglands.SphFac
end
