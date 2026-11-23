import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgSmul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem ex_add' {n : ℕ} (x y : Wt n) : ex (x + y) = ex x * ex y := (UpperTheory.RealTr.cfBasic n).1 x y

private theorem ex_zero' {n : ℕ} : ex (0 : Wt n) = 1 := (UpperTheory.RealTr.cfBasic n).2.1

private theorem fr_ext {n : ℕ} (f g : FR n) (h : ∀ x, cf f x = cf g x) : f = g :=
  (UpperTheory.RealTr.cfBasic n).2.2.1 f g h

private theorem cf_add' {n : ℕ} (f g : FR n) (x : Wt n) : cf (f + g) x = cf f x + cf g x :=
  ((UpperTheory.RealTr.cfBasic n).2.2.2.1 f g 0 x).1

private theorem cf_smul' {n : ℕ} (c : ℂ) (f : FR n) (x : Wt n) : cf (c • f) x = c * cf f x :=
  ((UpperTheory.RealTr.cfBasic n).2.2.2.1 f f c x).2

private theorem cf_zero' {n : ℕ} (x : Wt n) : cf (0 : FR n) x = 0 := by
  have := cf_smul' (0 : ℂ) (0 : FR n) x
  simpa using this

private theorem cf_sum' {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → FR n) (x : Wt n) :
    cf (∑ i ∈ s, f i) x = ∑ i ∈ s, cf (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf_zero']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cf_add', ih]

private theorem cf_ex {n : ℕ} (y x : Wt n) : cf (ex y) x = if y = x then 1 else 0 := by
  classical
  simp [cf, ex, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private theorem ex_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Wt n) :
    ∏ i ∈ s, ex (f i) = ex (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ex_add']

private theorem wtB_sum {n : ℕ} (B : Finset (Fin n × Fin n)) : wtB B = ∑ p ∈ B, rt p.1 p.2 := by
  funext c
  simp only [wtB, rt, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply]
  simp [Finset.sum_boole, eq_comm]

private theorem wtB_pos (n : ℕ) : wtB (posP n) = (2 : ℝ) • rhoV n := by
  funext c
  have h1 : ((posP n).filter fun p => p.1 = c).card = n - 1 - (c : ℕ) := by
    have : ((posP n).filter fun p => p.1 = c) = (Finset.Ioi c).image (fun b => (c, b)) := by
      ext ⟨a, b⟩
      simp [posP]
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Fin.card_Ioi]
  have h2 : ((posP n).filter fun p => p.2 = c).card = (c : ℕ) := by
    have : ((posP n).filter fun p => p.2 = c) = (Finset.Iio c).image (fun a => (a, c)) := by
      ext ⟨a, b⟩
      simp [posP]
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
    rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Fin.card_Iio]
  have hc : (c : ℕ) + 1 ≤ n := c.2
  have h3 : ((n - 1 - (c : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (c : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [wtB, h1, h2, h3, Pi.smul_apply, smul_eq_mul, rhoV]
  ring

private theorem chR_eq (n : ℕ) : chR n = ∑ B ∈ (posP n).powerset, ex (rhoV n - wtB B) := by
  rw [chR, Finset.prod_one_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [ex_sum, ← ex_add', wtB_sum, Finset.sum_neg_distrib, sub_eq_add_neg]

private def tw {n : ℕ} (w : Equiv.Perm (Fin n)) : FR n →ₐ[ℂ] FR n :=
  AddMonoidAlgebra.lift ℂ (FR n) (Wt n)
    { toFun := fun x => ex (x.toAdd ∘ w)
      map_one' := ex_zero'
      map_mul' := fun x y => by rw [← ex_add']; rfl }

private theorem tw_ex {n : ℕ} (w : Equiv.Perm (Fin n)) (y : Wt n) : tw w (ex y) = ex (y ∘ w) := by
  simp [tw, ex, AddMonoidAlgebra.lift_single]

private theorem cf_tw {n : ℕ} (w : Equiv.Perm (Fin n)) (f : FR n) (x : Wt n) :
    cf (tw w f) (x ∘ w) = cf f x := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [cf_zero']
  | add f g hf hg => rw [map_add, cf_add', cf_add', hf, hg]
  | single a b =>
    have h : AddMonoidAlgebra.single a b = b • (ex a : FR n) := by simp [ex]
    rw [h, map_smul, cf_smul', cf_smul', tw_ex, cf_ex, cf_ex]
    simp [w.surjective.injective_comp_right.eq_iff]

private theorem sg_ne {n : ℕ} (w : Equiv.Perm (Fin n)) : sg w ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [sg, h]

private theorem tw_asym {n : ℕ} (w : Equiv.Perm (Fin n)) (g : FR n) (hg : ASym g) :
    tw w g = sg w⁻¹ • g := by
  refine fr_ext _ _ fun x => ?_
  have h1 := cf_tw w g (x ∘ (w⁻¹ : Equiv.Perm (Fin n)))
  have h2 := hg w⁻¹ x
  have h3 : (x ∘ (w⁻¹ : Equiv.Perm (Fin n))) ∘ w = x := by funext a; simp
  rw [h3] at h1
  rw [h1, cf_smul', h2]

private theorem sym_of_mul {n : ℕ} (d e h : FR n) (hd : ASym d) (he : ASym e) (hd0 : d ≠ 0)
    (hm : e = d * h) : Sym h := by
  intro w x
  have h1 : tw w e = tw w d * tw w h := by rw [hm, map_mul]
  rw [tw_asym w e he, tw_asym w d hd, hm, smul_mul_assoc] at h1
  have h2 : d * h = d * tw w h := smul_right_injective _ (sg_ne w⁻¹) h1
  have h3 : h = tw w h := mul_left_cancel₀ hd0 h2
  conv_lhs => rw [h3]
  exact cf_tw w h x

private theorem alt_ne {n : ℕ} (x : Wt n) (hx : StrictAnti x) : alt x ≠ 0 := by
  intro h
  have := ((UpperTheory.RealTr.cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 x hx).1
  rw [h, cf_zero'] at this
  exact zero_ne_one this

private theorem denom_mul (n : ℕ) : alt ((2 : ℝ) • rhoV n) = alt (rhoV n) * chR n := by
  have h2 := UpperTheory.RealTr.denom n 2
  have h1 := UpperTheory.RealTr.denom n 1
  simp only [one_smul] at h1
  rw [h2, h1, chR]
  have e : ex ((2 : ℝ) • rhoV n) = ex (rhoV n) * ex (rhoV n) := by
    rw [← ex_add', two_smul]
  have f : ∀ p ∈ posP n, (1 - ex (-((2 : ℝ) • rt p.1 p.2)) : FR n) =
      (1 - ex (-rt p.1 p.2)) * (1 + ex (-rt p.1 p.2)) := by
    intro p _
    have : ex (-((2 : ℝ) • rt p.1 p.2)) = ex (-rt p.1 p.2) * ex (-rt p.1 p.2) := by
      rw [← ex_add', two_smul, neg_add]
    rw [this]; ring
  rw [Finset.prod_congr rfl f, Finset.prod_mul_distrib, e]
  ring

private theorem even_chR (n : ℕ) (x : Wt n) : cf (chR n) (-x) = cf (chR n) x := by
  classical
  rw [chR_eq, cf_sum', cf_sum']
  refine Finset.sum_nbij' (fun B => posP n \ B) (fun B => posP n \ B) ?_ ?_ ?_ ?_ ?_
  · intro B _; simp
  · intro B _; simp
  · intro B hB; simpa using Finset.inter_eq_right.2 (Finset.mem_powerset.1 hB)
  · intro B hB; simpa using Finset.inter_eq_right.2 (Finset.mem_powerset.1 hB)
  · intro B hB
    have hs : wtB (posP n \ B) + wtB B = (2 : ℝ) • rhoV n := by
      rw [← wtB_pos, wtB_sum, wtB_sum, wtB_sum]
      exact Finset.sum_sdiff (Finset.mem_powerset.1 hB)
    have hy : rhoV n - wtB (posP n \ B) = -(rhoV n - wtB B) := by
      have : wtB (posP n \ B) = (2 : ℝ) • rhoV n - wtB B := eq_sub_of_add_eq hs
      rw [this, two_smul]; abel
    have hi : (rhoV n - wtB B = -x) ↔ (-(rhoV n - wtB B) = x) :=
      ⟨fun e => by rw [e, neg_neg], fun e => by rw [← e, neg_neg]⟩
    rw [hy, cf_ex, cf_ex]
    simp only [hi]

private theorem supp_chR (n : ℕ) (x : Wt n) (h : cf (chR n) x ≠ 0) :
    ∃ B ⊆ posP n, x = rhoV n - wtB B := by
  rw [chR_eq, cf_sum'] at h
  obtain ⟨B, hB, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨B, Finset.mem_powerset.1 hB, ?_⟩
  rw [cf_ex] at hne
  by_contra hc
  exact hne (if_neg fun e => hc e.symm)

private theorem rt_self {n : ℕ} (a : Fin n) : rt a a = 0 := by simp [rt]

private theorem rt_swap {n : ℕ} (a b : Fin n) : rt b a = -rt a b := by simp [rt]

private theorem prod_all (n : ℕ) :
    ∏ a, ∏ b, (1 + ex (rt a b)) = (2 : ℂ) ^ n • (chR n * chR n) := by
  classical
  set g : Fin n × Fin n → FR n := fun p => 1 + ex (rt p.1 p.2) with hg
  have h0 : ∏ a, ∏ b, (1 + ex (rt a b)) = ∏ p : Fin n × Fin n, g p := by
    rw [Fintype.prod_prod_type]
  have hsplit : ∏ p : Fin n × Fin n, g p =
      (∏ p ∈ posP n, g p) * ((∏ a : Fin n, g (a, a)) * ∏ p ∈ posP n, g (p.2, p.1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 < p.2) g]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not
      (Finset.univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2) (fun p => p.1 = p.2) g]
    congr 1
    · refine Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
      · intro p _; simp
      · intro a _; simp
      · rintro ⟨a, b⟩ h
        simp at h
        simp [h.2]
      · intro a _; rfl
      · rintro ⟨a, b⟩ h
        simp at h
        simp [h.2]
    · refine Finset.prod_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨a, b⟩ h
        simp at h
        simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne h.1 (Ne.symm h.2)
      · rintro ⟨a, b⟩ h
        simp only [posP, Finset.mem_filter, Finset.mem_univ, true_and] at h
        simp [h.le, h.ne']
      · intro p _; rfl
      · intro p _; rfl
      · intro p _; rfl
  have hd : ∏ a : Fin n, g (a, a) = (2 : FR n) ^ n := by
    simp [hg, rt_self, ex_zero', one_add_one_eq_two]
  have hs : ∀ p ∈ posP n, g (p.2, p.1) = 1 + ex (-rt p.1 p.2) := by
    intro p _
    simp only [hg]
    rw [rt_swap p.1 p.2]
  have hq : ∏ p ∈ posP n, g p = ex ((2 : ℝ) • rhoV n) * ∏ p ∈ posP n, (1 + ex (-rt p.1 p.2)) := by
    have : ∀ p ∈ posP n, g p = ex (rt p.1 p.2) * (1 + ex (-rt p.1 p.2)) := by
      intro p _
      rw [mul_add, mul_one, ← ex_add', add_neg_cancel, ex_zero', add_comm]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, ex_sum, ← wtB_sum, wtB_pos]
  have e2 : ex ((2 : ℝ) • rhoV n) = ex (rhoV n) * ex (rhoV n) := by rw [← ex_add', two_smul]
  rw [h0, hsplit, hd, Finset.prod_congr rfl hs, hq, e2, Algebra.smul_def, chR]
  simp only [map_pow, map_ofNat]
  ring

theorem UpperTheory.RealTr.chRF :
    ∀ n : ℕ, alt ((2 : ℝ) • rhoV n) = alt (rhoV n) * chR n ∧ alt (rhoV n) ≠ 0 ∧ chR n ≠ 0 ∧ Sym (chR n) ∧ (∀ x, cf (chR n) (-x) = cf (chR n) x) ∧
      (∀ x, cf (chR n) x ≠ 0 → ∃ B ⊆ posP n, x = rhoV n - wtB B) ∧
      ∏ a, ∏ b, (1 + ex (rt a b)) = (2 : ℂ) ^ n • (chR n * chR n) ∧ wtB (posP n) = (2 : ℝ) • rhoV n ∧
      ∀ B : Finset (Fin n × Fin n), wtB B = ∑ p ∈ B, rt p.1 p.2 := by
  intro n
  have hρ : StrictAnti (rhoV n) := (UpperTheory.RealTr.rearr n).2.2.1
  have h2ρ : StrictAnti ((2 : ℝ) • rhoV n) := fun a b h => by
    have := hρ h
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  have hA := (UpperTheory.RealTr.cfBasic n).2.2.2.2.2.2.2.2.1
  have hm := denom_mul n
  have hd := alt_ne _ hρ
  refine ⟨hm, hd, ?_, sym_of_mul _ _ _ (hA _) (hA _) hd hm, even_chR n, supp_chR n, prod_all n, wtB_pos n, wtB_sum⟩
  intro h0
  rw [h0, mul_zero] at hm
  exact alt_ne _ h2ρ hm
