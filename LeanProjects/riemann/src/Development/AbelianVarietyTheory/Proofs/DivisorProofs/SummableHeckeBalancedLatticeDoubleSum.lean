import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.LatSum

variable {F : Type} [Field F] [NumberField F]

def absSum (x : F) : ℝ := ∑ τ : Emb F, |τ x|

theorem absSum_nonneg (x : F) : 0 ≤ absSum x := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_absSum (x : F) (τ : Emb F) : |τ x| ≤ absSum x :=
  Finset.single_le_sum (f := fun τ : Emb F => |τ x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)

theorem one_add_sum_le_prod {ι : Type} (s : Finset ι) (a : ι → ℝ) (h : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => h j
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith [h i] : (0:ℝ) ≤ 1 + a i), mul_nonneg (h i) h1]

theorem bound_eq (K₁ s x q : ℝ) (a b : ℕ) (hs : s ≠ 0) (hx : x ≠ 0) (hq : q ≠ 0) :
    (K₁ * s) ^ a / (x * (s / q)) ^ (a + b) = K₁ ^ a * q ^ (a + b) * ((s ^ b)⁻¹ * (x ^ (a + b))⁻¹) := by
  rw [mul_pow, mul_pow, div_pow, pow_add s]
  field_simp

variable [IsTotallyReal F]

open scoped Classical in

theorem norm_mixedEmbedding_le (x : F) : ‖mixedEmbedding F x‖ ≤ absSum x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) x,
    Real.norm_eq_abs]
  exact abs_le_absSum x _

open scoped Classical in
theorem absSum_pos {x : F} (hx : x ≠ 0) : 0 < absSum x := by
  have h : 0 < ‖mixedEmbedding F x‖ := norm_pos_iff.2 fun h =>
    hx ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  exact h.trans_le (norm_mixedEmbedding_le x)

open scoped Classical in

theorem summable_absSum_inv_pow (I : Frac F) {k : ℕ} (hk : Module.finrank ℚ F < k) :
    Summable (fun x : NZ (I : FractionalIdeal (𝓞 F)⁰ F) => ((absSum x.1) ^ k)⁻¹) := by
  let L := mixedEmbedding.idealLattice F I
  have hL := ZLattice.summable_norm_rpow L (-(k : ℝ)) (by
    rw [ZLattice.rank ℝ L, mixedEmbedding.finrank F]
    have : (Module.finrank ℚ F : ℝ) < k := by exact_mod_cast hk
    linarith)
  let j : NZ (I : FractionalIdeal (𝓞 F)⁰ F) → L := fun x =>
    ⟨mixedEmbedding F x.1, (mixedEmbedding.mem_idealLattice F I).2 ⟨x.1, x.2.1, rfl⟩⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext ((mixedEmbedding F).injective (congrArg Subtype.val h))
  refine (hL.comp_injective hj).of_nonneg_of_le (fun x => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun x => ?_)
  have hpos : 0 < ‖mixedEmbedding F x.1‖ := norm_pos_iff.2 fun h =>
    x.2.2 ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  show ((absSum x.1) ^ k)⁻¹ ≤ ‖mixedEmbedding F x.1‖ ^ (-(k : ℝ))
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (norm_mixedEmbedding_le x.1) k)

theorem prod_abs_emb (x : F) : ∏ τ : Emb F, |τ x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (prod_emb x)
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem exists_absSum_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ I, x ≠ 0 → β ≤ absSum x := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  set D := |((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ)| with hD
  have hDpos : 0 < D := by simp [hD, Algebra.norm_eq_zero_iff, hd0]
  have hn : 1 ≤ Fintype.card (Emb F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  refine ⟨min 1 D⁻¹, lt_min one_pos (inv_pos.2 hDpos), fun x hx hx0 => ?_⟩
  obtain ⟨g, hg⟩ := h x hx
  have hg' : ((g : 𝓞 F) : F) = ((d : 𝓞 F) : F) * x := by
    rw [← Algebra.smul_def] at *; simpa using hg
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0] at hg'; simp at hg'
    exact hg'.elim (fun h => hd0 (by exact_mod_cast h)) hx0
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ g : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg0
    exact_mod_cast Int.one_le_abs this
  have e1 : ((Algebra.norm ℤ g : ℤ) : ℚ) = Algebra.norm ℚ ((d : 𝓞 F) : F) * Algebra.norm ℚ x := by
    rw [Algebra.coe_norm_int, hg', map_mul]
  have e2 : ((Algebra.norm ℤ g : ℤ) : ℝ) =
      ((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ) * ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul, ← hD, ← prod_abs_emb] at h1
  have hle : ∏ τ : Emb F, |τ x| ≤ absSum x ^ Fintype.card (Emb F) := by
    calc ∏ τ : Emb F, |τ x| ≤ ∏ _τ : Emb F, absSum x :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun τ _ => abs_le_absSum x τ)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hS0 := absSum_nonneg x
  rcases le_or_gt 1 (absSum x) with hS | hS
  · exact (min_le_left _ _).trans hS
  · have hpow : absSum x ^ Fintype.card (Emb F) ≤ absSum x := pow_le_of_le_one hS0 hS.le (by omega)
    refine (min_le_right _ _).trans ?_
    have : 1 ≤ D * absSum x := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpow) hDpos.le)
    rw [inv_le_iff_one_le_mul₀ hDpos]
    linarith

end GlobalTheory.HeckeTwo.LatSum

open GlobalTheory.HeckeTwo.LatSum in

theorem GlobalTheory.HeckeTwo.summable_balanced_latSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  intro F _ _ _ 𝔞 𝔟 C₀ m
  set n := Fintype.card (Emb F) with hn_def
  set f := Module.finrank ℚ F with hf_def
  refine ⟨m * n + (f + 1), fun ε hbal => ?_⟩
  set N := m * n + (f + 1) with hN
  rcases isEmpty_or_nonempty (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) with hE | ⟨⟨c₀⟩⟩
  · exact summable_empty
  have hn : 1 ≤ n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  obtain ⟨τ₀⟩ : Nonempty (Emb F) := Fintype.card_pos_iff.1 hn
  obtain ⟨β, hβ, hβS⟩ := exists_absSum_lower (𝔟 : FractionalIdeal (𝓞 F)⁰ F)

  let bp : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → F := fun c => ((ε c : 𝓞 F) : F) * c.out.1
  have hunit0 : ∀ u : (𝓞 F)ˣ, ((u : 𝓞 F) : F) ≠ 0 := fun u h =>
    u.ne_zero (by exact_mod_cast h)
  have hbp_mem : ∀ c, bp c ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := fun c => by
    have := Submodule.smul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε c : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at this
  have hbp0 : ∀ c, bp c ≠ 0 := fun c => mul_ne_zero (hunit0 _) c.out.2.2
  have hC₀ : 1 ≤ C₀ := by
    have h := hbal c₀ τ₀ τ₀
    have hpos : 0 < |τ₀ (bp c₀)| := abs_pos.2 ((map_ne_zero τ₀).2 (hbp0 c₀))
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h) hpos
  have hq : 0 < (n : ℝ) * C₀ := mul_pos (by exact_mod_cast hn) (by linarith)
  have hlow : ∀ c (τ : Emb F), absSum (bp c) / (n * C₀) ≤ |τ (bp c)| := by
    intro c τ
    rw [div_le_iff₀ hq]
    calc absSum (bp c) = ∑ τ' : Emb F, |τ' (bp c)| := rfl
      _ ≤ ∑ _τ' : Emb F, C₀ * |τ (bp c)| := Finset.sum_le_sum fun τ' _ => hbal c τ' τ
      _ = |τ (bp c)| * (n * C₀) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

  let g : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ := fun c => ((absSum (bp c)) ^ (f + 1))⁻¹
  let h : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ := fun y => ((absSum y.1) ^ N)⁻¹
  have hg : Summable g := by
    refine (summable_absSum_inv_pow 𝔟 (k := f + 1) (by omega)).comp_injective
      (i := fun c => (⟨bp c, hbp_mem c, hbp0 c⟩ : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) ?_
    intro c c' hcc
    have e : bp c = bp c' := congrArg Subtype.val hcc
    refine Quotient.out_equiv_out.1 ⟨(ε c')⁻¹ * ε c, ?_⟩
    have h1 : (((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c' : 𝓞 F) : F) = 1 := unit_inv_mul (ε c')
    simp only [bp] at e
    push_cast
    linear_combination (-(c'.out.1) * h1) - ((((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * e
  have hh : Summable h := summable_absSum_inv_pow 𝔞 (k := N) (by omega)
  let e : (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := fun p =>
    (p.1, ⟨((((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.2.1, by
      have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule
        (((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) p.2.2.1
      rwa [Algebra.smul_def] at this, mul_ne_zero (hunit0 _) p.2.2.2⟩)
  have he : Function.Injective e := by
    rintro ⟨c, ν⟩ ⟨c', ν'⟩ hcc
    have h1 : c = c' := congrArg Prod.fst hcc
    subst h1
    have h2 := congrArg (fun p => (p.2 : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1) hcc
    simp only [e] at h2
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (hunit0 _) h2))
  have hV := (hg.mul_of_nonneg hh (fun c => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun y => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))).comp_injective he
  set K₁ : ℝ := 1 + n * C₀ / β ^ 2 with hK₁
  refine (hV.mul_left (K₁ ^ (m * n) * (n * C₀) ^ N)).of_nonneg_of_le
    (fun p => Finset.prod_nonneg fun τ _ => div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))
    (fun p => ?_)

  obtain ⟨c, ν⟩ := p
  set b' := bp c with hb'
  set ν' := ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 with hν'
  set s := absSum b' with hs
  set x := absSum ν' with hx
  have hsβ : β ≤ s := hβS _ (hbp_mem c) (hbp0 c)
  have hs0 : 0 < s := hβ.trans_le hsβ
  have hx0 : 0 < x := absSum_pos (mul_ne_zero (hunit0 _) ν.2.2)
  have hid : ∀ τ : Emb F, |τ ν.1 * τ c.out.1| = |τ ν'| * |τ b'| := by
    intro τ
    have h1 : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
    rw [← abs_mul, ← map_mul, ← map_mul]
    congr 2
    simp only [hν', hb', bp]
    linear_combination (-(ν.1 * c.out.1)) * h1
  have hA : ∀ τ : Emb F, |τ b'| + |τ b'|⁻¹ ≤ K₁ * s := by
    intro τ
    have hlo := hlow c τ
    have hpos : 0 < s / (n * C₀) := div_pos hs0 hq
    have h1 : |τ b'|⁻¹ ≤ n * C₀ / s := by
      calc |τ b'|⁻¹ ≤ (s / (n * C₀))⁻¹ := inv_anti₀ hpos hlo
        _ = n * C₀ / s := inv_div _ _
    have h2 : n * C₀ / s ≤ n * C₀ / β ^ 2 * s := by
      rw [div_le_iff₀ hs0]
      have hβ2 : β ^ 2 ≤ s * s := by nlinarith
      calc (n : ℝ) * C₀ = n * C₀ / β ^ 2 * β ^ 2 := by field_simp
        _ ≤ n * C₀ / β ^ 2 * (s * s) := mul_le_mul_of_nonneg_left hβ2 (by positivity)
        _ = _ := by ring
    have h3 : |τ b'| ≤ s := abs_le_absSum _ τ
    rw [hK₁]; nlinarith
  have hnum : ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ (K₁ * s) ^ (m * n) := by
    calc ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ ∏ _τ : Emb F, (K₁ * s) ^ m :=
          Finset.prod_le_prod (fun _ _ => pow_nonneg (by positivity) _) (fun τ _ => pow_le_pow_left₀ (by positivity) (hA τ) m)
      _ = (K₁ * s) ^ (m * n) := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hden : (x * (s / (n * C₀))) ^ N ≤ ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N := by
    rw [Finset.prod_pow]
    refine pow_le_pow_left₀ (mul_nonneg hx0.le (div_pos hs0 hq).le) ?_ N
    calc x * (s / (n * C₀)) = ∑ τ : Emb F, |τ ν'| * (s / (n * C₀)) := by rw [hx, absSum, Finset.sum_mul]
      _ ≤ ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := Finset.sum_le_sum fun τ _ => by
          rw [hid]; exact mul_le_mul_of_nonneg_left (hlow c τ) (abs_nonneg _)
      _ ≤ 1 + ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := by linarith
      _ ≤ _ := one_add_sum_le_prod _ _ fun τ => abs_nonneg _
  have hdpos : 0 < (x * (s / (n * C₀))) ^ N := pow_pos (mul_pos hx0 (div_pos hs0 hq)) N
  show ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m / (1 + |τ ν.1 * τ c.out.1|) ^ N ≤
    K₁ ^ (m * n) * (n * C₀) ^ N * (((s) ^ (f + 1))⁻¹ * ((x) ^ N)⁻¹)
  rw [Finset.prod_div_distrib]
  calc (∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m) / ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N
      ≤ (K₁ * s) ^ (m * n) / (x * (s / (n * C₀))) ^ N :=
        div_le_div₀ (by positivity) hnum hdpos hden
    _ = K₁ ^ (m * n) * (n * C₀) ^ N * ((s ^ (f + 1))⁻¹ * (x ^ N)⁻¹) := by
        rw [hN]
        exact bound_eq _ _ _ _ _ _ hs0.ne' hx0.ne' hq.ne'
