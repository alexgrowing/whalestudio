import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HermInv

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_algebraMap [Unram F E] (x : F) : star (algebraMap F E x) = algebraMap F E x := Unram.star_fix x

def starLin [Unram F E] : E →ₗ[F] E where
  toFun := star
  map_add' := star_add
  map_smul' c z := by
    simp only [Algebra.smul_def, RingHom.id_apply, star_mul, star_algebraMap, mul_comm]

theorem fixed_mem_range [Unram F E] {y : E} (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  by_contra hne
  push_neg at hne
  have hli : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hne (-(s / t))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [Unram.finrank_eq (F := F) (E := E)])
  obtain ⟨z, hz⟩ := Unram.star_ne (F := F) (E := E)
  apply hz
  have hle : Submodule.span F (Set.range ![(1 : E), y]) ≤ LinearMap.ker (starLin (F := F) (E := E) - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simp [starLin]
    · simp [starLin, hy]
  have := hle (htop ▸ Submodule.mem_top : z ∈ Submodule.span F (Set.range ![(1 : E), y]))
  simpa [starLin, sub_eq_zero] using this

section Gen
variable {r : ℕ} {K : Type} [CommRing K]

theorem pow_r_mulVec [Nontrivial K] (Y : Gl r K) :
    Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ fun i : Fin r => Y.1.charpoly.coeff i) := by
  have h0 := Matrix.aeval_self_charpoly Y.1
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Finset.sum_range_succ,
    Finset.sum_range] at h0
  have hc : Y.1.charpoly.coeff r = 1 := by
    have := (Matrix.charpoly_monic Y.1).coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [hc, one_smul, add_comm] at h0
  have hA : Y.1 ^ r = -∑ i : Fin r, Y.1.charpoly.coeff i • Y.1 ^ (i : ℕ) := eq_neg_iff_add_eq_zero.mpr h0
  rw [hA, Matrix.neg_mulVec]
  congr 1
  ext j
  simp only [mulVec, dotProduct, Bm, of_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

theorem mulBm_eq (Y : Gl r K) (k : ℕ) : Y.2.2.1 ᵥ* (Y.1 ^ k * Bm Y) = fun j : Fin r => mom Y (k + j) := by
  funext j
  have : (Y.1 ^ k * Bm Y) = Matrix.of fun i (j : Fin r) => ((Y.1 ^ (k + (j : ℕ))) *ᵥ Y.2.1) i := by
    ext i j
    simp only [mul_apply, Bm, of_apply, pow_add, ← mulVec_mulVec]
    rfl
  rw [this]
  simp only [vecMul, mom, dotProduct, of_apply]

theorem mom_add_r (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) (k : ℕ) :
    mom Y (k + r) = -((fun j : Fin r => mom Y (k + j)) ⬝ᵥ q) := by
  rw [← mulBm_eq, ← dotProduct_mulVec, ← mulVec_mulVec, ← dotProduct_neg, ← mulVec_neg, ← hq, mulVec_mulVec, ← pow_add]
  rfl

theorem seq_eq {u v : ℕ → K} (q : Fin r → K) (hu : ∀ k, u (k + r) = -((fun j : Fin r => u (k + j)) ⬝ᵥ q))
    (hv : ∀ k, v (k + r) = -((fun j : Fin r => v (k + j)) ⬝ᵥ q)) (h : ∀ k < r, u k = v k) : u = v := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < r
    · exact h n hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + r := ⟨n - r, by omega⟩
      rw [hu, hv]
      congr 2
      funext j
      exact ih _ (by omega)

def ev (r : ℕ) (K : Type) [CommRing K] (j : ℕ) : Fin r → K := fun i => if (i : ℕ) = j then 1 else 0

theorem comp_mulVec_ev (p : Fin r → K) (j : ℕ) (hj : j + 1 < r) : companion p *ᵥ ev r K j = ev r K (j + 1) := by
  funext i
  simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨j, by omega⟩]
  · simp [companion, show j + 1 ≠ r by omega]
  · intro l _ hl
    rw [if_neg]
    exact fun h => hl (Fin.ext h)
  · simp

theorem comp_pow_ev (p : Fin r → K) (j : ℕ) (hj : j < r) : companion p ^ j *ᵥ ev r K 0 = ev r K j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), comp_mulVec_ev p j hj]

theorem comp_pow_r (p : Fin r → K) : companion p ^ r *ᵥ ev r K 0 = -p := by
  cases r with
  | zero => funext i; exact i.elim0
  | succ s =>
    rw [pow_succ', ← mulVec_mulVec, comp_pow_ev p s (by omega)]
    funext i
    simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨s, by omega⟩]
    · simp [companion]
    · intro l _ hl
      rw [if_neg]
      exact fun h => hl (Fin.ext h)
    · simp

theorem sec_snd (a : Inv r K) : (sec a).2.1 = ev r K 0 := rfl

theorem Bm_sec (a : Inv r K) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, of_apply, sec_snd]
  rw [show (sec a).1 = companion a.1 from rfl, comp_pow_ev a.1 j j.2]
  simp [ev, one_apply, Fin.ext_iff, eq_comm]

theorem sec_rec (a : Inv r K) (k : ℕ) :
    mom (sec a) (k + r) = -((fun j : Fin r => mom (sec a) (k + j)) ⬝ᵥ a.1) :=
  mom_add_r (sec a) a.1 (by rw [Bm_sec, one_mulVec]; exact comp_pow_r a.1) k

theorem mom_sec_lt (a : Inv r K) (i : Fin r) : mom (sec a) i = a.2.1 i := by
  simp only [mom]
  rw [show (sec a).1 = companion a.1 from rfl, sec_snd, comp_pow_ev a.1 i i.2]
  simp only [dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp [show (sec a).2.2.1 = a.2.1 from rfl]
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp

end Gen

section Herm
variable {r : ℕ}

theorem hasInv_iff (X : Hn r F E) (a : Inv r F) : HasInv X a ↔
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (a.1 i)) ∧
    (∀ i : Fin r, mom X.toGl i = algebraMap F E (a.2.1 i)) ∧ X.2.2 = a.2.2 := by
  simp only [HasInv, GlobalTheory.JR.inv, Inv.map, Prod.mk.injEq, funext_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (algebraMap F E).injective.eq_iff)

theorem charpoly_coeff_star (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (i : ℕ) :
    star (A.charpoly.coeff i) = A.charpoly.coeff i := by
  have hT : A.map (starRingEnd E) = Aᵀ := by
    ext k l
    have := congrFun (congrFun hA l) k
    rw [Matrix.star_apply] at this
    rw [Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply, this]
  calc star (A.charpoly.coeff i) = (A.charpoly.map (starRingEnd E)).coeff i := by
        rw [Polynomial.coeff_map]; rfl
    _ = A.charpoly.coeff i := by rw [← Matrix.charpoly_map, hT, Matrix.charpoly_transpose]

theorem conjT_eq (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) : Aᴴ = A := hA

theorem form_pow (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (v w : Fin r → E) (k : ℕ) :
    star (A ^ k *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (A ^ k *ᵥ w) := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.conjTranspose_pow, conjT_eq A hA]

theorem mom_star (X : Hn r F E) (k : ℕ) : star (mom X.toGl k) = mom X.toGl k := by
  show star (star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)) = star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)
  conv_lhs => rw [star_dotProduct, star_star]
  rw [form_pow X.1.1 X.1.2]

variable [Unram F E]

theorem part1 (X : Hn r F E) : ∃ a : Inv r F, HasInv X a := by
  choose p hp using fun i : Fin r => fixed_mem_range (F := F) (charpoly_coeff_star X.1.1 X.1.2 i)
  choose m hm using fun i : Fin r => fixed_mem_range (F := F) (mom_star X i)
  exact ⟨(p, m, X.2.2), (hasInv_iff X _).2 ⟨fun i => (hp i).symm, fun i => (hm i).symm, rfl⟩⟩

end Herm

section Act
variable {r : ℕ}

theorem starU_mul (g : Matrix.unitaryGroup (Fin r) E) : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2

theorem mul_starU (g : Matrix.unitaryGroup (Fin r) E) : g.1 * star g.1 = 1 := Matrix.mem_unitaryGroup_iff.1 g.2

theorem unit_conj_pow (g : Matrix.unitaryGroup (Fin r) E) (A : Matrix (Fin r) (Fin r) E) (k : ℕ) :
    (g.1 * A * star g.1) ^ k = g.1 * A ^ k * star g.1 := by
  induction k with
  | zero => simp [mul_starU g]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (star g.1) g.1, starU_mul g, one_mul]

theorem unit_form (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E) :
    star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    starU_mul g, one_mulVec]

theorem charpoly_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    (actU g X).1.1.charpoly = X.1.1.charpoly := by
  show (g.1 * X.1.1 * star g.1).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, starU_mul g, one_mul]

theorem mom_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (k : ℕ) :
    mom (actU g X).toGl k = mom X.toGl k := by
  show star (g.1 *ᵥ X.2.1) ⬝ᵥ ((g.1 * X.1.1 * star g.1) ^ k *ᵥ (g.1 *ᵥ X.2.1)) = star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)
  rw [unit_conj_pow, mulVec_mulVec, mul_assoc, mul_assoc, starU_mul g, mul_one,
    ← mulVec_mulVec, unit_form]

theorem part2 (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    HasInv (actU g X) a := by
  obtain ⟨h1, h2, h3⟩ := (hasInv_iff X a).1 h
  exact (hasInv_iff _ a).2 ⟨fun i => by rw [charpoly_actU]; exact h1 i, fun i => by rw [mom_actU]; exact h2 i, h3⟩

end Act

section Gen2
variable {r : ℕ} {K : Type} [CommRing K]

theorem mul_Bm (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) :
    Y.1 * Bm Y = Bm Y * companion q := by
  ext i j
  have hL : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [mul_apply, Bm, mulVec, dotProduct]
  rw [hL]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [hj, hq]
    simp [mul_apply, companion, hj, mulVec, dotProduct]
  · rw [mul_apply, Finset.sum_eq_single ⟨(j : ℕ) + 1, by omega⟩]
    · simp [companion, hj, Bm]
    · intro l _ hl
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hl (Fin.ext h)
      simp [companion, hj, this]
    · simp

theorem Bm_ev (Y : Gl r K) : Bm Y *ᵥ ev r K 0 = Y.2.1 := by
  funext i
  simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨0, i.pos⟩]
  · simp [Bm]
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp

end Gen2

section Main
variable {r : ℕ}

theorem mom_map (X : Hn r F E) (a : Inv r F) (h : HasInv X a) (n : ℕ) :
    mom X.toGl n = algebraMap F E (mom (sec a) n) := by
  obtain ⟨h1, h2, -⟩ := (hasInv_iff X a).1 h
  have hq : X.toGl.1 ^ r *ᵥ X.toGl.2.1 = -(Bm X.toGl *ᵥ fun i => algebraMap F E (a.1 i)) := by
    have := pow_r_mulVec X.toGl
    rwa [show (fun i : Fin r => X.toGl.1.charpoly.coeff i) = fun i => algebraMap F E (a.1 i) from funext h1] at this
  have hS : ∀ k, algebraMap F E (mom (sec a) (k + r)) =
      -((fun j : Fin r => algebraMap F E (mom (sec a) (k + j))) ⬝ᵥ fun i => algebraMap F E (a.1 i)) := by
    intro k
    rw [sec_rec]
    simp [dotProduct, map_sum, map_mul]
  have := seq_eq (u := fun n => mom X.toGl n) (v := fun n => algebraMap F E (mom (sec a) n)) _
    (mom_add_r X.toGl _ hq) hS (fun k hk => by
      have e1 := h2 ⟨k, hk⟩
      have e2 := mom_sec_lt a ⟨k, hk⟩
      simp only at e1 e2 ⊢
      rw [e1, e2])
  exact congrFun this n

theorem gram (X : Hn r F E) : (Bm X.toGl)ᴴ * Bm X.toGl = Matrix.of fun i j : Fin r => mom X.toGl ((i : ℕ) + j) := by
  ext i j
  have : ((Bm X.toGl)ᴴ * Bm X.toGl) i j = star (X.1.1 ^ (i : ℕ) *ᵥ X.2.1) ⬝ᵥ (X.1.1 ^ (j : ℕ) *ᵥ X.2.1) := by
    simp only [mul_apply, conjTranspose_apply, Bm, of_apply, dotProduct, Pi.star_apply]
    rfl
  rw [this, form_pow X.1.1 X.1.2, mulVec_mulVec, ← pow_add]
  rfl

theorem gram_hankel (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    (Bm X.toGl)ᴴ * Bm X.toGl = (hankel a).map (algebraMap F E) := by
  rw [gram]
  ext i j
  simp [hankel, mom_map X a h]

theorem det_unit (a : Inv r F) (hΔ : Delta a ≠ 0) (h : Matrix (Fin r) (Fin r) E)
    (hh : hᴴ * h = (hankel a).map (algebraMap F E)) : IsUnit h.det := by
  have : (hᴴ * h).det ≠ 0 := by
    rw [hh, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hΔ
  rw [det_mul] at this
  exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul this)

end Main

section Three
variable {r : ℕ}

theorem pow_r_of (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    X.1.1 ^ r *ᵥ X.2.1 = -(Bm X.toGl *ᵥ fun i => algebraMap F E (a.1 i)) := by
  obtain ⟨h1, -, -⟩ := (hasInv_iff X a).1 h
  have := pow_r_mulVec X.toGl
  rwa [show (fun i : Fin r => X.toGl.1.charpoly.coeff i) = fun i => algebraMap F E (a.1 i) from funext h1] at this

theorem semiconj_of_act (g : Matrix.unitaryGroup (Fin r) E) (X₁ X₂ : Hn r F E) (hact : actU g X₁ = X₂) :
    g.1 * X₁.1.1 = X₂.1.1 * g.1 := by
  have e1 : g.1 * X₁.1.1 * star g.1 = X₂.1.1 := congrArg (fun Y : Hn r F E => Y.1.1) hact
  rw [← e1, mul_assoc _ (star g.1), starU_mul, mul_one]

theorem g_Bm (g : Matrix.unitaryGroup (Fin r) E) (X₁ X₂ : Hn r F E) (hact : actU g X₁ = X₂) :
    g.1 * Bm X₁.toGl = Bm X₂.toGl := by
  have hs := semiconj_of_act g X₁ X₂ hact
  have e2 : g.1 *ᵥ X₁.2.1 = X₂.2.1 := congrArg (fun Y : Hn r F E => Y.2.1) hact
  have hp : ∀ k : ℕ, g.1 * X₁.1.1 ^ k = X₂.1.1 ^ k * g.1 := fun k => SemiconjBy.pow_right hs k
  ext i j
  have : (g.1 * Bm X₁.toGl) i j = (g.1 *ᵥ (X₁.1.1 ^ (j : ℕ) *ᵥ X₁.2.1)) i := by
    simp only [mul_apply, Bm, of_apply, mulVec, dotProduct]
    rfl
  rw [this, mulVec_mulVec, hp, ← mulVec_mulVec, e2]
  rfl

theorem part3 (X₁ X₂ : Hn r F E) (a : Inv r F) (hΔ : Delta a ≠ 0) (h₁ : HasInv X₁ a) (h₂ : HasInv X₂ a) :
    ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂ := by
  have G₁ := gram_hankel X₁ a h₁
  have G₂ := gram_hankel X₂ a h₂
  have u₁ := det_unit a hΔ _ G₁
  have hB₁ : Bm X₁.toGl * (Bm X₁.toGl)⁻¹ = 1 := mul_nonsing_inv _ u₁
  have hB₁' : (Bm X₁.toGl)⁻¹ * Bm X₁.toGl = 1 := nonsing_inv_mul _ u₁
  set B₁ := Bm X₁.toGl with hB1def
  set B₂ := Bm X₂.toGl with hB2def
  have hstar : star (B₂ * B₁⁻¹) * (B₂ * B₁⁻¹) = 1 := by
    rw [star_eq_conjTranspose, conjTranspose_mul]
    calc (B₁⁻¹)ᴴ * B₂ᴴ * (B₂ * B₁⁻¹) = (B₁⁻¹)ᴴ * (B₂ᴴ * B₂) * B₁⁻¹ := by simp only [mul_assoc]
      _ = (B₁⁻¹)ᴴ * (B₁ᴴ * B₁) * B₁⁻¹ := by rw [G₁, G₂]
      _ = (B₁ * B₁⁻¹)ᴴ * (B₁ * B₁⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = 1 := by rw [hB₁, conjTranspose_one, one_mul]
  have hmem : B₂ * B₁⁻¹ ∈ Matrix.unitaryGroup (Fin r) E := Matrix.mem_unitaryGroup_iff'.2 hstar
  have hmul : (B₂ * B₁⁻¹) * star (B₂ * B₁⁻¹) = 1 := Matrix.mem_unitaryGroup_iff.1 hmem
  have C₁ : X₁.1.1 * B₁ = B₁ * companion (fun i => algebraMap F E (a.1 i)) :=
    mul_Bm X₁.toGl _ (pow_r_of X₁ a h₁)
  have C₂ : X₂.1.1 * B₂ = B₂ * companion (fun i => algebraMap F E (a.1 i)) :=
    mul_Bm X₂.toGl _ (pow_r_of X₂ a h₂)
  have hs : (B₂ * B₁⁻¹) * X₁.1.1 = X₂.1.1 * (B₂ * B₁⁻¹) := by
    calc (B₂ * B₁⁻¹) * X₁.1.1 = B₂ * (B₁⁻¹ * X₁.1.1 * B₁) * B₁⁻¹ := by simp only [mul_assoc, hB₁, mul_one]
      _ = B₂ * companion (fun i => algebraMap F E (a.1 i)) * B₁⁻¹ := by
        rw [mul_assoc B₁⁻¹ X₁.1.1 B₁, C₁, ← mul_assoc B₁⁻¹ B₁, hB₁', one_mul]
      _ = X₂.1.1 * (B₂ * B₁⁻¹) := by rw [← C₂]; simp only [mul_assoc]
  obtain ⟨-, -, l₁⟩ := (hasInv_iff X₁ a).1 h₁
  obtain ⟨-, -, l₂⟩ := (hasInv_iff X₂ a).1 h₂
  refine ⟨⟨B₂ * B₁⁻¹, hmem⟩, ?_, ?_⟩
  · have e1 : (B₂ * B₁⁻¹) * X₁.1.1 * star (B₂ * B₁⁻¹) = X₂.1.1 := by rw [hs, mul_assoc, hmul, mul_one]
    have b1 : B₁ *ᵥ ev r E 0 = X₁.2.1 := Bm_ev X₁.toGl
    have b2 : B₂ *ᵥ ev r E 0 = X₂.2.1 := Bm_ev X₂.toGl
    have e2 : (B₂ * B₁⁻¹) *ᵥ X₁.2.1 = X₂.2.1 := by
      rw [← b1, mulVec_mulVec, mul_assoc, hB₁', mul_one, b2]
    exact Prod.ext (Subtype.ext e1) (Prod.ext e2 (l₁.trans l₂.symm))
  · intro g hg
    apply Subtype.ext
    have := g_Bm g X₁ X₂ hg
    rw [← hB1def, ← hB2def] at this
    show g.1 = B₂ * B₁⁻¹
    rw [← this, mul_assoc, hB₁, mul_one]

end Three

section Four
variable {r : ℕ}

theorem comp_map {K L : Type} [CommRing K] [CommRing L] (f : K →+* L) (p : Fin r → K) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [map_apply, companion, of_apply]
  split_ifs <;> simp

theorem hankel_symm {K : Type} [CommRing K] (a : Inv r K) : (hankel a)ᵀ = hankel a := by
  ext i j
  simp [hankel, add_comm]

theorem HC_apply {K : Type} [CommRing K] (a : Inv r K) (i j : Fin r) :
    (hankel a * companion a.1) i j = mom (sec a) ((i : ℕ) + j + 1) := by
  by_cases hj : (j : ℕ) + 1 = r
  · rw [add_assoc, hj, sec_rec]
    simp [mul_apply, companion, hj, hankel, dotProduct]
  · rw [mul_apply, Finset.sum_eq_single ⟨(j : ℕ) + 1, by omega⟩]
    · simp [companion, hj, hankel, add_assoc]
    · intro l _ hl
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hl (Fin.ext h)
      simp [companion, hj, this]
    · simp

theorem HC_symm {K : Type} [CommRing K] (a : Inv r K) :
    (companion a.1)ᵀ * hankel a = hankel a * companion a.1 := by
  have : (hankel a * companion a.1)ᵀ = hankel a * companion a.1 := by
    ext i j
    rw [transpose_apply, HC_apply, HC_apply, add_comm (j : ℕ)]
  rw [← this, transpose_mul, hankel_symm]

theorem conj_pow' (h h' M : Matrix (Fin r) (Fin r) E) (hh : h' * h = 1) (hh' : h * h' = 1) (k : ℕ) :
    (h * M * h') ^ k = h * M ^ k * h' := by
  induction k with
  | zero => simp [hh']
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc h' h, hh, one_mul]

theorem mulVec_ev {K : Type} [CommRing K] (M : Matrix (Fin r) (Fin r) K) (j : Fin r) :
    M *ᵥ ev r K j = fun i => M i j := by
  funext i
  simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl; rw [if_neg]; exact fun h => hl (Fin.ext h)
  · simp

theorem part4 [Unram F E] (a : Inv r F) (hΔ : Delta a ≠ 0) :
    (∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E) := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨Bm X.toGl, gram_hankel X a hX⟩
  · rintro ⟨h, hh⟩
    have u := det_unit a hΔ h hh
    have hinv : h * h⁻¹ = 1 := mul_nonsing_inv _ u
    have hinv' : h⁻¹ * h = 1 := nonsing_inv_mul _ u
    set p : Fin r → E := fun i => algebraMap F E (a.1 i) with hp
    set CE := companion p with hCE
    have hCEm : CE = (companion a.1).map (algebraMap F E) := by rw [hCE, comp_map]
    have hCEH : CEᴴ = ((companion a.1)ᵀ).map (algebraMap F E) := by
      rw [hCEm]
      ext i j
      simp [conjTranspose_apply, star_algebraMap]
    have hM : CEᴴ * (hᴴ * h) = (hᴴ * h) * CE := by
      rw [hh, hCEH, hCEm, ← Matrix.map_mul, ← Matrix.map_mul, HC_symm]
    have hA : IsSelfAdjoint (h * CE * h⁻¹) := by
      show star (h * CE * h⁻¹) = h * CE * h⁻¹
      have e0 : star (h * CE * h⁻¹) = (h⁻¹)ᴴ * CEᴴ * hᴴ := by
        rw [star_eq_conjTranspose]; simp only [conjTranspose_mul, mul_assoc]
      rw [e0]
      calc (h⁻¹)ᴴ * CEᴴ * hᴴ = (h⁻¹)ᴴ * (CEᴴ * (hᴴ * h)) * h⁻¹ := by simp only [mul_assoc, hinv, mul_one]
        _ = (h⁻¹)ᴴ * ((hᴴ * h) * CE) * h⁻¹ := by rw [hM]
        _ = (h * h⁻¹)ᴴ * (h * CE * h⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
        _ = h * CE * h⁻¹ := by rw [hinv, conjTranspose_one, one_mul]
    let X : Hn r F E := (⟨h * CE * h⁻¹, hA⟩, h *ᵥ ev r E 0, a.2.2)
    have hpow : ∀ k : ℕ, X.1.1 ^ k *ᵥ X.2.1 = h *ᵥ (CE ^ k *ᵥ ev r E 0) := by
      intro k
      show (h * CE * h⁻¹) ^ k *ᵥ (h *ᵥ ev r E 0) = _
      rw [conj_pow' h h⁻¹ CE hinv' hinv, mulVec_mulVec, mul_assoc, hinv', mul_one, ← mulVec_mulVec]
    have hBm : Bm X.toGl = h := by
      ext i j
      show (X.1.1 ^ (j : ℕ) *ᵥ X.2.1) i = h i j
      rw [hpow, hCE, comp_pow_ev p j j.2, mulVec_ev]
    have G := gram X
    rw [hBm, hh] at G
    refine ⟨X, (hasInv_iff X a).2 ⟨?_, ?_, rfl⟩⟩
    · have e1 := pow_r_mulVec X.toGl
      have e2 : X.1.1 ^ r *ᵥ X.2.1 = -(h *ᵥ p) := by
        rw [hpow, hCE, comp_pow_r, mulVec_neg]
      rw [show X.toGl.1 = X.1.1 from rfl, show X.toGl.2.1 = X.2.1 from rfl, e2, hBm, neg_inj] at e1
      have e3 := congrArg (fun v => h⁻¹ *ᵥ v) e1
      simp only [mulVec_mulVec, hinv', one_mulVec] at e3
      intro i
      exact (congrFun e3 i).symm
    · intro i
      have e4 := congrFun (congrFun G ⟨0, i.pos⟩) i
      simp only [map_apply, of_apply, hankel, Fin.val_mk, zero_add] at e4
      rw [← e4, mom_sec_lt]
end Four

theorem herm_invariants : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by
  intro F E _ _ _ _ _ r
  exact ⟨fun X => part1 X, fun g X a h => part2 g X a h, fun X₁ X₂ a hΔ h₁ h₂ => part3 X₁ X₂ a hΔ h₁ h₂,
    fun a hΔ => part4 a hΔ⟩

end GlobalTheory.JR.HermInv
