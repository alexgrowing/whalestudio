import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

open Filter Topology

namespace GlobalTheory.ConeSq

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def sq (l : ι → ℤ) : Matrix ι ι ℝ := vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))

def cone (S : Finset (ι → ℤ)) : Set (Matrix ι ι ℝ) :=
  {P | ∃ c : (ι → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • sq l}

theorem zero_mem (S : Finset (ι → ℤ)) : (0 : Matrix ι ι ℝ) ∈ cone S :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem add_mem {S : Finset (ι → ℤ)} {P Q : Matrix ι ι ℝ} (hP : P ∈ cone S) (hQ : Q ∈ cone S) :
    P + Q ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  obtain ⟨d, hd, rfl⟩ := hQ
  exact ⟨c + d, fun l => add_nonneg (hc l) (hd l), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem smul_mem {S : Finset (ι → ℤ)} {P : Matrix ι ι ℝ} {a : ℝ} (ha : 0 ≤ a) (hP : P ∈ cone S) :
    a • P ∈ cone S := by
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨a • c, fun l => mul_nonneg ha (hc l), by simp [Finset.smul_sum, smul_smul]⟩

theorem mono {S T : Finset (ι → ℤ)} (h : S ⊆ T) {P : Matrix ι ι ℝ} (hP : P ∈ cone S) :
    P ∈ cone T := by
  obtain ⟨c, hc, rfl⟩ := hP
  refine ⟨fun l => if l ∈ S then c l else 0, fun l => by dsimp only; split_ifs <;> simp [hc], ?_⟩
  rw [← Finset.sum_subset h (fun l _ hl => by simp [hl])]
  exact Finset.sum_congr rfl fun l hl => by simp [hl]

theorem sq_mem {S : Finset (ι → ℤ)} {l : ι → ℤ} (hl : l ∈ S) : sq l ∈ cone S := by
  refine ⟨fun m => if m = l then 1 else 0, fun m => by dsimp only; split_ifs <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single l (fun m _ hm => by simp [hm]) (fun h => absurd hl h)]
  simp

theorem sum_mem {S : Finset (ι → ℤ)} {κ : Type} (s : Finset κ) {f : κ → Matrix ι ι ℝ}
    (h : ∀ k ∈ s, f k ∈ cone S) : ∑ k ∈ s, f k ∈ cone S :=
  Finset.sum_induction f (· ∈ cone S) (fun _ _ => add_mem) (zero_mem S) h

def plus (i j : ι) : ι → ℤ := Pi.single i 1 + Pi.single j 1

def minus (i j : ι) : ι → ℤ := Pi.single i 1 - Pi.single j 1

def gens : Finset (ι → ℤ) :=
  Finset.univ.image (fun p : ι × ι => plus p.1 p.2) ∪ Finset.univ.image (fun p : ι × ι => minus p.1 p.2)

def bsum : Matrix ι ι ℝ := ∑ p : ι × ι, (sq (plus p.1 p.2) + sq (minus p.1 p.2))

theorem sq_plus_sub_sq_minus (i j a b : ι) :
    sq (plus i j) a b - sq (minus i j) a b =
      2 * ((if a = i ∧ b = j then 1 else 0) + (if a = j ∧ b = i then 1 else 0)) := by
  simp only [sq, plus, minus, vecMulVec_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply,
    Int.cast_add, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rcases eq_or_ne i j with rfl | hij
  · by_cases h1 : a = i <;> by_cases h3 : b = i <;> simp [h1, h3] <;> norm_num
  · by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;> by_cases h4 : b = j <;>
      first
      | exact absurd (h1.symm.trans h2) hij
      | exact absurd (h3.symm.trans h4) hij
      | (simp [h1, h2, h3, h4, hij, hij.symm]; try norm_num)

theorem eq_sum_sq_sub (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a) :
    M = ∑ p : ι × ι, (M p.1 p.2 / 4) • (sq (plus p.1 p.2) - sq (minus p.1 p.2)) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, sq_plus_sub_sq_minus]
  rw [Fintype.sum_prod_type]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [hM b a]; ring

theorem shift_mem (t : ℝ) (M : Matrix ι ι ℝ) (hM : ∀ a b, M a b = M b a)
    (hb : ∀ a b, |M a b| ≤ 4 * t) : t • bsum + M ∈ cone gens := by
  have e : t • bsum + M = ∑ p : ι × ι, ((t + M p.1 p.2 / 4) • sq (plus p.1 p.2)
      + (t - M p.1 p.2 / 4) • sq (minus p.1 p.2)) := by
    conv_lhs => rw [eq_sum_sq_sub M hM]
    rw [bsum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    module
  rw [e]
  refine sum_mem _ fun p _ => add_mem (smul_mem ?_ (sq_mem ?_)) (smul_mem ?_ (sq_mem ?_))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  · have := abs_le.mp (hb p.1 p.2); linarith
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))

theorem sq_symm (l : ι → ℤ) (a b : ι) : sq l a b = sq l b a := by
  simp only [sq, vecMulVec_apply, mul_comm]

theorem bsum_symm (a b : ι) : (bsum : Matrix ι ι ℝ) a b = bsum b a := by
  simp only [bsum, Matrix.sum_apply, Matrix.add_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [sq_symm _ a b, sq_symm (minus p.1 p.2) a b]

theorem quad_eq (M : Matrix ι ι ℝ) (c : ι → ℝ) :
    star c ⬝ᵥ (M *ᵥ c) = ∑ i, ∑ j, c i * c j * M i j := by
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tendsto_floor_div (x : ℝ) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) * x⌋ : ℤ) : ℝ) / N) atTop (𝓝 x) := by
  have h1 : Tendsto (fun N : ℕ => x - 1 / (N : ℝ)) atTop (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    have := Int.lt_floor_add_one ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    rw [div_le_iff₀ hN']
    have := Int.floor_le ((N : ℝ) * x)
    linarith [mul_comm x (N : ℝ)]

open scoped MatrixOrder in

theorem local_step (P₀ : Matrix ι ι ℝ) (h : P₀.PosDef) :
    ∃ S : Finset (ι → ℤ), ∀ᶠ P in 𝓝 P₀, P.IsHermitian → P ∈ cone S := by
  have hP₀s : ∀ a b, P₀ a b = P₀ b a := fun a b => by
    have := h.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  obtain ⟨η, hη, hmar⟩ := GlobalTheory.posDef_quad_margin (fun i j => P₀ i j) (fun c hc => by
    have := h.dotProduct_mulVec_pos hc
    rwa [quad_eq] at this)
  set β : ℝ := ∑ a, ∑ b, |(bsum : Matrix ι ι ℝ) a b| + 1 with hβdef
  have hβ : 0 < β := by positivity
  have hbβ : ∀ a b, |(bsum : Matrix ι ι ℝ) a b| ≤ β := fun a b => by
    have h1 : |(bsum : Matrix ι ι ℝ) a b| ≤ ∑ b', |(bsum : Matrix ι ι ℝ) a b'| :=
      Finset.single_le_sum (f := fun b' => |(bsum : Matrix ι ι ℝ) a b'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : ∑ b', |(bsum : Matrix ι ι ℝ) a b'| ≤ ∑ a', ∑ b', |(bsum : Matrix ι ι ℝ) a' b'| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |(bsum : Matrix ι ι ℝ) a' b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  set t : ℝ := η / (2 * β) with htdef
  have ht : 0 < t := by positivity
  set G : Matrix ι ι ℝ := P₀ - (2 * t) • bsum with hGdef
  have hGs : ∀ a b, G a b = G b a := fun a b => by
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hP₀s a b, bsum_symm a b]
  have hG : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨IsHermitian.ext fun a b => by rw [star_trivial, hGs], fun c => ?_⟩
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    rw [quad_eq]
    have := hmar (fun a b => -(2 * t) * bsum a b) (fun a b => by
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      calc 2 * t * |(bsum : Matrix ι ι ℝ) a b| ≤ 2 * t * β := by gcongr; exact hbβ a b
        _ = η := by rw [htdef]; field_simp) c hc
    refine this.le.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    simp only [hGdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set R : Matrix ι ι ℝ := CFC.sqrt G with hRdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hRR : R * R = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hRs : ∀ a b, R a b = R b a := fun a b => by
    have := hR.isHermitian.apply a b
    rw [star_trivial] at this
    exact this.symm
  have hGsum : ∀ a b, G a b = ∑ k, R k a * R k b := fun a b => by
    rw [← hRR, mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hRs a k]
  have hconv : ∀ a b, Tendsto (fun N : ℕ => ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N)) atTop (𝓝 (G a b)) := fun a b => by
    rw [hGsum]
    exact tendsto_finset_sum _ fun k _ => (tendsto_floor_div _).mul (tendsto_floor_div _)
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∀ a b, |∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) - G a b| < t :=
    (eventually_gt_atTop 0).and (eventually_all.2 fun a => eventually_all.2 fun b =>
      (hconv a b).eventually (eventually_abs_sub_lt _ ht))
  obtain ⟨N, hN, hNt⟩ := hev.exists
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set m : ι → ι → ℤ := fun k a => ⌊(N : ℝ) * R k a⌋ with hmdef
  set Q : Matrix ι ι ℝ := ∑ k, (1 / (N : ℝ) ^ 2) • sq (m k) with hQdef
  have hQ : ∀ a b, Q a b = ∑ k, ((⌊(N : ℝ) * R k a⌋ : ℤ) : ℝ) / N *
      (((⌊(N : ℝ) * R k b⌋ : ℤ) : ℝ) / N) := fun a b => by
    simp only [hQdef, hmdef, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, sq, vecMulVec_apply]
    exact Finset.sum_congr rfl fun k _ => by field_simp
  have hQs : ∀ a b, Q a b = Q b a := fun a b => by
    rw [hQ, hQ]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQmem : Q ∈ cone (Finset.univ.image m) :=
    sum_mem _ fun k _ => smul_mem (by positivity) (sq_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  refine ⟨gens ∪ Finset.univ.image m, ?_⟩
  have hnear : ∀ᶠ P in 𝓝 P₀, ∀ a b, |P a b - P₀ a b| < t :=
    eventually_all.2 fun a => eventually_all.2 fun b =>
      ((continuous_id.matrix_elem a b).tendsto P₀).eventually (eventually_abs_sub_lt _ ht)
  filter_upwards [hnear] with P hP hPh
  have hPs : ∀ a b, P a b = P b a := fun a b => by
    have := hPh.apply a b
    rw [star_trivial] at this
    exact this.symm
  set M : Matrix ι ι ℝ := (P - P₀) + (G - Q) with hMdef
  have e : P = Q + ((2 * t) • bsum + M) := by
    rw [hMdef, hGdef]; abel
  rw [e]
  refine add_mem (mono Finset.subset_union_right hQmem)
    (mono Finset.subset_union_left (shift_mem _ M ?_ ?_))
  · intro a b
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    rw [hPs a b, hP₀s a b, hGs a b, hQs a b]
  · intro a b
    have h1 := hP a b
    have h2 := hNt a b
    rw [← hQ] at h2
    simp only [hMdef, Matrix.add_apply, Matrix.sub_apply]
    have h3 := abs_add_le (P a b - P₀ a b) (G a b - Q a b)
    rw [abs_sub_comm (G a b)] at h3
    linarith

theorem exists_finset_cone : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (𝒦 : Set (Matrix ι ι ℝ)),
    IsCompact 𝒦 → (∀ P ∈ 𝒦, P.PosDef) → ∃ S : Finset (ι → ℤ), ∀ P ∈ 𝒦, ∃ c : (ι → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro ι _ _ 𝒦 hK hpd
  choose S hS using fun P (hP : P ∈ 𝒦) => local_step P (hpd P hP)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover'
    (fun P hP => {Q : Matrix ι ι ℝ | Q.IsHermitian → Q ∈ cone (S P hP)}) hS
  refine ⟨t.biUnion (fun x => S x.1 x.2), fun P hP => ?_⟩
  obtain ⟨x, hx, hPx⟩ := Set.mem_iUnion₂.mp (ht hP)
  exact mono (Finset.subset_biUnion_of_mem _ hx) (hPx (hpd P hP).isHermitian)

end GlobalTheory.ConeSq
