import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.UHMulInv

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
open ReciprocityTheory.ChartRestriction.DS.Xi.StepA (herm_add_l herm_add_r herm_sub_l herm_sub_r herm_smul_l herm_smul_r herm_zero_l herm_zero_r
  herm_UH Hpk_mulVec Hpk_conjT)

namespace GlobalTheory.Amp.ExtPow

theorem gram_core {n j : ℕ} (P P' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v v' : Fin j → Fin n → ℂ)
    (M : Matrix (Fin j) (Fin j) ℂ)
    (h : ∀ p ∈ P, ∀ p' ∈ P', ‖∑ a, ∑ b, (star (v a) ⬝ᵥ p.ofLp) * M a b * star (star (v' b) ⬝ᵥ p'.ofLp)‖ ≤ 2 * ‖p‖ * ‖p'‖) :
    gramProj P v * gramProj P' v' * ‖M.det‖ ≤ 2 ^ j := by
  have hA : ∀ (Q : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (u : Fin j → Fin n → ℂ),
      ∃ A : Matrix (Fin j) (Fin n) ℂ, (Matrix.gram ℂ fun a => Q.starProjection (WithLp.toLp 2 (u a))) = A * Aᴴ ∧
        ∀ w : Fin n → ℂ, ∑ i, ‖w i‖ ^ 2 ≤ 1 → ∃ p ∈ Q, ‖p‖ ≤ 1 ∧ ∀ a, (A *ᵥ w) a = star (u a) ⬝ᵥ p.ofLp := by
    intro Q u
    refine ⟨Matrix.of fun a i => star ((Q.starProjection (WithLp.toLp 2 (u a))).ofLp i), ?_, ?_⟩
    · ext a b
      rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro l _
      simp [Matrix.conjTranspose_apply, mul_comm]
    · intro w hw
      refine ⟨Q.starProjection (WithLp.toLp 2 w), Q.starProjection_apply_mem _, ?_, fun a => ?_⟩
      · refine (Q.norm_starProjection_apply_le _).trans ?_
        rw [EuclideanSpace.norm_eq]
        simpa using Real.sqrt_le_one.2 hw
      · have e1 : ⟪Q.starProjection (WithLp.toLp 2 (u a)), WithLp.toLp 2 w⟫_ℂ =
            ⟪WithLp.toLp 2 (u a), Q.starProjection (WithLp.toLp 2 w)⟫_ℂ := Q.inner_starProjection_left_eq_right _ _
        rw [PiLp.inner_apply, PiLp.inner_apply] at e1
        simp only [Matrix.mulVec, dotProduct, Pi.star_apply]
        simpa [mul_comm] using e1
  obtain ⟨A, hA1, hA2⟩ := hA P v
  obtain ⟨A', hA1', hA2'⟩ := hA P' v'
  unfold gramProj
  rw [hA1, hA1']
  apply Formalism.HermitianLatticeCounting.P.exterior_power_bound j n A A' M
  intro w₁ w₂ h₁ h₂
  obtain ⟨p, hp, hp1, hp2⟩ := hA2 w₁ h₁
  obtain ⟨p', hp', hp1', hp2'⟩ := hA2' w₂ h₂
  simp only [hp2, hp2']
  refine (h p hp p' hp').trans ?_
  have := norm_nonneg p
  have := norm_nonneg p'
  nlinarith [mul_le_mul hp1 hp1' this zero_le_one]

theorem herm_conj {k r : ℕ} (u v : Fin (2 * r + k + 1) → ℂ) :
    star (herm (Hpk k r) u v) = herm (Hpk k r) v u := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, Hpk_conjT, ← Matrix.dotProduct_mulVec]

theorem herm_cs {k r : ℕ} (S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ))
    (hS : ∀ v ∈ S, 0 ≤ (herm (Hpk k r) v v).re) (u v : Fin (2 * r + k + 1) → ℂ) (hu : u ∈ S) (hv : v ∈ S) :
    ‖herm (Hpk k r) u v‖ ^ 2 ≤ (herm (Hpk k r) u u).re * (herm (Hpk k r) v v).re := by
  let c : PreInnerProductSpace.Core ℂ S :=
    { inner := fun x y => herm (Hpk k r) y x
      conj_inner_symm := fun x y => herm_conj _ _
      re_inner_nonneg := fun x => hS x x.2
      add_left := fun x y z => herm_add_r _ _ _ _
      smul_left := fun x y a => herm_smul_r _ _ _ _ }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ S _ _ _ c ⟨u, hu⟩ ⟨v, hv⟩
  change ‖herm (Hpk k r) v u‖ * ‖herm (Hpk k r) u v‖ ≤ (herm (Hpk k r) u u).re * (herm (Hpk k r) v v).re at h
  rw [← herm_conj u v, norm_star] at h
  rw [sq]; exact h

def Low {n : ℕ} (m : ℕ) (v : Fin n → ℂ) : Prop := ∀ i : Fin n, m ≤ i.val → v i = 0

theorem low_of_mem {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) : Low r v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    intro i hi
    have := a.isLt
    apply Pi.single_eq_of_ne
    intro h; rw [h] at hi; simp [eI] at hi; omega
  | zero => intro i _; rfl
  | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
  | smul a x _ hx => intro i hi; simp [hx i hi]

theorem low_eq {k r j : ℕ} (hj : j ≤ r) {v : Fin (2 * r + k + 1) → ℂ} (hv : Low j v) :
    v = ∑ a : Fin j, v (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj a)) := by
  ext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < j
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · simp [bvec, eI]
    · intro b _ hb
      have : i ≠ eI k r (Fin.castLE hj b) := fun h => hb (Fin.ext (congrArg Fin.val h).symm)
      simp [bvec, Pi.single_eq_of_ne this]
    · simp
  · rw [hv i (by omega), eq_comm]
    apply Finset.sum_eq_zero
    intro b _
    have : i ≠ eI k r (Fin.castLE hj b) := fun h => hi (by rw [h]; exact b.isLt)
    simp [bvec, Pi.single_eq_of_ne this]

theorem low_N {k r j : ℕ} (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : Low j v) :
    Low j (n *ᵥ v) := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : j ≤ l.val
  · rw [hv l hl, mul_zero]
  · have h := hn.2.1 ⟨l.val, by omega⟩ i (by simp; omega)
    have e : eI k r ⟨l.val, by omega⟩ = l := rfl
    rw [e, if_neg (fun h => by rw [h] at hi; omega)] at h
    rw [h, zero_mul]

theorem herm_low {k r : ℕ} {u v : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, herm (Hpk k r) u (bvec (eI k r a)) = 0)
    (hv : Low r v) : herm (Hpk k r) u v = 0 := by
  rw [low_eq le_rfl hv]
  have : ∀ s : Finset (Fin r), herm (Hpk k r) u (∑ a ∈ s, v (eI k r (Fin.castLE le_rfl a)) • bvec (eI k r (Fin.castLE le_rfl a))) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [herm_zero_r]
    | insert a s ha ih => rw [Finset.sum_insert ha, herm_add_r, ih, herm_smul_r, hu]; simp
  exact this _

theorem herm_e {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (eI k r a)) = u (esI k r a) := by
  have : star (bvec (eI k r a)) = bvec (eI k r a) := by simp [bvec]
  unfold herm
  rw [this, bvec, single_one_dotProduct, Hpk_mulVec, if_pos (Or.inl (show (eI k r a).val < r from a.isLt))]
  rfl

theorem herm_low_low {k r : ℕ} {u v : Fin (2 * r + k + 1) → ℂ} (hu : Low r u) (hv : Low r v) :
    herm (Hpk k r) u v = 0 := by
  apply herm_low _ hv
  intro a
  rw [herm_e]
  apply hu
  have := a.isLt
  simp only [esI]; omega

theorem herm_nonneg {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (he : ∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0)
    (hvz : herm (Hpk k r) v z = 0) : 0 ≤ (herm (Hpk k r) v v).re := by
  let y : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then v i else 0
  have hy : Low r y := fun i hi => if_neg (by omega)
  have hw : inWb k r (v - y) := by
    intro i hi
    rcases hi with hi | hi
    · simp [y, hi]
    · have := he ⟨2 * r + k - i.val, by omega⟩
      rw [herm_e] at this
      have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by simp [esI]; omega)
      rw [e] at this
      have h2 : ¬ i.val < r := by omega
      simp [y, h2, this]
  have hvy : herm (Hpk k r) v y = 0 := herm_low he hy
  have hyv : herm (Hpk k r) y v = 0 := by rw [← herm_conj, hvy, star_zero]
  have hzy : herm (Hpk k r) z y = 0 := by
    apply herm_low _ hy
    intro a
    rw [herm_e]
    apply hz
    have := a.isLt
    simp only [esI]; omega
  have hyz : herm (Hpk k r) y z = 0 := by rw [← herm_conj, hzy, star_zero]
  have e1 : herm (Hpk k r) (v - y) (v - y) = herm (Hpk k r) v v := by
    rw [herm_sub_l, herm_sub_r, herm_sub_r, hvy, hyv, herm_low_low hy hy]; ring
  by_contra hneg
  push_neg at hneg
  have h := revCS k r z (v - y) hz hw (by unfold Tz at hT; linarith) (by rw [e1]; exact hneg)
  rw [herm_sub_l, hvz, hyz] at h
  have : 0 < Tz k r (v - y) := by unfold Tz; rw [e1]; linarith
  have := mul_pos hT this
  simp at h
  linarith

theorem low_split {k r j : ℕ} (hj : j ≤ r) {n₁ n₂ g : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (c : ℂ)
    (hg : ∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : Low r v) :
    ∃ u, Low j u ∧ Low r ((n₁ * g * n₂) *ᵥ (v - u)) := by
  have hu2 : IsUnit n₂.det := ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 n₂ h₂.1).1
  have hy := low_N le_rfl h₂ hv
  set y := n₂ *ᵥ v with hyd
  let lo : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < j then y i else 0
  have hlo : Low j lo := fun i hi => if_neg (by omega)
  refine ⟨n₂⁻¹ *ᵥ lo, low_N hj ((nSubgroup k r).2.2 _ h₂) hlo, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec lo,
    Matrix.mul_nonsing_inv _ hu2, Matrix.one_mulVec, ← hyd]
  apply low_N le_rfl h₁
  have hhi : Low r (y - lo) := fun i hi => by
    have : ¬ i.val < j := by omega
    simp [lo, this, hy i hi]
  have e : g *ᵥ (y - lo) = c • (y - lo) := by
    rw [low_eq le_rfl hhi, Matrix.mulVec_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : j ≤ a.val
    · rw [Matrix.mulVec_smul, hg (Fin.castLE le_rfl a) ha, smul_comm]
    · have : (eI k r (Fin.castLE le_rfl a)).val < j := by simp [eI]; omega
      have e0 : (y - lo) (eI k r (Fin.castLE le_rfl a)) = 0 := by
        simp only [Pi.sub_apply, lo, if_pos this, sub_self]
      rw [e0]; simp
  rw [e]
  intro i hi
  simp [hhi i hi]

theorem herm_sum_l {k r j : ℕ} (α : Fin j → ℂ) (f : Fin j → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ a, α a • f a) w = ∑ a, α a * herm (Hpk k r) (f a) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul]

def Zj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (γ : Mat k r) : Matrix (Fin j) (Fin j) ℂ := fun a b =>
  herm (Hpk k r) (γ *ᵥ bvec (eI k r (Fin.castLE hj b))) (bvec (eI k r (Fin.castLE hj a)))

theorem Dj_eq {k r j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) :
    Dj k r hj z z' γ = ‖(Zj k r hj γ).det‖ := by
  unfold Dj Dmin
  congr 2
  ext a b
  have ha : a.val < r := lt_of_lt_of_le a.isLt hj
  have hb : b.val < r := lt_of_lt_of_le b.isLt hj
  simp only [Matrix.submatrix_apply, Zhat, fvec, Zj, Fin.val_castLE, ha, hb, dif_pos]
  rfl

theorem unit_det {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det ∧ g⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 g hg

theorem mul_GG {k r : ℕ} {g h : Mat k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r :=
  (uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.1 g hg h hh

theorem herm_adj {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u (g⁻¹ *ᵥ v) = herm (Hpk k r) (g *ᵥ u) v := by
  rw [← herm_UH _ hg, Matrix.mulVec_mulVec v, Matrix.mul_nonsing_inv _ (unit_det hg).1, Matrix.one_mulVec]

theorem herm_adj' {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ u) v = herm (Hpk k r) u (g *ᵥ v) := by
  rw [← herm_UH _ hg, Matrix.mulVec_mulVec u, Matrix.mul_nonsing_inv _ (unit_det hg).1, Matrix.one_mulVec]

theorem Zj_inv {k r j : ℕ} (hj : j ≤ r) {γ : Mat k r} (hγ : γ ∈ GG k r) : Zj k r hj γ⁻¹ = (Zj k r hj γ)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply, Zj, Zj, herm_conj, herm_adj' hγ]

theorem mem_Ppos {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ x : Mat k r} {p : EuclideanSpace ℂ (Fin (2 * r + k + 1))}
    (hp : p ∈ Ppos k r z z' γ x) :
    Hpk k r *ᵥ p.ofLp = p.ofLp ∧ ∃ h y, x *ᵥ p.ofLp = h + y ∧ Low r y ∧
      (∀ a : Fin r, herm (Hpk k r) h (bvec (eI k r a)) = 0) ∧ herm (Hpk k r) h z' = 0 ∧
      (∀ a : Fin r, herm (Hpk k r) h (γ⁻¹ *ᵥ bvec (eI k r a)) = 0) ∧ herm (Hpk k r) h (γ⁻¹ *ᵥ z) = 0 := by
  obtain ⟨h1, h2⟩ := hp
  have h1' : (Hpk k r - 1) *ᵥ p.ofLp = 0 := h1
  have h2' : x *ᵥ p.ofLp ∈ Hcom k r z z' γ ⊔ Xsp k r := h2
  obtain ⟨h, hh, y, hy, e⟩ := Submodule.mem_sup.1 h2'
  have f1 : ∀ (t : Fin (2 * r + k + 1) → ℂ) (a : Fin r), fvec k r t a.castSucc = bvec (eI k r a) := by
    intro t a; simp [fvec]
  have f2 : ∀ (t : Fin (2 * r + k + 1) → ℂ), fvec k r t (Fin.last r) = t := by
    intro t; simp [fvec]
  refine ⟨?_, h, y, e.symm, low_of_mem hy, fun a => ?_, ?_, fun a => ?_, ?_⟩
  · rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1'
  · rw [← f1 z' a]; exact (hh _).1
  · rw [← f2 z']; exact (hh _).1
  · rw [← f1 z a]; exact (hh _).2
  · rw [← f2 z]; exact (hh _).2

theorem herm_pos_eq {k r : ℕ} {p : EuclideanSpace ℂ (Fin (2 * r + k + 1))} (hp : Hpk k r *ᵥ p.ofLp = p.ofLp)
    (q : EuclideanSpace ℂ (Fin (2 * r + k + 1))) : herm (Hpk k r) p.ofLp q.ofLp = ⟪q, p⟫_ℂ := by
  unfold herm
  rw [hp, PiLp.inner_apply]
  simp [dotProduct, mul_comm]

theorem bound_of_split {k r j : ℕ} (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {γ : Mat k r} (hγ : γ ∈ GG k r)
    (s₁ : ∀ v, Low r v → ∃ u, Low j u ∧ Low r (γ *ᵥ (v - u)))
    (s₂ : ∀ v, Low r v → ∃ u, Low j u ∧ Low r (γ⁻¹ *ᵥ (v - u)))
    {x : Mat k r} (hx : x ∈ GG k r) :
    Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  have hγγ : γ⁻¹⁻¹ = γ := Matrix.nonsing_inv_nonsing_inv _ (unit_det hγ).1
  have hγx := mul_GG hγ hx
  unfold Yj
  rw [Dj_eq, Dj_eq, Zj_inv hj hγ, Matrix.det_conjTranspose, norm_star]
  set Z := Zj k r hj γ with hZ
  by_cases hd : Z.det = 0
  · rw [hd, norm_zero, mul_zero]; positivity
  have hd' : ‖Z.det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.2 hd
  refine le_of_eq_of_le ?_ (gram_core (Ppos k r z z' γ x) (Ppos k r z' z γ⁻¹ (γ * x))
    (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))))
    (fun a : Fin j => (γ * x)⁻¹ *ᵥ (γ⁻¹⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) (Z⁻¹)ᵀ ?_)
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv]
    field_simp
  intro p hp p' hp'
  obtain ⟨hHp, h₁, y₁, e₁, hy₁, a₀, -, a₁, b₁⟩ := mem_Ppos hp
  obtain ⟨hHp', h', y₂, e₂, hy₂, a₂, b₂, c₂, -⟩ := mem_Ppos hp'
  rw [hγγ] at c₂ ⊢
  simp only [herm_adj hγ] at a₁ b₁
  set h := γ *ᵥ h₁ with hh
  have ew : (γ * x) *ᵥ p.ofLp = h + γ *ᵥ y₁ := by rw [← Matrix.mulVec_mulVec, e₁, Matrix.mulVec_add]
  have hc : ∀ v, Low r v → herm (Hpk k r) h (γ *ᵥ v) = 0 := fun v hv => by
    rw [hh, herm_UH _ hγ]; exact herm_low a₀ hv
  have hc' : ∀ v, Low r v → herm (Hpk k r) h' (γ *ᵥ v) = 0 := fun v hv => by
    rw [← herm_adj' hγ]; exact herm_low (fun a => by rw [herm_adj' hγ]; exact c₂ a) hv
  have sw : ∀ u v, herm (Hpk k r) u v = 0 → herm (Hpk k r) v u = 0 := fun u v e => by
    rw [← herm_conj, e, star_zero]
  have n₁ : herm (Hpk k r) h h = ⟪p, p⟫_ℂ := by
    rw [← herm_pos_eq hHp, ← herm_UH _ hγx p.ofLp, ew, herm_add_l, herm_add_r, herm_add_r, hc _ hy₁, sw _ _ (hc _ hy₁),
      herm_UH _ hγ y₁, herm_low_low hy₁ hy₁]; ring
  have n₂ : herm (Hpk k r) h' h' = ⟪p', p'⟫_ℂ := by
    rw [← herm_pos_eq hHp', ← herm_UH _ hγx p'.ofLp, e₂, herm_add_l, herm_add_r, herm_add_r, herm_low a₂ hy₂,
      sw _ _ (herm_low a₂ hy₂), herm_low_low hy₂ hy₂]; ring
  have n₃ : herm (Hpk k r) (γ *ᵥ y₁) y₂ = ⟪p', p⟫_ℂ - herm (Hpk k r) h h' := by
    rw [← herm_pos_eq hHp, ← herm_UH _ hγx p.ofLp, ew, e₂, herm_add_l, herm_add_r, herm_add_r, herm_low a₁ hy₂,
      sw _ _ (hc' _ hy₁)]; ring
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
    { carrier := {v | (∀ a : Fin r, herm (Hpk k r) v (bvec (eI k r a)) = 0) ∧ herm (Hpk k r) v z = 0}
      zero_mem' := ⟨fun a => herm_zero_l _ _, herm_zero_l _ _⟩
      add_mem' := fun {u v} hu hv => ⟨fun a => by rw [herm_add_l, hu.1, hv.1, add_zero],
        by rw [herm_add_l, hu.2, hv.2, add_zero]⟩
      smul_mem' := fun c v hv => ⟨fun a => by rw [herm_smul_l, hv.1, mul_zero], by rw [herm_smul_l, hv.2, mul_zero]⟩ }
  have cs := herm_cs S (fun v hv => herm_nonneg hz hT hv.1 hv.2) h h' ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  have ip : ∀ q : EuclideanSpace ℂ (Fin (2 * r + k + 1)), (⟪q, q⟫_ℂ).re = ‖q‖ ^ 2 := fun q =>
    inner_self_eq_norm_sq (𝕜 := ℂ) q
  rw [n₁, n₂, ip, ip, ← mul_pow] at cs
  have cs' : ‖herm (Hpk k r) h h'‖ ≤ ‖p‖ * ‖p'‖ := le_of_pow_le_pow_left₀ two_ne_zero (by positivity) cs
  have bd : ‖herm (Hpk k r) (γ *ᵥ y₁) y₂‖ ≤ 2 * ‖p‖ * ‖p'‖ := by
    rw [n₃]
    have := norm_inner_le_norm (𝕜 := ℂ) p' p
    have := norm_sub_le ⟪p', p⟫_ℂ (herm (Hpk k r) h h')
    linarith
  refine le_of_eq_of_le (congrArg _ ?_) bd
  obtain ⟨u₁, hu₁, hv₁⟩ := s₁ y₁ hy₁
  obtain ⟨u₂, hu₂, hv₂⟩ := s₂ y₂ hy₂
  have le : ∀ a : Fin r, Low r (bvec (eI k r a)) := fun a => low_of_mem (Submodule.subset_span ⟨a, rfl⟩)
  have lu₁ : Low r u₁ := fun i hi => hu₁ i (hj.trans hi)
  have lu₂ : Low r u₂ := fun i hi => hu₂ i (hj.trans hi)
  obtain ⟨α, hα⟩ : ∃ α : Fin j → ℂ, u₁ = ∑ a, α a • bvec (eI k r (Fin.castLE hj a)) := ⟨_, low_eq hj hu₁⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin j → ℂ, u₂ = ∑ a, β a • bvec (eI k r (Fin.castLE hj a)) := ⟨_, low_eq hj hu₂⟩
  have r₁ : ∀ v, Low r v → herm (Hpk k r) (γ *ᵥ y₁) v = herm (Hpk k r) (γ *ᵥ u₁) v := fun v hv => by
    have := herm_low_low hv₁ hv
    rwa [Matrix.mulVec_sub, herm_sub_l, sub_eq_zero] at this
  have r₂ : ∀ v, Low r v → herm (Hpk k r) y₂ (γ *ᵥ v) = herm (Hpk k r) u₂ (γ *ᵥ v) := fun v hv => by
    have := herm_low_low hv₂ hv
    rwa [herm_adj' hγ, herm_sub_l, sub_eq_zero] at this
  have g₁ : γ *ᵥ u₁ = ∑ a, α a • (γ *ᵥ bvec (eI k r (Fin.castLE hj a))) := by
    rw [hα, Matrix.mulVec_sum]; simp only [Matrix.mulVec_smul]
  have k₁ : ∀ a : Fin j, star (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) ⬝ᵥ p.ofLp = (Z *ᵥ α) a := fun a => by
    have : star (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) ⬝ᵥ p.ofLp =
        herm (Hpk k r) p.ofLp (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) := by rw [herm, hHp]
    rw [this, herm_adj hx, herm_adj hγ, Matrix.mulVec_mulVec, ew, herm_add_l, a₁, zero_add, r₁ _ (le _), g₁, herm_sum_l]
    simp only [Matrix.mulVec, dotProduct, mul_comm]
    rfl
  have k₂ : ∀ b : Fin j, star (star ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) ⬝ᵥ p'.ofLp) =
      (star β ᵥ* Z) b := fun b => by
    have : star ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) ⬝ᵥ p'.ofLp =
        herm (Hpk k r) p'.ofLp ((γ * x)⁻¹ *ᵥ (γ *ᵥ bvec (eI k r (Fin.castLE hj b)))) := by rw [herm, hHp']
    rw [this, herm_adj hγx, e₂, herm_add_l, c₂, zero_add, r₂ _ (le _), hβ, herm_sum_l, star_sum]
    simp only [star_mul', herm_conj]
    rfl
  have k₃ : herm (Hpk k r) (γ *ᵥ y₁) y₂ = star β ⬝ᵥ (Z *ᵥ α) := by
    rw [r₁ _ hy₂, ← herm_conj, r₂ _ lu₁, hβ, herm_sum_l, star_sum]
    simp only [star_mul', herm_conj]
    simp only [g₁, herm_sum_l]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  simp only [k₁, k₂]
  rw [k₃]
  have : star β ⬝ᵥ (Z *ᵥ α) = (star β ᵥ* Z) ⬝ᵥ (Z⁻¹ *ᵥ (Z *ᵥ α)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.dotProduct_mulVec]
  rw [this]
  generalize star β ᵥ* Z = s
  generalize Z *ᵥ α = t
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem gram_mul_minor_le : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ)
    (μR : Measure (Mt k r)), IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ x ∈ GG k r,
    Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  rintro k r j hj z z' γ s μR ⟨hz, -, hT, n₁, h₁, n₂, h₂, g, β, c, ⟨hg, hc, -, -, -, -, he, -⟩, rfl, -⟩ x hx
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  refine bound_of_split hj hz hT (mul_GG (mul_GG h₁.1 hg) h₂.1)
    (fun v hv => low_split hj h₁ h₂ c (fun a ha => (he a ha).1) hv) (fun v hv => ?_) hx
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc]
  refine low_split hj ((nSubgroup k r).2.2 _ h₂) ((nSubgroup k r).2.2 _ h₁) c⁻¹ (fun a ha => ?_) hv
  have e := congrArg (fun v => g⁻¹ *ᵥ v) (he a ha).1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det hg).1, Matrix.one_mulVec, Matrix.mulVec_smul] at e
  conv_rhs => rw [e]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

end GlobalTheory.Amp.ExtPow
