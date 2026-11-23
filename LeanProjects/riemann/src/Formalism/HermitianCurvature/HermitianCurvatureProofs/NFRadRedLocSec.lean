import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Trans

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

def tth (a b : Fin m → ℂ) : ℂ := -(herm H a b / ((‖herm H a b‖ : ℝ) : ℂ))

def tmat (a b : Fin m → ℂ) (q : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  TwoByOneBlock.qrefl H b ((star (tth H a b) - 1) / (q : ℂ)) *
    TwoByOneBlock.qrefl H (a + (-(tth H a b)) • b) (-1 / ((q : ℂ) - ((-‖herm H a b‖ : ℝ) : ℂ)))

variable {H}

theorem trans_expl (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : q ≠ 0)
    (ha : herm H a a = q) (hb : herm H b b = q) (θ : ℂ) (t : ℝ) (hθ : θ * star θ = 1)
    (ht : star θ * herm H a b = t) (hqt : q * t ≤ 0) :
    TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t)) ∈ UH H ∧
    (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 →
      (TwoByOneBlock.qrefl H b ((star θ - 1) / q) * TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t))) *ᵥ x = x := by
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq
  have hsq : star (q : ℂ) = q := Complex.conj_ofReal q
  have hst : star (t : ℂ) = t := Complex.conj_ofReal t
  have hqt' : (q : ℂ) - t ≠ 0 := by
    rw [← Complex.ofReal_sub]
    refine Complex.ofReal_ne_zero.2 fun h0 => hq ?_
    have e : t = q := by linarith
    rw [e] at hqt
    exact mul_self_eq_zero.1 (le_antisymm hqt (mul_self_nonneg q))
  have hba : herm H b a = star (herm H a b) := TwoByOneBlock.herm_symm H hH a b
  have ht' : θ * herm H b a = t := by
    have e := congrArg star ht
    rw [star_mul', star_star, hst] at e
    rw [hba]; exact e

  have mul_mem : ∀ g h : Matrix (Fin m) (Fin m) ℂ, g ∈ UH H → h ∈ UH H → g * h ∈ UH H := by
    intro g h hg hh
    have hg' : gᴴ * H * g = H := hg
    have hh' : hᴴ * H * h = H := hh
    show (g * h)ᴴ * H * (g * h) = H
    calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hg', hh']
  have hc1 : (star θ - 1) / (q : ℂ) + star ((star θ - 1) / (q : ℂ)) +
      (star θ - 1) / (q : ℂ) * star ((star θ - 1) / (q : ℂ)) * herm H b b = 0 := by
    have hs1 : star ((star θ - 1) / (q : ℂ)) = (θ - 1) / q := by
      rw [star_div₀, star_sub, star_star, star_one, hsq]
    rw [hs1, hb]
    have e : (star θ - 1) / (q : ℂ) + (θ - 1) / q + (star θ - 1) / q * ((θ - 1) / q) * q =
        (θ * star θ - 1) / q := by
      field_simp
      ring
    rw [e, hθ, sub_self, zero_div]
  have hD : herm H (a + (-θ) • b) (a + (-θ) • b) = 2 * ((q : ℂ) - t) := by
    rw [TwoByOneBlock.herm_add_left, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_left,
      TwoByOneBlock.herm_smul_left, TwoByOneBlock.herm_smul_right, TwoByOneBlock.herm_smul_right, ha, hb, star_neg]
    linear_combination (-1 : ℂ) * ht + (-1 : ℂ) * ht' + (q : ℂ) * hθ
  have hc2 : -1 / ((q : ℂ) - t) + star (-1 / ((q : ℂ) - t)) +
      -1 / ((q : ℂ) - t) * star (-1 / ((q : ℂ) - t)) * herm H (a + (-θ) • b) (a + (-θ) • b) = 0 := by
    have hs2 : star (-1 / ((q : ℂ) - t)) = -1 / ((q : ℂ) - t) := by
      rw [star_div₀, star_neg, star_one, star_sub, hsq, hst]
    rw [hs2, hD]
    field_simp
    ring
  have hA : herm H a (a + (-θ) • b) = (q : ℂ) - t := by
    rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, ha, ← ht, star_neg]
    ring
  have h2a : TwoByOneBlock.qrefl H (a + (-θ) • b) (-1 / ((q : ℂ) - t)) *ᵥ a = θ • b := by
    rw [TwoByOneBlock.qrefl_mulVec, hA, div_mul_cancel₀ _ hqt']
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1b : TwoByOneBlock.qrefl H b ((star θ - 1) / q) *ᵥ (θ • b) = b := by
    rw [TwoByOneBlock.qrefl_mulVec, TwoByOneBlock.herm_smul_left, hb]
    have e : (star θ - 1) / (q : ℂ) * (θ * q) = 1 - θ := by
      rw [mul_comm θ, ← mul_assoc, div_mul_cancel₀ _ hq']
      linear_combination hθ
    rw [e]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨mul_mem _ _ (TwoByOneBlock.qrefl_mem H hH b _ hc1) (TwoByOneBlock.qrefl_mem H hH _ _ hc2), ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, h2a, h1b]
  · intro x hxa hxb
    have hxd : herm H x (a + (-θ) • b) = 0 := by
      rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, hxa, hxb]
      ring
    rw [← Matrix.mulVec_mulVec, TwoByOneBlock.qrefl_mulVec H (a + (-θ) • b) _ x, hxd, mul_zero, zero_smul, add_zero,
      TwoByOneBlock.qrefl_mulVec, hxb, mul_zero, zero_smul, add_zero]

theorem tmat_spec (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : herm H a a = q) (hb : herm H b b = q) (hs : herm H a b ≠ 0) :
    tmat H a b q ∈ UH H ∧ tmat H a b q *ᵥ a = b ∧
    ∀ x, herm H x a = 0 → herm H x b = 0 → tmat H a b q *ᵥ x = x := by
  have hs' : ‖herm H a b‖ ≠ 0 := norm_ne_zero_iff.2 hs
  have hsc : ((‖herm H a b‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs'
  have hsn : star ((‖herm H a b‖ : ℝ) : ℂ) = ‖herm H a b‖ := Complex.conj_ofReal _
  have hm : herm H a b * star (herm H a b) = ((‖herm H a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm]; exact Complex.mul_conj _
  have hθ : tth H a b * star (tth H a b) = 1 := by
    unfold tth
    rw [star_neg, star_div₀, hsn, neg_mul_neg, div_mul_div_comm, hm, div_eq_one_iff_eq (mul_ne_zero hsc hsc)]
    push_cast
    ring
  have ht : star (tth H a b) * herm H a b = ((-‖herm H a b‖ : ℝ) : ℂ) := by
    unfold tth
    rw [star_neg, star_div₀, hsn, neg_mul, div_mul_eq_mul_div, mul_comm (star (herm H a b)), hm]
    push_cast
    field_simp
  have hqt : q * (-‖herm H a b‖) ≤ 0 := by nlinarith [norm_nonneg (herm H a b)]
  unfold tmat
  exact trans_expl hH a b q hq.ne' ha hb _ _ hθ ht hqt

end Trans

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}

theorem cdm_iff {F : X → Matrix (Fin m) (Fin m) ℂ} :
    ContDiffOn ℝ n F s ↔ ∀ i j, ContDiffOn ℝ n (fun x => F x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.1 (contDiffOn_pi.1 h i) j
  · intro h
    exact contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => h i j

theorem cdm_mul {F G : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) (hG : ContDiffOn ℝ n G s) :
    ContDiffOn ℝ n (fun x => F x * G x) s := by
  refine cdm_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => ((cdm_iff.1 hF) i k).mul ((cdm_iff.1 hG) k j)

theorem cd_star {f : X → ℂ} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => star (f x)) s := by
  exact Complex.conjCLE.contDiff.comp_contDiffOn hf

theorem cd_ofReal {f : X → ℝ} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => (f x : ℂ)) s := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf

theorem cd_div {f g : X → ℂ} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h0 : ∀ x ∈ s, g x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x / g x) s := by
  have hinv : ContDiffOn ℝ n (fun x => (g x)⁻¹) s := fun x hx =>
    (contDiffAt_inv ℝ (h0 x hx)).comp_contDiffWithinAt x (hg x hx)
  simpa only [div_eq_mul_inv] using hf.mul hinv

theorem cdm_conjT {F : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun x => (F x)ᴴ) s := by
  refine cdm_iff.2 fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact cd_star ((cdm_iff.1 hF) j i)

theorem cdv_mulVec {F : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) (v : Fin m → ℂ) :
    ContDiffOn ℝ n (fun x => F x *ᵥ v) s := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => ((cdm_iff.1 hF) i j).mul contDiffOn_const

theorem cdv_smul {c : X → ℂ} {v : X → Fin m → ℂ} (hc : ContDiffOn ℝ n c s) (hv : ContDiffOn ℝ n v s) :
    ContDiffOn ℝ n (fun x => c x • v x) s := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (contDiffOn_pi.1 hv i)

theorem cd_herm (H : Matrix (Fin m) (Fin m) ℂ) {A B : X → Fin m → ℂ} (hA : ContDiffOn ℝ n A s)
    (hB : ContDiffOn ℝ n B s) : ContDiffOn ℝ n (fun x => herm H (A x) (B x)) s := by
  have hHA : ContDiffOn ℝ n (fun x => H *ᵥ A x) s := by
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiffOn.sum fun j _ => contDiffOn_const.mul (contDiffOn_pi.1 hA j)
  simp only [herm, dotProduct, Pi.star_apply]
  exact ContDiffOn.sum fun i _ => (cd_star (contDiffOn_pi.1 hB i)).mul (contDiffOn_pi.1 hHA i)

theorem cdm_qrefl (H : Matrix (Fin m) (Fin m) ℂ) {d : X → Fin m → ℂ} {c : X → ℂ} (hd : ContDiffOn ℝ n d s)
    (hc : ContDiffOn ℝ n c s) : ContDiffOn ℝ n (fun x => TwoByOneBlock.qrefl H (d x) (c x)) s := by
  refine cdm_iff.2 fun i j => ?_
  simp only [TwoByOneBlock.qrefl, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.vecMul, dotProduct, Pi.star_apply]
  exact contDiffOn_const.add (hc.mul ((contDiffOn_pi.1 hd i).mul
    (ContDiffOn.sum fun k _ => (cd_star (contDiffOn_pi.1 hd k)).mul contDiffOn_const)))

theorem cdm_tmat (H : Matrix (Fin m) (Fin m) ℂ) {A B : X → Fin m → ℂ} {Q : X → ℝ} (hA : ContDiffOn ℝ n A s)
    (hB : ContDiffOn ℝ n B s) (hQ : ContDiffOn ℝ n Q s) (hs : ∀ x ∈ s, herm H (A x) (B x) ≠ 0)
    (hq : ∀ x ∈ s, 0 < Q x) : ContDiffOn ℝ n (fun x => tmat H (A x) (B x) (Q x)) s := by
  have hh : ContDiffOn ℝ n (fun x => herm H (A x) (B x)) s := cd_herm H hA hB
  have hn : ContDiffOn ℝ n (fun x => ‖herm H (A x) (B x)‖) s := hh.norm ℝ hs
  have htth : ContDiffOn ℝ n (fun x => tth H (A x) (B x)) s := by
    unfold tth
    refine (cd_div hh (cd_ofReal hn) fun x hx => ?_).neg
    exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hs x hx))
  unfold tmat
  refine cdm_mul (cdm_qrefl H hB ?_) (cdm_qrefl H (hA.add (cdv_smul htth.neg hB)) ?_)
  · exact cd_div ((cd_star htth).sub contDiffOn_const) (cd_ofReal hQ)
      fun x hx => Complex.ofReal_ne_zero.2 (hq x hx).ne'
  · refine cd_div contDiffOn_const ((cd_ofReal hQ).sub (cd_ofReal hn.neg)) fun x hx => ?_
    have h1 := hq x hx
    have h2 := norm_nonneg (herm H (A x) (B x))
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.2 (ne_of_gt (by linarith))

theorem cd_normSq : ContDiff ℝ n (fun w : ℂ => Complex.normSq w) := by
  simp_rw [Complex.normSq_eq_norm_sq]
  exact contDiff_norm_sq ℝ

end Smooth

section Main

variable {k r : ℕ}

def u1 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z' + (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z

def u2 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a₀ : Q.Mx k r) (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  (a₀⁻¹ * g) *ᵥ z' + (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z

def qf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) : ℝ :=
  (Complex.normSq (zetaL k r z z' (Fin.last r) g) - Tz k r z * Tz k r z') / Tz k r z

def af (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (a₀ : Q.Mx k r) (g : Q.Mx k r) : Q.Mx k r :=
  a₀ * tmat (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g) (qf k r z z' g)

def bf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (a₀ : Q.Mx k r) (g : Q.Mx k r) : Q.Mx k r :=
  Hpk k r * (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g))ᴴ * Hpk k r * g

private lemma hpk_apply_of_outer_index (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    Hpk k r i j = if i.val + j.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk]
  split_ifs <;> first | rfl | (exfalso; omega)

private lemma hpk_mulVec_apply_of_outer_index (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) : (Hpk k r *ᵥ v) i = v ⟨2 * r + k - i.val, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, fun j => hpk_apply_of_outer_index (k := k) (r := r) i j hi]
  rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
  · rw [if_pos (Nat.add_sub_cancel' (by omega)), one_mul]
  · intro l _ hl
    rw [if_neg, zero_mul]
    intro h
    exact hl (Fin.ext (by show l.val = 2 * r + k - i.val; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem herm_out {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {i : Fin (2 * r + k + 1)}
    (hi : ¬ TwoByOneBlock.mid k r i) : herm (Hpk k r) (bvec i) d = 0 := by
  have hi0 : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
  have hi' : i.val < r ∨ r + k < i.val := by omega
  rw [TwoByOneBlock.herm_symm (Hpk k r) (GBasic.Hpk_herm k r), gn_herm_bvec_right, hpk_mulVec_apply_of_outer_index d i hi',
    hd _ (by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega), star_zero]

theorem inWb_uwb {g : Q.Mx k r} (hg : g ∈ B2.UWb k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (g *ᵥ v) := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  intro i hi
  obtain ⟨j, hjv⟩ : ∃ j : Fin (2 * r + k + 1), j.val = 2 * r + k - i.val := ⟨⟨_, by omega⟩, rfl⟩
  have hjo : j.val < r ∨ r + k < j.val := by omega
  have hji : (⟨2 * r + k - j.val, by omega⟩ : Fin (2 * r + k + 1)) = i :=
    Fin.ext (by show 2 * r + k - j.val = i.val; omega)
  have hfix : g *ᵥ bvec j = bvec j := by
    rcases Nat.lt_or_ge j.val r with h | h
    · have e : eI k r ⟨j.val, h⟩ = j := Fin.ext rfl
      rw [← e]
      exact (hg'.2 _).1
    · have ha : i.val < r := by omega
      have e : esI k r ⟨i.val, ha⟩ = j := Fin.ext (by show 2 * r + k - i.val = j.val; omega)
      rw [← e]
      exact (hg'.2 _).2
  have e1 : (g *ᵥ v) i = (Hpk k r *ᵥ (g *ᵥ v)) j := by rw [hpk_mulVec_apply_of_outer_index _ j hjo, hji]
  rw [e1, ← gn_herm_bvec_right, ← hfix, TwoByOneBlock.herm_UH hg'.1, gn_herm_bvec_right, hpk_mulVec_apply_of_outer_index _ j hjo, hji]
  exact hv i hi

theorem inWb_add {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) : inWb k r (v + w) := by
  intro i hi
  simp only [Pi.add_apply, hv i hi, hw i hi, add_zero]

theorem inWb_smul (c : ℂ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (c • v) := by
  intro i hi
  simp only [Pi.smul_apply, hv i hi, smul_zero]

theorem key {z v : Fin (2 * r + k + 1) → ℂ} {ζ : ℂ} {T T' : ℝ} (hT : T ≠ 0) (hz : herm (Hpk k r) z z = -(T : ℂ))
    (hvz : herm (Hpk k r) v z = ζ) (hvv : herm (Hpk k r) v v = -(T' : ℂ)) :
    herm (Hpk k r) (v + (ζ / (T : ℂ)) • z) (v + (ζ / (T : ℂ)) • z) = (((Complex.normSq ζ - T * T') / T : ℝ) : ℂ) ∧
      herm (Hpk k r) z (v + (ζ / (T : ℂ)) • z) = 0 := by
  have hzv : herm (Hpk k r) z v = star ζ := by
    rw [TwoByOneBlock.herm_symm (Hpk k r) (GBasic.Hpk_herm k r), hvz]
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT
  have hsT : star (T : ℂ) = T := Complex.conj_ofReal T
  have hn : ((Complex.normSq ζ : ℝ) : ℂ) = ζ * star ζ := (Complex.mul_conj ζ).symm
  constructor
  · rw [TwoByOneBlock.herm_add_left, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_left,
      TwoByOneBlock.herm_smul_left, TwoByOneBlock.herm_smul_right, TwoByOneBlock.herm_smul_right, hz, hvz, hvv, hzv, star_div₀, hsT]
    push_cast
    rw [hn]
    field_simp
    ring
  · rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, hz, hzv, star_div₀, hsT]
    field_simp
    ring

theorem uh_inv_mem {X : Q.Mx k r} (hX : X ∈ UH (Hpk k r)) : X⁻¹ ∈ UH (Hpk k r) := by
  have hX' : Xᴴ * Hpk k r * X = Hpk k r := hX
  have hdH : (Hpk k r).det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det (GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hdX : IsUnit X.det := by
    have e := congrArg Matrix.det hX'
    rw [Matrix.det_mul, Matrix.det_mul] at e
    refine isUnit_iff_ne_zero.2 fun h0 => hdH ?_
    rw [h0, mul_zero] at e
    exact e.symm
  show (X⁻¹)ᴴ * Hpk k r * X⁻¹ = Hpk k r
  calc (X⁻¹)ᴴ * Hpk k r * X⁻¹ = (X⁻¹)ᴴ * (Xᴴ * Hpk k r * X) * X⁻¹ := by rw [hX']
    _ = (X * X⁻¹)ᴴ * Hpk k r * (X * X⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hdX]; simp

theorem inv_fix {X : Q.Mx k r} (hu : IsUnit X.det) {v w : Fin (2 * r + k + 1) → ℂ} (h : X *ᵥ v = w) :
    X⁻¹ *ᵥ w = v := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem zeta_lt {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) :
    Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) g) := by
  have h : 0 < Complex.normSq (zetaL k r z z' (Fin.last r) g) - Tz k r z * Tz k r z' := hG
  linarith

theorem first_section_hermitian_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hsec : IsSection k r z z' μsec)
    {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) :
    herm (Hpk k r) (u1 k r z z' μsec g) (u1 k r z z' μsec g) = (qf k r z z' g : ℂ) ∧
      herm (Hpk k r) z (u1 k r z z' μsec g) = 0 ∧ inWb k r (u1 k r z z' μsec g) := by
  have hζ := zeta_lt hG
  have hμ := NFRadRedA.muZ_uwb hsec hζ
  have hμU : muZ k r μsec (zetaL k r z z' (Fin.last r) g) ∈ UH (Hpk k r) := hμ.1
  have hvz : herm (Hpk k r) (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') z = zetaL k r z z' (Fin.last r) g := by
    rw [← NFRadRedA.zeta_eq]
    exact NFRadRedA.zeta_muZ hz hz' hsec hζ
  have hvv : herm (Hpk k r) (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') (muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z') =
      -((Tz k r z' : ℝ) : ℂ) := by
    rw [TwoByOneBlock.herm_UH hμU, TwoByOneBlock.herm_self_eq]
  obtain ⟨h1, h2⟩ := key hT.ne' (TwoByOneBlock.herm_self_eq z) hvz hvv
  exact ⟨h1, h2, inWb_add (inWb_uwb hμ hz') (inWb_smul _ hz)⟩

private lemma hpk_conjTranspose_hpk_mul_eq_one_of_mem_uh {X : Q.Mx k r} (hX : X ∈ UH (Hpk k r)) :
    Hpk k r * Xᴴ * Hpk k r * X = 1 ∧ X * (Hpk k r * Xᴴ * Hpk k r) = 1 := by
  have hX' : Xᴴ * Hpk k r * X = Hpk k r := hX
  have h1 : Hpk k r * Xᴴ * Hpk k r * X = 1 := by
    calc Hpk k r * Xᴴ * Hpk k r * X = Hpk k r * (Xᴴ * Hpk k r * X) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hX', GBasic.Hpk_sq]
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

private lemma mul_mem_UH_of_mem_of_mem {X Y : Q.Mx k r} (hX : X ∈ UH (Hpk k r)) (hY : Y ∈ UH (Hpk k r)) :
    X * Y ∈ UH (Hpk k r) := by
  have hX' : Xᴴ * Hpk k r * X = Hpk k r := hX
  have hY' : Yᴴ * Hpk k r * Y = Hpk k r := hY
  show (X * Y)ᴴ * Hpk k r * (X * Y) = Hpk k r
  calc (X * Y)ᴴ * Hpk k r * (X * Y) = Yᴴ * (Xᴴ * Hpk k r * X) * Y := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hX', hY']

theorem second_section_hermitian_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) {a₀ : Q.Mx k r}
    (ha₀ : a₀ ∈ UWset k r z) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    herm (Hpk k r) (u2 k r z z' a₀ g) (u2 k r z z' a₀ g) = (qf k r z z' g : ℂ) ∧
      herm (Hpk k r) z (u2 k r z z' a₀ g) = 0 ∧ inWb k r (u2 k r z z' a₀ g) := by
  have ha' : a₀ ∈ UH (Hpk k r) ∧ (∀ a : Fin r, a₀ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      a₀ *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧ a₀ *ᵥ z = z := ha₀
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < (Fin.last r).val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  have hd := Matrix.isUnit_det_of_left_inverse (hpk_conjTranspose_hpk_mul_eq_one_of_mem_uh ha'.1).1
  have hinv : a₀⁻¹ ∈ UH (Hpk k r) := uh_inv_mem ha'.1
  have hgW : g ∈ B2.UWb k r := ⟨hg'.1, fun a => hg'.2 a a.isLt⟩
  have hiW : a₀⁻¹ ∈ B2.UWb k r := ⟨hinv, fun a => ⟨inv_fix hd (ha'.2.1 a).1, inv_fix hd (ha'.2.1 a).2⟩⟩
  have hz0 : a₀⁻¹ *ᵥ z = z := inv_fix hd ha'.2.2
  have hvz : herm (Hpk k r) ((a₀⁻¹ * g) *ᵥ z') z = zetaL k r z z' (Fin.last r) g := by
    rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← hz0]
    rw [TwoByOneBlock.herm_UH hinv]
    exact (NFRadRedA.zeta_eq g).symm
  have hvv : herm (Hpk k r) ((a₀⁻¹ * g) *ᵥ z') ((a₀⁻¹ * g) *ᵥ z') = -((Tz k r z' : ℝ) : ℂ) := by
    rw [← Matrix.mulVec_mulVec, TwoByOneBlock.herm_UH hinv, TwoByOneBlock.herm_UH hg'.1, TwoByOneBlock.herm_self_eq]
  obtain ⟨h1, h2⟩ := key hT.ne' (TwoByOneBlock.herm_self_eq z) hvz hvv
  have hu : inWb k r (u2 k r z z' a₀ g) := by
    unfold u2
    rw [← Matrix.mulVec_mulVec]
    exact inWb_add (inWb_uwb hiW (inWb_uwb hgW hz')) (inWb_smul _ hz)
  exact ⟨h1, h2, hu⟩

theorem qf_pos (hT : 0 < Tz k r z) {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) : 0 < qf k r z z' g := by
  unfold qf
  exact div_pos (by linarith [zeta_lt hG]) hT

theorem pt (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hsec : IsSection k r z z' μsec)
    {a₀ : Q.Mx k r} (ha₀ : a₀ ∈ UWset k r z) {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r))
    (hG : 0 < GGl k r z z' g) (hs : herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g) ≠ 0) :
    af k r z z' μsec a₀ g ∈ UWset k r z ∧ bf k r z z' μsec a₀ g ∈ UWset k r z' ∧
      g = af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * bf k r z z' μsec a₀ g := by
  have hH := GBasic.Hpk_herm k r
  have hζ := zeta_lt hG
  have hq := qf_pos hT hG
  obtain ⟨h1q, h1z, h1w⟩ := first_section_hermitian_facts hz hz' hT hsec hG
  obtain ⟨h2q, h2z, h2w⟩ := second_section_hermitian_facts hz hz' hT ha₀ hg
  obtain ⟨hTU, hTu, hTx⟩ := tmat_spec hH _ _ _ hq h1q h2q hs
  have ha' : a₀ ∈ UH (Hpk k r) ∧ (∀ a : Fin r, a₀ *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      a₀ *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧ a₀ *ᵥ z = z := ha₀
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < (Fin.last r).val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  have hd0 : IsUnit a₀.det := Matrix.isUnit_det_of_left_inverse (hpk_conjTranspose_hpk_mul_eq_one_of_mem_uh ha'.1).1
  have hμ : muZ k r μsec (zetaL k r z z' (Fin.last r) g) ∈ UH (Hpk k r) ∧ ∀ a : Fin r,
      muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ bvec (esI k r a) = bvec (esI k r a) :=
    NFRadRedA.muZ_uwb hsec hζ
  have hmI : ∀ a : Fin r, ¬ TwoByOneBlock.mid k r (eI k r a) := fun a h =>
    absurd h.1 (by show ¬ r ≤ a.val; omega)
  have hmS : ∀ a : Fin r, ¬ TwoByOneBlock.mid k r (esI k r a) := fun a h =>
    absurd h.2 (by show ¬ 2 * r + k - a.val ≤ r + k; omega)
  have hTe : ∀ i, ¬ TwoByOneBlock.mid k r i → tmat (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g) (qf k r z z' g) *ᵥ bvec i = bvec i :=
    fun i hi => hTx _ (herm_out h1w hi) (herm_out h2w hi)
  have hTz := hTx z h1z h2z

  have hafU : af k r z z' μsec a₀ g ∈ UH (Hpk k r) := mul_mem_UH_of_mem_of_mem ha'.1 hTU
  have hafe : ∀ a : Fin r, af k r z z' μsec a₀ g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      af k r z z' μsec a₀ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro a
    unfold af
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTe _ (hmI a), hTe _ (hmS a)]
    exact ha'.2.1 a
  have hafz : af k r z z' μsec a₀ g *ᵥ z = z := by
    unfold af
    rw [← Matrix.mulVec_mulVec, hTz, ha'.2.2]

  have hXU : af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g) ∈ UH (Hpk k r) := mul_mem_UH_of_mem_of_mem hafU hμ.1
  have hXe : ∀ a : Fin r, (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g)) *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g)) *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro a
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hμ.2 a).1, (hμ.2 a).2]
    exact hafe a
  have hXi := hpk_conjTranspose_hpk_mul_eq_one_of_mem_uh hXU
  have hYU : Hpk k r * (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g))ᴴ * Hpk k r ∈ UH (Hpk k r) := by
    rw [← Matrix.inv_eq_left_inv hXi.1]
    exact uh_inv_mem hXU
  have hYfix : ∀ v, (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g)) *ᵥ v = v →
      (Hpk k r * (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g))ᴴ * Hpk k r) *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, hXi.1, Matrix.one_mulVec]

  have hgz : (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g)) *ᵥ z' = g *ᵥ z' := by
    have hμz : muZ k r μsec (zetaL k r z z' (Fin.last r) g) *ᵥ z' =
        u1 k r z z' μsec g - (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z := (add_sub_cancel_right _ _).symm
    have hu2z : u2 k r z z' a₀ g - (zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) • z = (a₀⁻¹ * g) *ᵥ z' :=
      add_sub_cancel_right _ _
    unfold af
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hμz, Matrix.mulVec_sub, Matrix.mulVec_smul, hTu, hTz,
      hu2z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hd0]
  refine ⟨⟨hafU, hafe, hafz⟩, ⟨mul_mem_UH_of_mem_of_mem hYU hg'.1, fun a => ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · unfold bf
    rw [← Matrix.mulVec_mulVec, (hg'.2 a a.isLt).1, hYfix _ (hXe a).1]
  · unfold bf
    rw [← Matrix.mulVec_mulVec, (hg'.2 a a.isLt).2, hYfix _ (hXe a).2]
  · show (Hpk k r * (af k r z z' μsec a₀ g * muZ k r μsec (zetaL k r z z' (Fin.last r) g))ᴴ * Hpk k r * g) *ᵥ z' = z'
    rw [← Matrix.mulVec_mulVec, ← hgz, Matrix.mulVec_mulVec, hXi.1, Matrix.one_mulVec]
  · unfold bf
    rw [← Matrix.mul_assoc, hXi.2, Matrix.one_mul]

end Main

theorem locSec : NFRadRedS.LocSec := by
  intro k r z z' μsec _hk hz hz' hT _hT' hsec g₀ hg₀ hG₀
  have hH := GBasic.Hpk_herm k r
  have hTc : ((Tz k r z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'

  have hζ : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => zetaL k r z z' (Fin.last r) g) Set.univ := by
    have e : (fun g : Q.Mx k r => zetaL k r z z' (Fin.last r) g) = fun g => herm (Hpk k r) (g *ᵥ z') z :=
      funext fun g => NFRadRedA.zeta_eq g
    rw [e]
    exact cd_herm _ (cdv_mulVec (F := fun g : Q.Mx k r => g) contDiffOn_id z') contDiffOn_const
  have hGs : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => GGl k r z z' g) Set.univ :=
    (cd_normSq.comp_contDiffOn hζ).sub contDiffOn_const
  have hWo : IsOpen {g : Q.Mx k r | 0 < GGl k r z z' g} := isOpen_lt continuous_const (continuousOn_univ.1 hGs.continuousOn)
  have hμs : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => muZ k r μsec (zetaL k r z z' (Fin.last r) g)) {g : Q.Mx k r | 0 < GGl k r z z' g} := by
    refine cdm_iff.2 fun i j => ?_
    simp only [muZ, B2.embWb]
    split_ifs
    · exact (hsec.1 _ _).comp (hζ.mono (Set.subset_univ _)) (by intro g hg; exact zeta_lt hg)
    · exact contDiffOn_const
    · exact contDiffOn_const
  have hcs : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => zetaL k r z z' (Fin.last r) g / (Tz k r z : ℂ)) {g : Q.Mx k r | 0 < GGl k r z z' g} :=
    cd_div (hζ.mono (Set.subset_univ _)) contDiffOn_const fun _ _ => hTc
  have hu1s : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => u1 k r z z' μsec g) {g : Q.Mx k r | 0 < GGl k r z z' g} := by
    unfold u1
    exact (cdv_mulVec hμs z').add (cdv_smul hcs contDiffOn_const)
  have hu2s : ∀ a₀ : Q.Mx k r, ContDiffOn ℝ ∞ (fun g : Q.Mx k r => u2 k r z z' a₀ g) {g : Q.Mx k r | 0 < GGl k r z z' g} := by
    intro a₀
    unfold u2
    exact (cdv_mulVec (cdm_mul (F := fun _ => a₀⁻¹) (G := fun g => g) contDiffOn_const contDiffOn_id) z').add
      (cdv_smul hcs contDiffOn_const)
  have hqs : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => qf k r z z' g) Set.univ := by
    unfold qf
    exact ((cd_normSq.comp_contDiffOn hζ).sub contDiffOn_const).div_const _

  obtain ⟨h1q, h1z, h1w⟩ := first_section_hermitian_facts hz hz' hT hsec hG₀
  have hq₀ := qf_pos hT hG₀
  have hqc : ((qf k r z z' g₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq₀.ne'
  have hone : (1 : Q.Mx k r) ∈ UWset k r z :=
    ⟨by show (1 : Q.Mx k r)ᴴ * Hpk k r * 1 = Hpk k r; simp,
      fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  have hmI : ∀ a : Fin r, ¬ TwoByOneBlock.mid k r (eI k r a) := fun a h =>
    absurd h.1 (by show ¬ r ≤ a.val; omega)
  have hmS : ∀ a : Fin r, ¬ TwoByOneBlock.mid k r (esI k r a) := fun a h =>
    absurd h.2 (by show ¬ 2 * r + k - a.val ≤ r + k; omega)
  obtain ⟨a₀, ha₀, hne⟩ : ∃ a₀ ∈ UWset k r z,
      herm (Hpk k r) (u1 k r z z' μsec g₀) (u2 k r z z' a₀ g₀) ≠ 0 := by
    by_cases h0 : herm (Hpk k r) (u1 k r z z' μsec g₀) (u2 k r z z' 1 g₀) = 0
    ·
      obtain ⟨h2q, h2z, h2w⟩ := second_section_hermitian_facts hz hz' hT hone hg₀
      have h21 : herm (Hpk k r) (u2 k r z z' 1 g₀) (u1 k r z z' μsec g₀) = 0 := by
        rw [TwoByOneBlock.herm_symm (Hpk k r) hH, h0, star_zero]
      have hsq : star ((qf k r z z' g₀ : ℝ) : ℂ) = qf k r z z' g₀ := Complex.conj_ofReal _
      have hdd : herm (Hpk k r) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) =
          2 * ((qf k r z z' g₀ : ℝ) : ℂ) := by
        rw [TwoByOneBlock.herm_add_left, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_left,
          TwoByOneBlock.herm_smul_left, TwoByOneBlock.herm_smul_right, TwoByOneBlock.herm_smul_right, h1q, h2q, h0, h21, star_neg, star_one]
        ring
      have hcond : -1 / ((qf k r z z' g₀ : ℝ) : ℂ) + star (-1 / ((qf k r z z' g₀ : ℝ) : ℂ)) +
          -1 / ((qf k r z z' g₀ : ℝ) : ℂ) * star (-1 / ((qf k r z z' g₀ : ℝ) : ℂ)) *
            herm (Hpk k r) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) = 0 := by
        rw [star_div₀, star_neg, star_one, hsq, hdd]
        field_simp
        ring
      obtain ⟨R, hRdef⟩ : ∃ R : Q.Mx k r, R = TwoByOneBlock.qrefl (Hpk k r) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀)
          (-1 / ((qf k r z z' g₀ : ℝ) : ℂ)) := ⟨_, rfl⟩
      have hRmem : R ∈ UH (Hpk k r) := by
        rw [hRdef]
        exact TwoByOneBlock.qrefl_mem _ hH _ _ hcond
      have hRfix : ∀ x, herm (Hpk k r) x (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) = 0 → R *ᵥ x = x := by
        intro x hx
        rw [hRdef, TwoByOneBlock.qrefl_mulVec, hx, mul_zero, zero_smul, add_zero]
      have hdW : inWb k r (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) := inWb_add h1w (inWb_smul _ h2w)
      have hzd : herm (Hpk k r) z (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) = 0 := by
        rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, h1z, h2z]
        ring
      have hR : R ∈ UWset k r z :=
        ⟨hRmem, fun a => ⟨hRfix _ (herm_out hdW (hmI a)), hRfix _ (herm_out hdW (hmS a))⟩, hRfix _ hzd⟩
      have hv1d : herm (Hpk k r) (u1 k r z z' μsec g₀) (u1 k r z z' μsec g₀ + (-1 : ℂ) • u2 k r z z' 1 g₀) = ((qf k r z z' g₀ : ℝ) : ℂ) := by
        rw [TwoByOneBlock.herm_add_right, TwoByOneBlock.herm_smul_right, h1q, h0]
        ring
      have hRv1 : R *ᵥ u1 k r z z' μsec g₀ = u2 k r z z' 1 g₀ := by
        rw [hRdef, TwoByOneBlock.qrefl_mulVec, hv1d, div_mul_cancel₀ _ hqc]
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hdR : IsUnit R.det := Matrix.isUnit_det_of_left_inverse (hpk_conjTranspose_hpk_mul_eq_one_of_mem_uh hRmem).1
      have hRi : R⁻¹ *ᵥ u2 k r z z' 1 g₀ = u1 k r z z' μsec g₀ := inv_fix hdR hRv1
      have hRz : R⁻¹ *ᵥ z = z := inv_fix hdR (hRfix z hzd)
      have hu2R : u2 k r z z' R g₀ = R⁻¹ *ᵥ u2 k r z z' 1 g₀ := by
        unfold u2
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hRz, inv_one, Matrix.one_mul, Matrix.mulVec_mulVec]
      refine ⟨R, hR, ?_⟩
      rw [hu2R, hRi, h1q]
      exact hqc
    · exact ⟨1, hone, h0⟩

  have hfc : ContinuousOn (fun g : Q.Mx k r => herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g)) {g : Q.Mx k r | 0 < GGl k r z z' g} :=
    (cd_herm (n := ∞) _ hu1s (hu2s a₀)).continuousOn
  have haS : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => af k r z z' μsec a₀ g) ({g : Q.Mx k r | 0 < GGl k r z z' g} ∩ (fun g : Q.Mx k r => herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g)) ⁻¹' {0}ᶜ) := by
    unfold af
    exact cdm_mul (F := fun _ => a₀) contDiffOn_const
      (cdm_tmat _ (hu1s.mono fun x hx => hx.1) ((hu2s a₀).mono fun x hx => hx.1) (hqs.mono (Set.subset_univ _))
        (fun g hg => hg.2) (fun g hg => qf_pos hT hg.1))
  have hbS : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => bf k r z z' μsec a₀ g) ({g : Q.Mx k r | 0 < GGl k r z z' g} ∩ (fun g : Q.Mx k r => herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g)) ⁻¹' {0}ᶜ) := by
    unfold bf
    exact cdm_mul (cdm_mul (cdm_mul contDiffOn_const (cdm_conjT (cdm_mul haS (hμs.mono fun x hx => hx.1))))
      contDiffOn_const) (G := fun g => g) contDiffOn_id
  refine ⟨{g : Q.Mx k r | 0 < GGl k r z z' g} ∩ (fun g : Q.Mx k r => herm (Hpk k r) (u1 k r z z' μsec g) (u2 k r z z' a₀ g)) ⁻¹' {0}ᶜ, hfc.isOpen_inter_preimage hWo isOpen_compl_singleton, ⟨hG₀, hne⟩,
    fun g => af k r z z' μsec a₀ g, fun g => bf k r z z' μsec a₀ g, haS, hbS, ?_⟩
  intro g hg hgl hG
  exact pt hz hz' hT hsec ha₀ hgl hG hg.2

end Formalism.FourierDecayAlt.P.NFRadRedLocSec

namespace Formalism.FourierDecayAlt.P

theorem local_smooth_section : NFRadRedS.LocSec := by
  exact NFRadRedLocSec.locSec

end Formalism.FourierDecayAlt.P
