import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  have hi := i.isLt
  show ∑ j, Hpk k r i j * v j = _
  split_ifs with h1 h2
  · simp_rw [hpk_out h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp_rw [hpk_mid h1]
    rw [Finset.sum_eq_single i]
    · simp [h2]
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp_rw [hpk_mid h1]
    rw [Finset.sum_eq_single i]
    · simp [h2]
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro hj'
      exact hj (Fin.ext hj')
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  split_ifs with h1 h2
  · rw [hpk_mulVec, if_pos]
    · congr 1
      ext
      show 2 * r + k - (2 * r + k - i.val) = i.val
      omega
    · show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val
      omega
  · rw [hpk_mulVec, if_neg h1, if_pos h2, neg_neg]
  · rw [hpk_mulVec, if_neg h1, if_neg h2]

theorem mat_eq_of_mulVec {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem hpk_sq : Hpk k r * Hpk k r = 1 := mat_eq_of_mulVec (fun v => by
  rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec])

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem gv_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem gv_inv_eq {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (gv_left_inv hg)

theorem gv_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  rw [gv_inv_eq hg]
  exact gv_left_inv hg

theorem gv_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (gv_inv_mul hg))

theorem gv_one : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem gv_mul {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem gv_inv_mem {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := gv_mul_inv hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem gv_inv_inv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹⁻¹ = g := Matrix.inv_eq_left_inv (gv_mul_inv hg)

theorem hpk_mem : Hpk k r ∈ GV k r := by
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [hpk_conjT, hpk_sq, Matrix.one_mul]

theorem gN_eq_frob (g : Mat k r) :
    gN g = @Norm.norm _ (Matrix.frobeniusSeminormedAddCommGroup).toNorm g := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two, Complex.normSq_eq_norm_sq]

theorem gN_mul_le (a b : Mat k r) : gN (a * b) ≤ gN a * gN b := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b

theorem gN_nonneg (g : Mat k r) : 0 ≤ gN g := by
  unfold gN
  exact Real.sqrt_nonneg _

theorem gN_conjT (g : Mat k r) : gN gᴴ = gN g := by
  unfold gN
  congr 1
  rw [Finset.sum_comm]
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]

theorem gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  rw [gv_inv_eq hg]
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le _ _) (gN_nonneg _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

theorem gN_one_pos : 0 < gN (1 : Mat k r) := by
  unfold gN
  apply Real.sqrt_pos.mpr
  have h0 : (0 : ℝ) < Complex.normSq ((1 : Mat k r) 0 0) := by simp
  calc (0 : ℝ) < Complex.normSq ((1 : Mat k r) 0 0) := h0
    _ ≤ ∑ j, Complex.normSq ((1 : Mat k r) 0 j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq ((1 : Mat k r) 0 j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ 0)
    _ ≤ ∑ i, ∑ j, Complex.normSq ((1 : Mat k r) i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq ((1 : Mat k r) i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ 0)

theorem gN_pos {g : Mat k r} (hg : g ∈ GV k r) : 0 < gN g := by
  have h1 := gN_mul_le g⁻¹ g
  rw [gv_inv_mul hg] at h1
  rcases (gN_nonneg g).lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, mul_zero] at h1
    linarith [gN_one_pos (k := k) (r := r)]

def KH (k r : ℕ) : ℝ := gN (Hpk k r) ^ 2

theorem KH_pos : 0 < KH k r := by
  unfold KH
  exact pow_pos (gN_pos hpk_mem) 2

theorem gN_le_inv {g : Mat k r} (hg : g ∈ GV k r) : gN g ≤ KH k r * gN g⁻¹ := by
  unfold KH
  have h := gN_inv_le (gv_inv_mem hg)
  rwa [gv_inv_inv hg] at h

theorem rpow_neg_le {x y c b : ℝ} (hy : 0 < y) (hc : 0 < c) (hb : 0 ≤ b) (h : y ≤ c * x) :
    x ^ (-b) ≤ c ^ b * y ^ (-b) := by
  have hx : 0 < x := by
    by_contra hx
    push_neg at hx
    nlinarith
  have hA : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  have hB : 0 < y ^ b := Real.rpow_pos_of_pos hy b
  have hC : 0 < c ^ b := Real.rpow_pos_of_pos hc b
  have key : y ^ b ≤ c ^ b * x ^ b := by
    rw [← Real.mul_rpow hc.le hx.le]
    exact Real.rpow_le_rpow hy.le h hb
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  have e : c ^ b * (y ^ b)⁻¹ - (x ^ b)⁻¹ = (c ^ b * x ^ b - y ^ b) / (x ^ b * y ^ b) := by
    field_simp <;> ring
  have h2 : 0 ≤ (c ^ b * x ^ b - y ^ b) / (x ^ b * y ^ b) :=
    div_nonneg (by linarith) (mul_pos hA hB).le
  linarith

theorem uw_gv {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) : h ∈ GV k r := hh.1

theorem n_gv {m : Mat k r} (hm : m ∈ Nset k r) : m ∈ GV k r := hm.1

theorem uw_inv_mem {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hG, hE, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := gv_inv_mul hG
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨gv_inv_mem hG, fun a => ⟨fix _ (hE a).1, fix _ (hE a).2⟩, fix _ hz⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem sig_mul (X : SigData k r) {x y : Mat k r} (hx : x ∈ GV k r) (hy : y ∈ GV k r) :
    X.σ (x * y) = (X.σ x).comp (X.σ y) := X.rep.1.2 x hx y hy

theorem sig_inner (X : SigData k r) {y : Mat k r} (hy : y ∈ GV k r) (u v : X.Hs) :
    ⟪X.σ y u, v⟫_ℂ = ⟪u, X.σ y⁻¹ v⟫_ℂ := by
  have hyi : y⁻¹ ∈ GV k r := gv_inv_mem hy
  have hcomp : X.σ y (X.σ y⁻¹ v) = v := by
    have h := X.rep.1.2 y hy y⁻¹ hyi
    rw [gv_mul_inv hy, X.rep.1.1] at h
    have h2 := DFunLike.congr_fun h v
    simp only [ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at h2
    exact h2.symm
  let L : X.Hs →ₗᵢ[ℂ] X.Hs :=
    { toLinearMap := (X.σ y).toLinearMap, norm_map' := fun w => X.rep.2.1 y hy w }
  calc ⟪X.σ y u, v⟫_ℂ = ⟪X.σ y u, X.σ y (X.σ y⁻¹ v)⟫_ℂ := by rw [hcomp]
    _ = ⟪L u, L (X.σ y⁻¹ v)⟫_ℂ := rfl
    _ = ⟪u, X.σ y⁻¹ v⟫_ℂ := L.inner_map_map _ _

theorem C_nonneg {E : Type} [NormedAddCommGroup E] {f : Mat k r → E} {C e : ℝ}
    (h : ∀ x ∈ GV k r, ‖f x‖ ≤ C * gN x ^ e) : 0 ≤ C := by
  have h1 := h 1 gv_one
  have hp : 0 < gN (1 : Mat k r) ^ e := Real.rpow_pos_of_pos gN_one_pos e
  by_contra hC
  push_neg at hC
  have h2 : C * gN (1 : Mat k r) ^ e < 0 := mul_neg_of_neg_of_pos hC hp
  linarith [norm_nonneg (f 1)]

theorem w_mem (X : SigData k r) : X.w ∈ Vfl X := ⟨X.Cw, X.dec⟩

theorem sig_mem_vfl (X : SigData k r) (ha : 0 ≤ X.a) {g : Mat k r} (hg : g ∈ GV k r) {u : X.Hs}
    (hu : u ∈ Vfl X) : X.σ g u ∈ Vfl X := by
  obtain ⟨C, hC⟩ := hu
  have hgi : g⁻¹ ∈ GV k r := gv_inv_mem hg
  have hc : 0 < gN g⁻¹ := gN_pos hgi
  have hC0 : 0 ≤ C := C_nonneg (f := mc X u X.w) hC
  refine ⟨C * gN g⁻¹ ^ X.a, fun x hx => ?_⟩
  have hxg : x * g ∈ GV k r := gv_mul hx hg
  have e : mc X (X.σ g u) X.w x = mc X u X.w (x * g) := by
    unfold mc
    rw [sig_mul X hx hg, ContinuousLinearMap.comp_apply]
  rw [e]
  have hy : 0 < gN x := gN_pos hx
  have hle : gN x ≤ gN g⁻¹ * gN (x * g) := by
    have h1 := gN_mul_le (x * g) g⁻¹
    rw [Matrix.mul_assoc, gv_mul_inv hg, Matrix.mul_one] at h1
    rw [mul_comm (gN g⁻¹)]
    exact h1
  have key := rpow_neg_le hy hc ha hle
  calc ‖mc X u X.w (x * g)‖ ≤ C * gN (x * g) ^ (-X.a) := hC _ hxg
    _ ≤ C * (gN g⁻¹ ^ X.a * gN x ^ (-X.a)) := mul_le_mul_of_nonneg_left key hC0
    _ = C * gN g⁻¹ ^ X.a * gN x ^ (-X.a) := by ring

theorem coef_bound (X : SigData k r) (ha : 0 ≤ X.a) {u : X.Hs} (hu : u ∈ Vfl X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ GV k r, ‖⟪X.σ y X.w, u⟫_ℂ‖ ≤ C * gN y ^ (-X.a) := by
  obtain ⟨C, hC⟩ := hu
  have hC0 : 0 ≤ C := C_nonneg (f := mc X u X.w) hC
  refine ⟨C * KH k r ^ X.a, mul_nonneg hC0 (Real.rpow_pos_of_pos KH_pos _).le, fun y hy => ?_⟩
  have hyi : y⁻¹ ∈ GV k r := gv_inv_mem hy
  rw [sig_inner X hy]
  have key := rpow_neg_le (gN_pos hy) KH_pos ha (gN_le_inv hy)
  calc ‖⟪X.w, X.σ y⁻¹ u⟫_ℂ‖ = ‖mc X u X.w y⁻¹‖ := rfl
    _ ≤ C * gN y⁻¹ ^ (-X.a) := hC _ hyi
    _ ≤ C * (KH k r ^ X.a * gN y ^ (-X.a)) := mul_le_mul_of_nonneg_left key hC0
    _ = C * KH k r ^ X.a * gN y ^ (-X.a) := by ring

theorem psi_norm (D : RealPlaceData k r Wp Wp) (m : Mat k r) : ‖psiD D m‖ = 1 := by
  unfold psiD psi
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem pi_norm_le (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) : ‖D.π h‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
  rw [D.π_unitary h hh v, one_mul])

theorem ae_UN (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 ∈ UWset k r D.z ∧ Matrix.of p.2 ∈ Nset k r := by
  haveI : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.mpr D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.mpr D.haarN.conc
  exact ((Measure.quasiMeasurePreserving_fst (μ := D.μW) (ν := D.μN)).ae hW).and
    ((Measure.quasiMeasurePreserving_snd (μ := D.μW) (ν := D.μN)).ae hN)

theorem be_bound (D : RealPlaceData k r Wp Wp) (X : SigData k r) {v : X.Hs} {b Cp : ℝ} (hb0 : 0 ≤ b)
    (hCp : ∀ x ∈ GV k r, ‖mc X X.w v x‖ ≤ Cp * gN x ^ (-b))
    (hS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN)) :
    ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b := by
  have hCp0 : 0 ≤ Cp := C_nonneg (f := mc X X.w v) hCp
  refine ⟨Cp * KH k r ^ b * ∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN),
    fun y hy => ?_⟩
  have bound : ∀ᵐ p ∂(D.μW.prod D.μN), ‖beInt D X (X.σ y X.w) v p‖ ≤
      (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by
    filter_upwards [ae_UN D] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hW : Matrix.of p.1 ∈ GV k r := uw_gv hp1
    have hN : Matrix.of p.2 ∈ GV k r := n_gv hp2
    have hnw : Matrix.of p.2 * Matrix.of p.1 ∈ GV k r := gv_mul hN hW
    have hnwy : Matrix.of p.2 * Matrix.of p.1 * y ∈ GV k r := gv_mul hnw hy
    have hmc : mc X (X.σ y X.w) v (Matrix.of p.2 * Matrix.of p.1) =
        mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y) := by
      unfold mc
      rw [sig_mul X hnw hy, ContinuousLinearMap.comp_apply]
    have hpos : 0 < gN (Matrix.of p.2 * Matrix.of p.1) := gN_pos hnw
    have hle : gN (Matrix.of p.2 * Matrix.of p.1) ≤
        (KH k r * gN y) * gN (Matrix.of p.2 * Matrix.of p.1 * y) := by
      have h1 := gN_mul_le (Matrix.of p.2 * Matrix.of p.1 * y) y⁻¹
      rw [Matrix.mul_assoc _ y, gv_mul_inv hy, Matrix.mul_one] at h1
      have h2 : gN y⁻¹ ≤ KH k r * gN y := gN_inv_le hy
      calc gN (Matrix.of p.2 * Matrix.of p.1)
          ≤ gN (Matrix.of p.2 * Matrix.of p.1 * y) * gN y⁻¹ := h1
        _ ≤ gN (Matrix.of p.2 * Matrix.of p.1 * y) * (KH k r * gN y) :=
            mul_le_mul_of_nonneg_left h2 (gN_nonneg _)
        _ = (KH k r * gN y) * gN (Matrix.of p.2 * Matrix.of p.1 * y) := mul_comm _ _
    have key := rpow_neg_le hpos (mul_pos KH_pos (gN_pos hy)) hb0 hle
    have hpi : ‖D.π (Matrix.of p.1)⁻¹‖ ≤ 1 := pi_norm_le D (uw_inv_mem hp1)
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one, hmc]
    calc ‖mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y)‖ * ‖D.π (Matrix.of p.1)⁻¹‖
        ≤ ‖mc X X.w v (Matrix.of p.2 * Matrix.of p.1 * y)‖ * 1 :=
          mul_le_mul_of_nonneg_left hpi (norm_nonneg _)
      _ ≤ Cp * gN (Matrix.of p.2 * Matrix.of p.1 * y) ^ (-b) := by
          rw [mul_one]
          exact hCp _ hnwy
      _ ≤ Cp * ((KH k r * gN y) ^ b * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) :=
          mul_le_mul_of_nonneg_left key hCp0
      _ = Cp * (KH k r * gN y) ^ b * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) := by ring
  have hint : Integrable (fun p : Mt k r × Mt k r =>
      (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN) :=
    hS.const_mul _
  unfold beOp
  calc ‖∫ p, beInt D X (X.σ y X.w) v p ∂(D.μW.prod D.μN)‖
      ≤ ∫ p, (Cp * (KH k r * gN y) ^ b) * gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)
          ∂(D.μW.prod D.μN) := norm_integral_le_of_norm_le hint bound
    _ = (Cp * (KH k r * gN y) ^ b) *
          ∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN) :=
        integral_const_mul _ _
    _ = Cp * KH k r ^ b * (∫ p, gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b) ∂(D.μW.prod D.μN)) *
          gN y ^ b := by
        rw [Real.mul_rpow KH_pos.le (gN_nonneg y)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
