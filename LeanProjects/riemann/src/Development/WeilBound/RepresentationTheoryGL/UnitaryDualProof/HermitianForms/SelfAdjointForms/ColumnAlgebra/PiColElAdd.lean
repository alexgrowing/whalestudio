import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.alg

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
variable (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin N) k) V)

def fp (ξ : Fin (m + 1) → k) (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (x : V) : V :=
  ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) x

variable {ψ h π}

theorem colEl_comm (x y : Fin (m + 1) → k) : colEl k m N h x * colEl k m N h y = colEl k m N h y * colEl k m N h x := by
  rw [← colEl_add, ← colEl_add, add_comm]

theorem pi_colEl_add (x y : Fin (m + 1) → k) (v : V) :
    π (colEl k m N h (x + y)) v = π (colEl k m N h x) (π (colEl k m N h y) v) := by
  rw [colEl_add, map_mul]; rfl

theorem psi_mul_conj (c : Circle) : ((c : ℂ)) * starRingEnd ℂ (c : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp

theorem conj_mul_psi (c : Circle) : starRingEnd ℂ (c : ℂ) * (c : ℂ) = 1 := by
  rw [mul_comm, psi_mul_conj]

theorem fp_add (ξ : Fin (m + 1) → k) (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (x y : V) :
    fp ψ h π ξ p (x + y) = fp ψ h π ξ p x + fp ψ h π ξ p y := by
  unfold fp; rw [← smul_add, ← Finset.sum_add_distrib]; congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [map_add, smul_add]

theorem fp_smul (ξ : Fin (m + 1) → k) (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (c : ℂ) (x : V) :
    fp ψ h π ξ p (c • x) = c • fp ψ h π ξ p x := by
  unfold fp
  simp only [map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ring

theorem fp_sum (s : Finset (Fin (m + 1) → k)) (ξ : Fin (m + 1) → k)
    (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (x : V) :
    fp ψ h π ξ p (∑ t ∈ s, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) x) =
      ∑ t ∈ s, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • fp ψ h π ξ p (π (colEl k m N h t) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fp]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fp_add, fp_smul, ih]

theorem card_pos {ξ : Fin (m + 1) → k} {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p) : 0 < p.2.card := by
  obtain ⟨t, ht, -⟩ := hp.2.2.2.2.2 0 A.zero_mem
  exact Finset.card_pos.2 ⟨t, ht.1⟩

theorem collapse {X : Type} (T : Finset X) (hT : 0 < T.card) (f : X → Circle) (y : V) :
    ((T.card : ℂ)⁻¹) • ∑ t ∈ T, (starRingEnd ℂ ((f t : Circle) : ℂ)) • (((f t : Circle) : ℂ) • y) = y := by
  have e : ∀ t ∈ T, (starRingEnd ℂ ((f t : Circle) : ℂ)) • (((f t : Circle) : ℂ) • y) = y := fun t _ => by
    rw [smul_smul, conj_mul_psi, one_smul]
  have e2 : ∑ t ∈ T, (starRingEnd ℂ ((f t : Circle) : ℂ)) • (((f t : Circle) : ℂ) • y) = ∑ t ∈ T, y :=
    Finset.sum_congr rfl e
  rw [e2, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ T.card y, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hT.ne' : (T.card : ℂ) ≠ 0), one_smul]

theorem fp_comm (ξ : Fin (m + 1) → k) (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (y : Fin (m + 1) → k)
    (x : V) : π (colEl k m N h y) (fp ψ h π ξ p x) = fp ψ h π ξ p (π (colEl k m N h y) x) := by
  unfold fp
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, ← pi_colEl_add, ← pi_colEl_add, add_comm y t]

theorem fp_shift (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (hH : ∀ a ∈ p.1, ψ (ξ ⬝ᵥ a) = 1)
    (hT : ∀ t ∈ p.2, t ∈ A) (htr : ∀ a ∈ A, ∃! t, t ∈ p.2 ∧ a - t ∈ p.1) (x : V)
    (hx : ∀ a ∈ p.1, π (colEl k m N h a) x = x) {y : Fin (m + 1) → k} (hy : y ∈ A) :
    fp ψ h π ξ p (π (colEl k m N h y) x) = ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • fp ψ h π ξ p x := by
  classical
  have hs : ∀ t ∈ p.2, ∃ t', t' ∈ p.2 ∧ (t + y) - t' ∈ p.1 := fun t ht =>
    (htr _ (A.add_mem (hT t ht) hy)).exists
  have hr : ∀ t ∈ p.2, ∃ t', t' ∈ p.2 ∧ (t - y) - t' ∈ p.1 := fun t ht =>
    (htr _ (A.sub_mem (hT t ht) hy)).exists
  let σ : (Fin (m + 1) → k) → (Fin (m + 1) → k) := fun t =>
    if hh : ∃ t', t' ∈ p.2 ∧ (t + y) - t' ∈ p.1 then hh.choose else t
  let τ : (Fin (m + 1) → k) → (Fin (m + 1) → k) := fun t =>
    if hh : ∃ t', t' ∈ p.2 ∧ (t - y) - t' ∈ p.1 then hh.choose else t
  have hσ : ∀ t ∈ p.2, σ t ∈ p.2 ∧ (t + y) - σ t ∈ p.1 := fun t ht => by
    simp only [σ, dif_pos (hs t ht)]; exact (hs t ht).choose_spec
  have hτ : ∀ t ∈ p.2, τ t ∈ p.2 ∧ (t - y) - τ t ∈ p.1 := fun t ht => by
    simp only [τ, dif_pos (hr t ht)]; exact (hr t ht).choose_spec
  unfold fp
  rw [smul_comm (((ψ (ξ ⬝ᵥ y) : Circle) : ℂ)) ((p.2.card : ℂ)⁻¹)]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_nbij' σ τ (fun t ht => (hσ t ht).1) (fun t ht => (hτ t ht).1) (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht => ?_)
  · have h1 := hσ t ht
    have h2 := hτ _ h1.1
    refine ((htr _ (A.sub_mem (hT _ h1.1) hy)).unique ⟨h2.1, h2.2⟩ ⟨ht, ?_⟩)
    have : (σ t - y) - t = -((t + y) - σ t) := by abel
    rw [this]; exact p.1.neg_mem h1.2
  · have h1 := hτ t ht
    have h2 := hσ _ h1.1
    refine ((htr _ (A.add_mem (hT _ h1.1) hy)).unique ⟨h2.1, h2.2⟩ ⟨ht, ?_⟩)
    have : (τ t + y) - t = -((t - y) - τ t) := by abel
    rw [this]; exact p.1.neg_mem h1.2
  · obtain ⟨h1, h2⟩ := hσ t ht
    set u := (t + y) - σ t with hu
    have et : t + y = σ t + u := by rw [hu]; abel
    have hdot : ξ ⬝ᵥ t = ξ ⬝ᵥ σ t + ξ ⬝ᵥ u - ξ ⬝ᵥ y := by
      rw [← dotProduct_add, ← dotProduct_sub, ← et, add_sub_cancel_right]
    have hψt : ψ (ξ ⬝ᵥ t) = ψ (ξ ⬝ᵥ σ t) / ψ (ξ ⬝ᵥ y) := by
      rw [hdot, AddChar.map_sub_eq_div, AddChar.map_add_eq_mul, hH u h2, mul_one]
    rw [← pi_colEl_add, et, pi_colEl_add, hx u h2, smul_smul]
    congr 1
    rw [hψt, Circle.coe_div, map_div₀, div_eq_mul_inv, mul_comm]
    congr 1
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]

theorem fp_eigen (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} {x : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A x p)
    {y : Fin (m + 1) → k} (hy : y ∈ A) :
    π (colEl k m N h y) (fp ψ h π ξ p x) = ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • fp ψ h π ξ p x := by
  rw [fp_comm]
  exact fp_shift ξ p hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 x hp.2.2.1 hy

theorem fp_of_eigen (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (hT : ∀ t ∈ p.2, t ∈ A) (hc : 0 < p.2.card)
    (u : V) (hu : ∀ a ∈ A, π (colEl k m N h a) u = ((ψ (ξ ⬝ᵥ a) : Circle) : ℂ) • u) : fp ψ h π ξ p u = u := by
  unfold fp
  rw [Finset.sum_congr rfl fun t ht => by rw [hu t (hT t ht)]]
  exact collapse p.2 hc (fun t => ψ (ξ ⬝ᵥ t)) u

theorem fp_fp (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)}
    (p q : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)) (hp : ∀ t ∈ p.2, t ∈ A) (hcp : 0 < p.2.card)
    (hH : ∀ a ∈ q.1, ψ (ξ ⬝ᵥ a) = 1) (hT : ∀ t ∈ q.2, t ∈ A) (htr : ∀ a ∈ A, ∃! t, t ∈ q.2 ∧ a - t ∈ q.1) (x : V)
    (hx : ∀ a ∈ q.1, π (colEl k m N h a) x = x) : fp ψ h π ξ q (fp ψ h π ξ p x) = fp ψ h π ξ q x := by
  have e : fp ψ h π ξ p x = ((p.2.card : ℂ)⁻¹) •
      ∑ t ∈ p.2, (starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) x := rfl
  rw [e, fp_smul, fp_sum]
  rw [Finset.sum_congr rfl fun t ht => by rw [fp_shift ξ q hH hT htr x hx (hp t ht)]]
  exact collapse p.2 hcp (fun t => ψ (ξ ⬝ᵥ t)) _

theorem avg_eq_fp (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} {v : V}
    {p : AddSubgroup (Fin (m + 1) → k) × Finset (Fin (m + 1) → k)} (hp : AvgData ψ h π ξ A v p) :
    avg ψ h π ξ A v = fp ψ h π ξ p v := by
  have hd : ∃ p, AvgData ψ h π ξ A v p := ⟨p, hp⟩
  have hp0 := hd.choose_spec
  have e : avg ψ h π ξ A v = fp ψ h π ξ hd.choose v := by
    unfold avg; rw [dif_pos hd]; rfl
  rw [e]
  have h1 : fp ψ h π ξ hd.choose (fp ψ h π ξ p v) = fp ψ h π ξ p v :=
    fp_of_eigen ξ hd.choose hp0.2.2.2.2.1 (card_pos hp0) _ fun a ha => fp_eigen ξ hp ha
  have h2 : fp ψ h π ξ hd.choose (fp ψ h π ξ p v) = fp ψ h π ξ hd.choose v :=
    fp_fp ξ p hd.choose hp.2.2.2.2.1 (card_pos hp) hp0.2.2.2.1 hp0.2.2.2.2.1 hp0.2.2.2.2.2 v hp0.2.2.1
  rw [← h2, h1]

variable {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem B_colEl (hB : Lv ψ h π s B) (x : Fin (m + 1) → k) (v w : V) :
    B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have hmem : unip k (m + 1) (Multiplicative.ofAdd x) ∈ Mir k (m + 1) := by
    first
    | exact MirU_le_Mir k (m + 1) ⟨Multiplicative.ofAdd x, rfl⟩
    | exact MirU_le_Mir (m + 1) ⟨Multiplicative.ofAdd x, rfl⟩
  have e := hB.mir _ hmem v w
  have hd : nabs k (Matrix.GeneralLinearGroup.det (unip k (m + 1) (Multiplicative.ofAdd x))) = 1 := by
    rw [det_unip]; simp [nabs]
  rw [hd, Real.one_rpow, Complex.ofReal_one, one_mul] at e
  exact e

theorem avg_eig (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (v : V)
    {y : Fin (m + 1) → k} (hy : y ∈ A) :
    π (colEl k m N h y) (avg ψ h π ξ A v) = ((ψ (ξ ⬝ᵥ y) : Circle) : ℂ) • avg ψ h π ξ A v := by
  obtain ⟨p, hp⟩ := avgData_exists ψ h π hB.cont hB.smooth ξ A hA v
  rw [avg_eq_fp ξ hp]
  exact fp_eigen ξ hp hy

theorem avg_selfadj (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A)
    (v w : V) : B (avg ψ h π ξ A v) w = B (avg ψ h π ξ A v) (avg ψ h π ξ A w) := by
  obtain ⟨pw, hpw⟩ := avgData_exists ψ h π hB.cont hB.smooth ξ A hA w
  set a := avg ψ h π ξ A v with ha_def
  have hterm : ∀ t ∈ pw.2,
      B a ((starRingEnd ℂ ((ψ (ξ ⬝ᵥ t) : Circle) : ℂ)) • π (colEl k m N h t) w) = B a w := by
    intro t ht
    have htA : -t ∈ A := A.neg_mem (hpw.2.2.2.2.1 t ht)
    have e1 : a = π (colEl k m N h t) (π (colEl k m N h (-t)) a) := by
      rw [← pi_colEl_add, add_neg_cancel, colEl_zero, map_one]; rfl
    have e2 : B a (π (colEl k m N h t) w) = ((ψ (ξ ⬝ᵥ (-t)) : Circle) : ℂ) * B a w := by
      conv_lhs => rw [e1]
      rw [B_colEl hB, avg_eig hB ξ hA v htA, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [LinearMap.map_smulₛₗ, starRingEnd_self_apply, e2, smul_eq_mul, ← mul_assoc, dotProduct_neg,
      AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, psi_mul_conj, one_mul]
  rw [avg_eq_fp ξ hpw]
  unfold fp
  rw [LinearMap.map_smulₛₗ, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, map_inv₀, map_natCast, inv_mul_cancel₀ (by exact_mod_cast (card_pos hpw).ne' : (pw.2.card : ℂ) ≠ 0),
    one_smul]

theorem avg_orth (hB : Lv ψ h π s B) (ξ η : Fin (m + 1) → k) {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A)
    (hne : ∃ x ∈ A, ψ (ξ ⬝ᵥ x) ≠ ψ (η ⬝ᵥ x)) (v w : V) : B (avg ψ h π ξ A v) (avg ψ h π η A w) = 0 := by
  obtain ⟨x, hx, hne⟩ := hne
  set a := avg ψ h π ξ A v
  set b := avg ψ h π η A w
  have e := B_colEl hB x a b
  rw [avg_eig hB ξ hA v hx, avg_eig hB η hA w hx, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    smul_eq_mul, smul_eq_mul, ← mul_assoc] at e
  by_contra hX
  apply hne
  have hc : ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * starRingEnd ℂ ((ψ (η ⬝ᵥ x) : Circle) : ℂ) = 1 := by
    have h1 : (((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * starRingEnd ℂ ((ψ (η ⬝ᵥ x) : Circle) : ℂ) - 1) * B a b = 0 := by
      rw [sub_mul, one_mul, e, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hX)
  have h2 : ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) = ((ψ (η ⬝ᵥ x) : Circle) : ℂ) := by
    calc ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ)
        = ((ψ (ξ ⬝ᵥ x) : Circle) : ℂ) * (starRingEnd ℂ ((ψ (η ⬝ᵥ x) : Circle) : ℂ) * ((ψ (η ⬝ᵥ x) : Circle) : ℂ)) := by
          rw [conj_mul_psi, mul_one]
      _ = ((ψ (η ⬝ᵥ x) : Circle) : ℂ) := by rw [← mul_assoc, hc, one_mul]
  first | exact Circle.ext h2 | exact Subtype.ext h2

theorem avg_avg (hB : Lv ψ h π s B) (ξ : Fin (m + 1) → k) {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A)
    (hA' : IsLat A') (hAA : A ≤ A') (v : V) :
    avg ψ h π ξ A' (avg ψ h π ξ A v) = avg ψ h π ξ A' v ∧ avg ψ h π ξ A (avg ψ h π ξ A' v) = avg ψ h π ξ A' v := by
  obtain ⟨p, hp⟩ := avgData_exists ψ h π hB.cont hB.smooth ξ A hA v
  obtain ⟨p', hp'⟩ := avgData_exists ψ h π hB.cont hB.smooth ξ A' hA' v
  constructor
  · have hu : AvgData ψ h π ξ A' (fp ψ h π ξ p v) p' := by
      refine ⟨hp'.1, hp'.2.1, fun a ha => ?_, hp'.2.2.2.1, hp'.2.2.2.2.1, hp'.2.2.2.2.2⟩
      rw [fp_comm, hp'.2.2.1 a ha]
    rw [avg_eq_fp ξ hp, avg_eq_fp ξ hu, avg_eq_fp ξ hp']
    exact fp_fp ξ p p' (fun t ht => hAA (hp.2.2.2.2.1 t ht)) (card_pos hp) hp'.2.2.2.1 hp'.2.2.2.2.1 hp'.2.2.2.2.2 v
      hp'.2.2.1
  · obtain ⟨q, hq⟩ := avgData_exists ψ h π hB.cont hB.smooth ξ A hA (avg ψ h π ξ A' v)
    rw [avg_eq_fp ξ hq]
    exact fp_of_eigen ξ q hq.2.2.2.2.1 (card_pos hq) _ fun a ha => avg_eig hB ξ hA' v (hAA ha)

end

end PositivityTheory.RgUd.Form.LeviSmoothness.alg
