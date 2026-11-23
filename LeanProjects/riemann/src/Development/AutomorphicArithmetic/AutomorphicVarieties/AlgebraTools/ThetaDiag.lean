import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private def theta : E →ₗ[B] (U.oddForm p q).Ext where
  toFun z := (U.oddForm p q).el (T.tr z)
    (cornerProj B (U.ep p) (U.ep q) z + cornerProj B (U.ep p) (U.ep q) (T.st z))
  map_add' z w := by
    apply OddForm.Ext.ext
    · simp
    · simp only [map_add, OddForm.od_el, OddForm.od_add]; abel
  map_smul' c z := by
    apply OddForm.Ext.ext
    · simp
    · simp only [map_smul, OddForm.od_el, OddForm.od_smul, RingHom.id_apply, smul_add]

private theorem theta_ev (z : E) : (theta U p q z).ev = T.tr z := rfl

private theorem theta_od (z : E) :
    (theta U p q z).od.1 = U.ep p * (z * U.ep q) + U.ep p * (T.st z * U.ep q) := rfl

private theorem theta_st (z : E) : theta U p q (T.st z) = theta U p q z := by
  apply OddForm.Ext.ext
  · rw [theta_ev, theta_ev, T.tr_st]
  · apply Subtype.ext
    rw [theta_od, theta_od, T.st_st, add_comm]

variable {p q}

private theorem theta_ep (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) : theta U p q (U.ep a) = 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  apply OddForm.Ext.ext
  · rw [theta_ev, OddForm.ev_one, U.tr_ep]
  · apply Subtype.ext
    rw [theta_od, U.st_ep, OddForm.od_one]
    rcases ha with h | h
    · rw [h, ← mul_assoc, (U.coi.idem p).eq, hpq0]
      simp
    · rw [h, (U.coi.idem q).eq, hpq0]
      simp

private theorem theta_diag (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) {u : E}
    (hu : U.ep a * u * U.ep a = u) : theta U p q u = T.tr u • 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hsu : U.ep a * T.st u * U.ep a = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, mul_assoc]
  have L1 : ∀ w : E, U.ep p * w * U.ep p = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp [mul_assoc, hpq0]
  have L2 : ∀ w : E, U.ep q * w * U.ep q = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp only [mul_assoc]
    rw [← mul_assoc (U.ep p), hpq0, zero_mul]
  apply OddForm.Ext.ext
  · rw [theta_ev, OddForm.ev_smul, OddForm.ev_one, mul_one]
  · apply Subtype.ext
    rw [theta_od, OddForm.od_smul, OddForm.od_one, smul_zero]
    rcases ha with h | h
    · rw [h] at hu hsu
      rw [L1 u hu, L1 _ hsu]
      simp
    · rw [h] at hu hsu
      rw [L2 u hu, L2 _ hsu]
      simp

private theorem theta_pq (hpq : p ≠ q) {u : E} (hu : U.ep p * u * U.ep q = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep q * T.st u * U.ep p = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hqp0, zero_mul, map_zero]
  · have h0 : U.ep p * (T.st u * U.ep q) = 0 := by
      rw [← hsu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, add_zero, ← mul_assoc, hu]

private theorem theta_qp (hpq : p ≠ q) {u : E} (hu : U.ep q * u * U.ep p = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = T.st u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep p * T.st u * U.ep q = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hpq0, zero_mul, map_zero]
  · have h0 : U.ep p * (u * U.ep q) = 0 := by
      rw [← hu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, zero_add, ← mul_assoc, hsu]

private theorem theta_mul (hpq : p ≠ q) {a b c : ι} (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (hc : c = p ∨ c = q) {u v : E} (hu : U.ep a * u * U.ep b = u) (hv : U.ep b * v * U.ep c = v) :
    theta U p q (u * v) = theta U p q u * theta U p q v := by
  have hidem : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hL : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → U.ep i * w = w := by
    intro i j w hw
    calc U.ep i * w = U.ep i * (U.ep i * w * U.ep j) := by rw [hw]
      _ = U.ep i * U.ep i * w * U.ep j := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hR : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → w * U.ep j = w := by
    intro i j w hw
    calc w * U.ep j = U.ep i * w * U.ep j * U.ep j := by rw [hw]
      _ = U.ep i * w * (U.ep j * U.ep j) := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hsc : ∀ {i : ι} {w : E}, U.ep i * w * U.ep i = w → w = T.tr w • U.ep i := by
    intro i w hw
    have h := U.corner_eq i w
    rwa [hw] at h
  have hbe : ∀ x y, (U.oddForm p q).be x y = T.tr ((x : E) * T.st (y : E)) := fun x y => rfl
  have hleft : ∀ {i k : ι}, (i = p ∨ i = q) → U.ep i * u * U.ep i = u → U.ep i * v * U.ep k = v →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hi hu' hv'
    have huv : u * v = T.tr u • v := by
      conv_lhs => rw [hsc hu', smul_mul_assoc, hL hv']
    rw [huv, map_smul, theta_diag U hpq hi hu', smul_mul_assoc, one_mul]
  have hright : ∀ {i k : ι}, (k = p ∨ k = q) → U.ep k * v * U.ep k = v → U.ep i * u * U.ep k = u →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hk hv' hu'
    have huv : u * v = T.tr v • u := by
      conv_lhs => rw [hsc hv', mul_smul_comm, hR hu']
    rw [huv, map_smul, theta_diag U hpq hk hv', mul_smul_comm, mul_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha, hb] at hu <;> rw [hb, hc] at hv
  · exact hleft (Or.inl rfl) hu hv
  · exact hleft (Or.inl rfl) hu hv
  · have huv : U.ep p * (u * v) * U.ep p = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inl rfl) huv]
    obtain ⟨h1, h2⟩ := theta_pq U hpq hu
    obtain ⟨h3, h4⟩ := theta_qp U hpq hv
    apply OddForm.Ext.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, T.st_st]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hright (Or.inr rfl) hv hu
  · exact hright (Or.inl rfl) hv hu
  · have huv : U.ep q * (u * v) * U.ep q = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inr rfl) huv]
    obtain ⟨h1, h2⟩ := theta_qp U hpq hu
    obtain ⟨h3, h4⟩ := theta_pq U hpq hv
    apply OddForm.Ext.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, ← T.st_mul, T.tr_st, T.tr_comm]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hleft (Or.inr rfl) hu hv
  · exact hleft (Or.inr rfl) hu hv

end

theorem UpperTheory.V.AlgebraTools.vr_hom :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → ∃ φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext, (∀ y, φ y = U.vr p q y) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = algebraMap B _ (T.tr y) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hA, hB, -, hD, -, -, hG⟩ := units_basic T o U
  have hvr : ∀ y i j, U.vr p q y i j = theta U p q (U.x i * y * T.st (U.x j)) := fun _ _ _ => rfl
  have hmul : ∀ y z, U.vr p q (y * z) = U.vr p q y * U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [hvr]
    have hs : U.x i * (y * z) * T.st (U.x j) = ∑ k, (U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j)) := by
      calc U.x i * (y * z) * T.st (U.x j) = U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j) := by
            rw [hB, mul_one, mul_assoc (U.x i) y z]
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact theta_mul U hpq (ho i) (ho k) (ho j) (hG i k y) (hG k j z)
  have hone : U.vr p q 1 = 1 := by
    refine Matrix.ext fun i j => ?_
    rw [hvr, mul_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [U.x_st]
      exact theta_ep U hpq (ho i)
    · rw [hA i j h, map_zero]
  have hadd : ∀ y z, U.vr p q (y + z) = U.vr p q y + U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.add_apply, mul_add, add_mul, map_add]
  have hzero : U.vr p q 0 = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [hvr, mul_zero, zero_mul, map_zero, Matrix.zero_apply]
  have hsmul : ∀ (r : B) y, U.vr p q (r • y) = r • U.vr p q y := by
    intro r y
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hcomm : ∀ r : B, U.vr p q (algebraMap B E r) = algebraMap B (Matrix ι ι (U.oddForm p q).Ext) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone]
  have hst : ∀ y, U.vr p q (T.st y) = (U.vr p q y)ᵀ := by
    intro y
    refine Matrix.ext fun i j => ?_
    rw [Matrix.transpose_apply, hvr, hvr, ← theta_st U p q (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have htr : ∀ y, (U.vr p q y).trace = algebraMap B _ (T.tr y) := by
    intro y
    rw [Matrix.trace, Algebra.algebraMap_eq_smul_one, hD y, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, hvr]
    exact theta_diag U hpq (ho i) (hG i i y)
  let φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext := { toFun := U.vr p q, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd, commutes' := hcomm }
  exact ⟨φ, fun y => rfl, hst, htr⟩
