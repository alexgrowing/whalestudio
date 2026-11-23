import Mathlib
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountConv

noncomputable section WacPartAbs
open Matrix

namespace Formalism.MainNotions.Gaps.CC.WA
open Formalism.UG

section WacAbs

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem wac_cT_add (τ : A →+* A) (M N : Matrix n n A) : cT τ (M + N) = cT τ M + cT τ N := by
  ext i j; simp [cT]

theorem wac_cT_sub (τ : A →+* A) (M N : Matrix n n A) : cT τ (M - N) = cT τ M - cT τ N := by
  ext i j; simp [cT]

theorem wac_cT_smul (τ : A →+* A) (c : A) (M : Matrix n n A) : cT τ (c • M) = τ c • cT τ M := by
  ext i j; simp [cT]

theorem wac_cT_cT (τ : A →+* A) (h : ∀ a, τ (τ a) = a) (M : Matrix n n A) : cT τ (cT τ M) = M := by
  ext i j; simp [cT, h]

def WacSm (S : Subring A) (c : A) (N : Matrix n n A) : Prop := ∀ i j, ∃ s ∈ S, N i j = c * s

theorem wac_sm_mono (S : Subring A) (c c' : A) (hc' : c' ∈ S) {N : Matrix n n A}
    (h : WacSm S (c * c') N) : WacSm S c N := by
  intro i j
  obtain ⟨s, hs, e⟩ := h i j
  exact ⟨c' * s, mul_mem hc' hs, by rw [e]; ring⟩

theorem wac_sm_sub (S : Subring A) (c : A) {M N : Matrix n n A} (hM : WacSm S c M)
    (hN : WacSm S c N) : WacSm S c (M - N) := by
  intro i j
  obtain ⟨s, hs, e⟩ := hM i j
  obtain ⟨t, ht, e'⟩ := hN i j
  exact ⟨s - t, sub_mem hs ht, by rw [Matrix.sub_apply, e, e']; ring⟩

theorem wac_sm_neg (S : Subring A) (c : A) {M : Matrix n n A} (hM : WacSm S c M) :
    WacSm S c (-M) := by
  intro i j
  obtain ⟨s, hs, e⟩ := hM i j
  exact ⟨-s, neg_mem hs, by rw [Matrix.neg_apply, e]; ring⟩

theorem wac_sm_mul_left (S : Subring A) (c d : A) (M : Matrix n n A) (hM : ∀ i j, d * M i j ∈ S)
    {N : Matrix n n A} (hN : WacSm S (c * d) N) : WacSm S c (M * N) := by
  intro i j
  choose s hs e using hN
  refine ⟨∑ k, (d * M i k) * s k j, Subring.sum_mem _ fun k _ => mul_mem (hM i k) (hs k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e]; ring

theorem wac_sm_mul_right (S : Subring A) (c d : A) (M : Matrix n n A) (hM : ∀ i j, d * M i j ∈ S)
    {N : Matrix n n A} (hN : WacSm S (c * d) N) : WacSm S c (N * M) := by
  intro i j
  choose s hs e using hN
  refine ⟨∑ k, s i k * (d * M k j), Subring.sum_mem _ fun k _ => mul_mem (hs i k) (hM k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e]; ring

theorem wac_sm_smul (S : Subring A) (c d a : A) (ha : d * a ∈ S)
    {N : Matrix n n A} (hN : WacSm S (c * d) N) : WacSm S c (a • N) := by
  intro i j
  obtain ⟨s, hs, e⟩ := hN i j
  exact ⟨(d * a) * s, mul_mem ha hs, by rw [Matrix.smul_apply, e, smul_eq_mul]; ring⟩

theorem wac_sm_cT (S : Subring A) (τ : A →+* A) (hτ : ∀ s ∈ S, τ s ∈ S) (c : A) (hc : τ c = c)
    {N : Matrix n n A} (hN : WacSm S c N) : WacSm S c (cT τ N) := by
  intro i j
  obtain ⟨s, hs, e⟩ := hN j i
  refine ⟨τ s, hτ s hs, ?_⟩
  show τ (N j i) = _
  rw [e, map_mul, hc]

theorem wac_inv_one_sub (S : Subring A) (c : A) (hc : c ∈ S)
    (hjac : ∀ s ∈ S, ∃ t ∈ S, (1 + c * s) * t = 1) {N : Matrix n n A} (hN : WacSm S c N) :
    ∃ W' : Matrix n n A, (∀ i j, W' i j ∈ S) ∧ (1 - N) * W' = 1 := by
  choose s hs e using hN
  let cS : S := ⟨c, hc⟩
  let NS : Matrix n n S := fun i j => ⟨s i j, hs i j⟩
  let WS : Matrix n n S := 1 - cS • NS
  have hmap : WS.map S.subtype = 1 - N := by
    ext i j
    simp only [WS, NS, cS, Matrix.map_apply, Matrix.sub_apply, map_sub, Subring.subtype_apply, e i j]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hdet : ∃ a : S, WS.det = 1 + cS * a := by
    have h1 : (Ideal.Quotient.mk (Ideal.span {cS})) WS.det = 1 := by
      rw [RingHom.map_det]
      have : (Ideal.Quotient.mk (Ideal.span {cS})).mapMatrix WS = 1 := by
        ext i j
        simp only [WS, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply,
          Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
        have h0 : (Ideal.Quotient.mk (Ideal.span {cS})) cS = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
        rw [h0, zero_mul, sub_zero]
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.one_apply_ne h]
      rw [this, Matrix.det_one]
    have h2 : WS.det - 1 ∈ Ideal.span {cS} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
    exact ⟨a, by rw [mul_comm, ha]; ring⟩
  obtain ⟨a, ha⟩ := hdet
  obtain ⟨t, ht, hta⟩ := hjac a a.2
  have hu : IsUnit WS.det := by
    rw [ha]
    refine IsUnit.of_mul_eq_one (⟨t, ht⟩ : S) ?_
    apply Subtype.ext
    simpa using hta
  refine ⟨(WS⁻¹).map S.subtype, fun i j => (WS⁻¹ i j).2, ?_⟩
  rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

end WacAbs

section WacCayley

variable {E A O : Type} [Field E] [CommRing A] [CommRing O] [IsDomain O]
  {n : Type} [Fintype n] [DecidableEq n]

structure WacCtx (ι : E →+* A) (σ : E →+* E) (τ : A →+* A) (S : Subring A) (d : O →+* E) : Prop where
  comm : ∀ e, τ (ι e) = ι (σ e)
  fix : ∀ r, σ (d r) = d r
  dS : ∀ r, ι (d r) ∈ S
  tS : ∀ s ∈ S, τ s ∈ S
  den : ∀ a : A, ∃ r : O, r ≠ 0 ∧ ι (d r) * a ∈ S
  dense : ∀ (a : A) (r : O), r ≠ 0 → ∃ e : E, ∃ s ∈ S, a - ι e = ι (d r) * s
  jac : ∃ w : O, w ≠ 0 ∧ ∀ s ∈ S, ∃ t ∈ S, (1 + ι (d w) * s) * t = 1
  ss : ∀ e, σ (σ e) = e
  two : (2 : E) ≠ 0
  nontriv : Nontrivial A

variable {ι : E →+* A} {σ : E →+* E} {τ : A →+* A} {S : Subring A} {d : O →+* E}

theorem wac_den_matrix (H : WacCtx ι σ τ S d) (M : Matrix n n A) :
    ∃ r : O, r ≠ 0 ∧ ∀ i j, ι (d r) * M i j ∈ S := by
  classical
  choose r hr0 hr using fun p : n × n => H.den (M p.1 p.2)
  refine ⟨∏ p, r p, Finset.prod_ne_zero_iff.2 fun p _ => hr0 p, fun i j => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ (i, j)), mul_comm (r (i, j)), map_mul,
    map_mul, mul_assoc]
  exact mul_mem (H.dS _) (hr (i, j))

theorem wac_cT_map (H : WacCtx ι σ τ S d) (M : Matrix n n E) :
    cT τ (M.map ι) = (cT σ M).map ι := by
  ext i j; simp [cT, H.comm]

theorem wac_map_one (ι : E →+* A) : (1 : Matrix n n E).map ι = 1 :=
  Matrix.map_one ι (map_zero ι) (map_one ι)

theorem wac_cayley (H : WacCtx ι σ τ S d) (J : Matrix n n E) (hJ : cT σ J = J)
    (hJd : IsUnit J.det) (G : Matrix n n A) (hG : cT τ G * J.map ι * G = J.map ι)
    (hP : IsUnit (1 + G).det) (r : O) (hr : r ≠ 0) :
    ∃ Γ : Matrix n n E, cT σ Γ * J * Γ = J ∧ WacSm S (ι (d r)) (G - Γ.map ι) := by
  have := H.nontriv
  set J' := J.map ι with hJ'
  set P := 1 + G with hPdef
  set B := P⁻¹ with hBdef
  have hPB : P * B = 1 := Matrix.mul_nonsing_inv _ hP
  have hBP : B * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hcPB : cT τ B * cT τ P = 1 := by rw [← cT_mul, hPB, cT_one]
  have hcP : cT τ P = 1 + cT τ G := by rw [hPdef, wac_cT_add, cT_one]
  have h1 : J' * P + cT τ P * J' = cT τ P * J' * P := by
    rw [hcP, hPdef]
    have e : (1 + cT τ G) * J' * (1 + G) = J' + J' * G + cT τ G * J' + cT τ G * J' * G := by
      noncomm_ring
    rw [e, hG]; noncomm_ring
  have hC : cT τ B * J' + J' * B = J' := by
    calc cT τ B * J' + J' * B = cT τ B * (J' * P + cT τ P * J') * B := by
          rw [mul_add, add_mul,
            show cT τ B * (J' * P) * B = cT τ B * J' * (P * B) by simp only [Matrix.mul_assoc],
            show cT τ B * (cT τ P * J') * B = (cT τ B * cT τ P) * J' * B by
              simp only [Matrix.mul_assoc], hPB, hcPB, Matrix.mul_one, Matrix.one_mul]
      _ = cT τ B * (cT τ P * J' * P) * B := by rw [h1]
      _ = (cT τ B * cT τ P) * J' * (P * B) := by simp only [Matrix.mul_assoc]
      _ = J' := by rw [hPB, hcPB, Matrix.one_mul, Matrix.mul_one]
  set Ji := J⁻¹ with hJidef
  have hJJi : J * Ji = 1 := Matrix.mul_nonsing_inv _ hJd
  have hJiJ : Ji * J = 1 := Matrix.nonsing_inv_mul _ hJd
  set J'i := Ji.map ι with hJ'i
  have hJ'1 : J'i * J' = 1 := by rw [hJ'i, hJ', ← Matrix.map_mul, hJiJ, wac_map_one]
  set c2 := ι (2⁻¹) with hc2
  have h22 : c2 * 2 = 1 := by
    rw [hc2, show (2 : A) = ι 2 from (map_ofNat ι 2).symm, ← map_mul, inv_mul_cancel₀ H.two, map_one]
  have hB : B = c2 • (B - J'i * cT τ B * J' + 1) := by
    have e1 : J'i * cT τ B * J' = 1 - B := by
      have e0 : cT τ B * J' = J' - J' * B := eq_sub_of_add_eq hC
      rw [Matrix.mul_assoc, e0, Matrix.mul_sub, hJ'1, ← Matrix.mul_assoc, hJ'1, Matrix.one_mul]
    rw [e1]
    calc B = (c2 * 2) • B := by rw [h22, one_smul]
      _ = c2 • (B - (1 - B) + 1) := by
          rw [mul_smul]; congr 1; rw [two_smul]; abel
  obtain ⟨rP, hrP0, hrP⟩ := wac_den_matrix H P
  obtain ⟨rJ, hrJ0, hrJ⟩ := wac_den_matrix H J'
  obtain ⟨rJi, hrJi0, hrJi⟩ := wac_den_matrix H J'i
  obtain ⟨r2, hr20, hr2⟩ := H.den c2
  obtain ⟨w, hw0, hjac⟩ := H.jac
  set R := w * r * rP * rP with hR
  set R' := R * r2 * rJ * rJi with hR'
  have hR'0 : R' ≠ 0 := by
    simp only [hR', hR]
    repeat' apply mul_ne_zero
    all_goals assumption
  choose b s hs hb using fun i j => H.dense (B i j) R' hR'0
  set B0' : Matrix n n E := Matrix.of b with hB0'
  set Δ' := B - B0'.map ι with hΔ'def
  have hΔ' : WacSm S (ι (d R')) Δ' := fun i j => ⟨s i j, hs i j, by
    simpa [hΔ'def, hB0'] using hb i j⟩
  set B0 : Matrix n n E := (2⁻¹ : E) • (B0' - Ji * cT σ B0' * J + 1) with hB0
  have hιB0 : B0.map ι = c2 • (B0'.map ι - J'i * cT τ (B0'.map ι) * J' + 1) := by
    rw [hB0, Matrix.map_smul' _ _ _ (map_mul ι), wac_cT_map H]
    congr 1
    rw [Matrix.map_add _ (map_add ι), Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_mul, wac_map_one]
  set Δ := B - B0.map ι with hΔdef
  have hΔ : Δ = c2 • (Δ' - J'i * cT τ Δ' * J') := by
    calc Δ = c2 • (B - J'i * cT τ B * J' + 1) -
          c2 • (B0'.map ι - J'i * cT τ (B0'.map ι) * J' + 1) := by rw [← hB, ← hιB0]
      _ = c2 • (Δ' - J'i * cT τ Δ' * J') := by
          rw [← smul_sub]; congr 1
          rw [hΔ'def, wac_cT_sub, Matrix.mul_sub, Matrix.sub_mul]; abel
  have hfixδ : ∀ x : O, τ (ι (d x)) = ι (d x) := fun x => by rw [H.comm, H.fix]
  have hR'eq : ι (d R') = ι (d R) * ι (d r2) * ι (d rJ) * ι (d rJi) := by
    simp only [hR', map_mul]
  have hΔsm : WacSm S (ι (d R)) Δ := by
    rw [hΔ]
    apply wac_sm_smul S (ι (d R)) (ι (d r2)) c2 hr2
    apply wac_sm_sub
    · apply wac_sm_mono S _ (ι (d rJ)) (H.dS _)
      apply wac_sm_mono S _ (ι (d rJi)) (H.dS _)
      rw [← hR'eq]; exact hΔ'
    · apply wac_sm_mul_right S _ (ι (d rJ)) J' hrJ
      apply wac_sm_mul_left S _ (ι (d rJi)) J'i hrJi
      rw [← hR'eq]
      exact wac_sm_cT S τ H.tS _ (hfixδ _) hΔ'
  have hΔP : WacSm S (ι (d (w * r * rP))) (Δ * P) := by
    apply wac_sm_mul_right S _ (ι (d rP)) P hrP
    rw [← map_mul, ← map_mul]; exact hΔsm
  have hΔPw : WacSm S (ι (d w)) (Δ * P) := by
    apply wac_sm_mono S _ (ι (d (r * rP))) (H.dS _)
    rw [← map_mul, ← map_mul, ← mul_assoc]; exact hΔP
  have hPΔP : WacSm S (ι (d r)) (P * (Δ * P)) := by
    apply wac_sm_mono S _ (ι (d w)) (H.dS _)
    apply wac_sm_mul_left S _ (ι (d rP)) P hrP
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm r w]; exact hΔP
  obtain ⟨W', hW'S, hW'⟩ := wac_inv_one_sub S (ι (d w)) (H.dS w) hjac hΔPw
  have hιB0' : B0.map ι = (1 - Δ * P) * B := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hPB, Matrix.mul_one, hΔdef, sub_sub_cancel]
  have hinv : B0.map ι * (P * W') = 1 := by
    rw [hιB0', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBP, Matrix.one_mul, hW']
  have hB0d : B0.det ≠ 0 := by
    intro h0
    have hu : IsUnit (B0.map ι).det := Matrix.isUnit_det_of_right_inverse hinv
    have e : (B0.map ι).det = ι B0.det := by
      rw [RingHom.map_det]; rfl
    rw [e, h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hB0u : IsUnit B0.det := IsUnit.mk0 _ hB0d
  set B0i := B0⁻¹ with hB0idef
  have hB0B0i : B0 * B0i = 1 := Matrix.mul_nonsing_inv _ hB0u
  have hB0iB0 : B0i * B0 = 1 := Matrix.nonsing_inv_mul _ hB0u
  have hιB0i : B0i.map ι = P * W' := by
    calc B0i.map ι = B0i.map ι * (B0.map ι * (P * W')) := by rw [hinv, Matrix.mul_one]
      _ = (B0i.map ι * B0.map ι) * (P * W') := (Matrix.mul_assoc _ _ _).symm
      _ = P * W' := by rw [← Matrix.map_mul, hB0iB0, wac_map_one, Matrix.one_mul]
  have hcJi : cT σ Ji = Ji := by
    have e : cT σ Ji * J = 1 := by
      calc cT σ Ji * J = cT σ Ji * cT σ J := by rw [hJ]
        _ = cT σ (J * Ji) := (cT_mul _ _ _).symm
        _ = 1 := by rw [hJJi, cT_one]
    calc cT σ Ji = cT σ Ji * (J * Ji) := by rw [hJJi, Matrix.mul_one]
      _ = (cT σ Ji * J) * Ji := (Matrix.mul_assoc _ _ _).symm
      _ = Ji := by rw [e, Matrix.one_mul]
  have hcB0 : cT σ B0 = (2⁻¹ : E) • (cT σ B0' - J * (B0' * Ji) + 1) := by
    rw [hB0, wac_cT_smul, wac_cT_add, wac_cT_sub, cT_mul, cT_mul, wac_cT_cT σ H.ss, hJ, hcJi, cT_one,
      map_inv₀, map_ofNat]
  have hC0 : cT σ B0 * J + J * B0 = J := by
    have e1 : (cT σ B0' - J * (B0' * Ji) + 1) * J = cT σ B0' * J - J * B0' + J := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hJiJ, Matrix.mul_one]
    have e2 : J * (B0' - Ji * cT σ B0' * J + 1) = J * B0' - cT σ B0' * J + J := by
      rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hJJi, Matrix.one_mul]
    rw [hcB0, Matrix.smul_mul, e1]
    conv_lhs => rw [hB0]
    rw [Matrix.mul_smul, e2, ← smul_add]
    have e3 : cT σ B0' * J - J * B0' + J + (J * B0' - cT σ B0' * J + J) = (2 : E) • J := by
      rw [two_smul]; abel
    rw [e3, smul_smul, inv_mul_cancel₀ H.two, one_smul]
  set Γ := B0i - 1 with hΓdef
  have hΓB : Γ * B0 = 1 - B0 := by rw [hΓdef, Matrix.sub_mul, hB0iB0, Matrix.one_mul]
  have hkey : cT σ B0 * (cT σ Γ * J * Γ) * B0 = cT σ B0 * J * B0 := by
    calc cT σ B0 * (cT σ Γ * J * Γ) * B0 = cT σ (Γ * B0) * J * (Γ * B0) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = (1 - cT σ B0) * J * (1 - B0) := by rw [hΓB, wac_cT_sub, cT_one]
      _ = J - (cT σ B0 * J + J * B0) + cT σ B0 * J * B0 := by noncomm_ring
      _ = cT σ B0 * J * B0 := by rw [hC0]; abel
  have hcB0i : cT σ B0i * cT σ B0 = 1 := by rw [← cT_mul, hB0B0i, cT_one]
  have hΓ : cT σ Γ * J * Γ = J := by
    calc cT σ Γ * J * Γ = (cT σ B0i * cT σ B0) * (cT σ Γ * J * Γ) * (B0 * B0i) := by
          rw [hcB0i, hB0B0i, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ B0i * (cT σ B0 * (cT σ Γ * J * Γ) * B0) * B0i := by simp only [Matrix.mul_assoc]
      _ = cT σ B0i * (cT σ B0 * J * B0) * B0i := by rw [hkey]
      _ = (cT σ B0i * cT σ B0) * J * (B0 * B0i) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hcB0i, hB0B0i, Matrix.one_mul, Matrix.mul_one]
  refine ⟨Γ, hΓ, ?_⟩
  have hW'' : W' = 1 + Δ * P * W' := by
    have e := hW'
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    exact eq_add_of_sub_eq e
  have hfin : G - Γ.map ι = -(P * (Δ * P) * W') := by
    have e1 : Γ.map ι = P * W' - 1 := by
      rw [hΓdef, Matrix.map_sub _ (map_sub ι), hιB0i, wac_map_one]
    have e2 : G = P - 1 := by rw [hPdef]; abel
    rw [e1, e2]
    conv_lhs => rw [hW'']
    rw [Matrix.mul_add, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    abel
  rw [hfin]
  apply wac_sm_neg
  apply wac_sm_mul_right S _ 1 W' (by simpa using hW'S)
  rw [mul_one]; exact hPΔP

end WacCayley

end Formalism.MainNotions.Gaps.CC.WA

end WacPartAbs

noncomputable section WacPartSc

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.WA

open Formalism.UG

theorem wac_unit_exists {E A : Type} [Field E] [CommRing A] [IsArtinianRing A]
    {n : Type} [Fintype n] [DecidableEq n] (i : E →+* A) (G : Matrix n n A) (T : Set E)
    (hT : T.Infinite) : ∃ l ∈ T, IsUnit (i l • (1 : Matrix n n A) + G).det := by
  classical
  set χ : Polynomial A := (-G).charpoly with hχ
  have heval : ∀ a : A, χ.eval a = (a • (1 : Matrix n n A) + G).det := by
    intro a
    rw [hχ, Matrix.eval_charpoly, sub_neg_eq_add]
    congr 2
    ext p q
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hbad : ∀ m : Ideal A, m.IsMaximal → {l : E | χ.eval (i l) ∈ m}.Finite := by
    intro m hm
    let _ := Ideal.Quotient.field m
    let φ : E →+* A ⧸ m := (Ideal.Quotient.mk m).comp i
    have hφ : Function.Injective φ := φ.injective
    have hmon : (χ.map (Ideal.Quotient.mk m)).Monic := (Matrix.charpoly_monic _).map _
    have hfin : (φ ⁻¹' ((χ.map (Ideal.Quotient.mk m)).roots.toFinset : Set (A ⧸ m))).Finite :=
      Set.Finite.preimage hφ.injOn (Finset.finite_toSet _)
    refine hfin.subset ?_
    intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot.def]
    show Polynomial.eval (Ideal.Quotient.mk m (i l)) _ = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hl
  have hU : (⋃ m ∈ {I : Ideal A | I.IsMaximal}, {l : E | χ.eval (i l) ∈ m}).Finite :=
    Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite A) (fun m hm => hbad m hm)
  obtain ⟨l, hlT, hl⟩ := hT.exists_notMem_finite hU
  refine ⟨l, hlT, ?_⟩
  by_contra hnu
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (a := (i l • (1 : Matrix n n A) + G).det) hnu
  apply hl
  simp only [Set.mem_iUnion]
  refine ⟨m, hm, ?_⟩
  show χ.eval (i l) ∈ m
  rw [heval]
  exact hmem

theorem wac_norm_one_infinite {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσσ : ∀ e, σ (σ e) = e) (hθ : ∃ θ, σ θ ≠ θ) :
    {l : E | l * σ l = 1}.Infinite := by
  obtain ⟨θ, hθ⟩ := hθ
  have hne : ∀ a : F, algebraMap F E a + θ ≠ 0 := by
    intro a h
    apply hθ
    have : θ = algebraMap F E (-a) := by
      rw [map_neg]; exact (eq_neg_of_add_eq_zero_right h)
    rw [this, AlgHom.commutes]
  have hne' : ∀ a : F, algebraMap F E a + σ θ ≠ 0 := by
    intro a h
    apply hne a
    have := congrArg σ h
    rw [map_add, AlgHom.commutes, hσσ, map_zero] at this
    exact this
  let f : F → E := fun a => (algebraMap F E a + θ) / (algebraMap F E a + σ θ)
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    rw [div_eq_div_iff (hne' a) (hne' b)] at hab
    have h1 : (algebraMap F E a - algebraMap F E b) * (σ θ - θ) = 0 := by
      linear_combination hab
    rcases mul_eq_zero.1 h1 with h | h
    · exact (algebraMap F E).injective (sub_eq_zero.1 h)
    · exact absurd (sub_eq_zero.1 h) hθ
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨a, rfl⟩
  simp only [f, Set.mem_ofPred_eq]
  rw [map_div₀, map_add, map_add, AlgHom.commutes, hσσ]
  field_simp [hne a, hne' a]

theorem wac_artinian (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
  have : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  have : Module.Finite (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := Module.Finite.base_change _ _ _
  have : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
  exact RingEquiv.isArtinianRing (Algebra.TensorProduct.comm F (v.adicCompletion F) E).toRingEquiv

theorem wac_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (hσσ : ∀ e, σ (σ e) = e)
    (hθ : ∃ θ, σ θ ≠ θ) (v : HeightOneSpectrum (𝓞 F))
    (G : Matrix n n (E ⊗[F] v.adicCompletion F)) :
    ∃ l : E, l * σ l = 1 ∧
      IsUnit (1 + inclE (F := F) (v.adicCompletion F) (σ l) • G).det := by
  have := wac_artinian F E v
  obtain ⟨l, hl, hu⟩ := wac_unit_exists (inclE (F := F) (v.adicCompletion F)) G _
    (wac_norm_one_infinite σ hσσ hθ)
  refine ⟨l, hl, ?_⟩
  have hl' : inclE (F := F) (v.adicCompletion F) (σ l) * inclE (F := F) (v.adicCompletion F) l = 1 := by
    rw [← map_mul, mul_comm, hl, map_one]
  have e : (1 + inclE (F := F) (v.adicCompletion F) (σ l) • G) =
      inclE (F := F) (v.adicCompletion F) (σ l) •
        (inclE (F := F) (v.adicCompletion F) l • (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) + G) := by
    rw [smul_add, smul_smul, hl', one_smul]
  rw [e, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hl').pow _).mul hu

end Formalism.MainNotions.Gaps.CC.WA

end WacPartSc

noncomputable section WacPartNt

open Matrix TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.MainNotions.Gaps.CC.WA

open Formalism.UG Formalism.UG.P

section WaNt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem wac_incl_base (a : F) :
    inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E a) =
      (1 : E) ⊗ₜ[F] (algebraMap F (v.adicCompletion F) a) := by
  show (algebraMap F E a) ⊗ₜ[F] (1 : v.adicCompletion F) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem wac_dS (r : 𝓞 F) :
    inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E (r : F)) ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  rw [wac_incl_base]
  refine Subring.subset_closure (Or.inr ⟨⟨_, ?_⟩, rfl⟩)
  have := levelaf_int_mem_v v r
  rwa [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at this

theorem wac_sig_S (σ : E →ₐ[F] E) (s : E ⊗[F] v.adicCompletion F)
    (hs : s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring) :
    sigR σ (v.adicCompletion F) s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := by
  refine Subring.closure_induction (p := fun s _ => sigR σ (v.adicCompletion F) s ∈
    tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · have h1 : sigR σ (v.adicCompletion F)
          (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) =
          (σ (algebraMap (𝓞 E) E b)) ⊗ₜ[F] (1 : v.adicCompletion F) := by
        simp [sigR]
      show sigR σ _ (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ _
      rw [h1]
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E b)) :=
        (RingOfIntegers.isIntegral_coe b).map ((σ : E →+* E).toIntAlgHom)
      exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, hint⟩, rfl⟩⟩, rfl⟩)
    · have h1 : sigR σ (v.adicCompletion F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ _
      rw [h1]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  · rw [map_zero]; exact zero_mem _
  · rw [map_one]; exact one_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

theorem wac_den (a : E ⊗[F] v.adicCompletion F) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E (r : F)) * a ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  obtain ⟨N, hN, hmem⟩ := levelv_denom v a
  refine ⟨(N : 𝓞 F), Nat.cast_ne_zero.2 hN, ?_⟩
  have : inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E (((N : 𝓞 F)) : F)) * a =
      N • a := by
    rw [nsmul_eq_mul]
    congr 1
    have h0 : (((N : 𝓞 F)) : F) = (N : F) := map_natCast (algebraMap (𝓞 F) F) N
    rw [h0, map_natCast, map_natCast]
  rw [this]
  exact hmem

theorem wac_local_dense (x : v.adicCompletion F) (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ a : F, ∃ y ∈ v.adicCompletionIntegers F,
      x - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (r : F) * y := by
  obtain ⟨d, hd0, hd⟩ := levelaf_local_denom v x
  obtain ⟨s, hs⟩ := csApprox_local v (r * d) (mul_ne_zero hr hd0) _ hd
  have hcd : algebraMap (𝓞 F) (v.adicCompletion F) d ≠ 0 := levelaf_algebraMap_ne_zero v d hd0
  have hcr : algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := levelaf_algebraMap_ne_zero v r hr
  have hcrd : algebraMap (𝓞 F) (v.adicCompletion F) (r * d) ≠ 0 :=
    levelaf_algebraMap_ne_zero v _ (mul_ne_zero hr hd0)
  refine ⟨(s : F) / (d : F), (algebraMap (𝓞 F) (v.adicCompletion F) d * x -
    algebraMap (𝓞 F) (v.adicCompletion F) s) / algebraMap (𝓞 F) (v.adicCompletion F) (r * d), ?_, ?_⟩
  · rw [mem_adicCompletionIntegers, map_div₀, csApprox_val_int v (r * d)]
    have hpos : 0 < v.intValuation (r * d) :=
      zero_lt_iff.2 (v.intValuation_ne_zero _ (mul_ne_zero hr hd0))
    exact (div_le_one₀ hpos).2 hs.le
  · have e1 : algebraMap F (v.adicCompletion F) ((s : F) / (d : F)) =
        algebraMap (𝓞 F) (v.adicCompletion F) s / algebraMap (𝓞 F) (v.adicCompletion F) d := by
      rw [map_div₀, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) s,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) d]
    have e2 : algebraMap F (v.adicCompletion F) (r : F) =
        algebraMap (𝓞 F) (v.adicCompletion F) r := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) r]
    rw [e1, e2, map_mul]
    field_simp

theorem wac_dense (a : E ⊗[F] v.adicCompletion F) (r : 𝓞 F) (hr : r ≠ 0) :
    ∃ e : E, ∃ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
        (v.adicCompletionIntegers F).toSubring,
      a - inclE (F := F) (E := E) (v.adicCompletion F) e =
        inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E (r : F)) * s := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul e x =>
    obtain ⟨d, hd0, hd⟩ := wac_den v (inclE (F := F) (E := E) (v.adicCompletion F) e)
    obtain ⟨a0, y, hy, hxy⟩ := wac_local_dense v x (r * d) (mul_ne_zero hr hd0)
    refine ⟨a0 • e, _, mul_mem hd (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)), ?_⟩
    have h1 : inclE (F := F) (E := E) (v.adicCompletion F) (a0 • e) =
        e ⊗ₜ[F] (algebraMap F (v.adicCompletion F) a0) := by
      show (a0 • e) ⊗ₜ[F] (1 : v.adicCompletion F) = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.tmul_sub, hxy]
    show _ = ((algebraMap F E (r : F)) ⊗ₜ[F] (1 : v.adicCompletion F)) *
      ((((algebraMap F E (d : F)) ⊗ₜ[F] (1 : v.adicCompletion F)) *
        (e ⊗ₜ[F] (1 : v.adicCompletion F))) * ((1 : E) ⊗ₜ[F] y))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have h2 : (((r * d : 𝓞 F)) : F) = (r : F) * (d : F) := map_mul (algebraMap (𝓞 F) F) r d
    rw [h2, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, map_mul, mul_assoc]
  | add a b ha hb =>
    obtain ⟨e1, s1, hs1, h1⟩ := ha
    obtain ⟨e2, s2, hs2, h2⟩ := hb
    refine ⟨e1 + e2, s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [map_add, mul_add, ← h1, ← h2]
    ring

def wacF (E : Type) [Field E] [NumberField E] [Algebra F E] :
    v.adicCompletionIntegers F →+* E ⊗[F] v.adicCompletion F :=
  (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F).toRingHom.comp
    (v.adicCompletionIntegers F).subtype

theorem wacF_apply (y : v.adicCompletionIntegers F) :
    wacF v E y = (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := rfl

theorem wac_integral (s : E ⊗[F] v.adicCompletion F)
    (hs : s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring) : (wacF v E).IsIntegralElem s := by
  refine Subring.closure_induction (p := fun s _ => (wacF v E).IsIntegralElem s)
    ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · have h1 : IsIntegral ℤ (inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) :=
        map_isIntegral_int (inclE (F := F) (E := E) (v.adicCompletion F))
          (RingOfIntegers.isIntegral_coe b)
      have h2 : algebraMap ℤ (E ⊗[F] v.adicCompletion F) =
          (wacF v E).comp (Int.castRingHom (v.adicCompletionIntegers F)) := RingHom.ext_int _ _
      have h3 : ((wacF v E).comp (Int.castRingHom (v.adicCompletionIntegers F))).IsIntegralElem
          (inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap (𝓞 E) E b)) := by
        rw [← h2]; exact h1
      exact RingHom.IsIntegralElem.of_comp h3
    · exact (wacF v E).isIntegralElem_map (x := ⟨y, hy⟩)
  · exact (wacF v E).isIntegralElem_zero
  · exact (wacF v E).isIntegralElem_one
  · intro x y _ _ hx hy; exact RingHom.IsIntegralElem.add _ hx hy
  · intro x _ hx; exact RingHom.IsIntegralElem.neg _ hx
  · intro x y _ _ hx hy; exact RingHom.IsIntegralElem.mul _ hx hy

def wacFS (E : Type) [Field E] [NumberField E] [Algebra F E] :
    v.adicCompletionIntegers F →+* tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring :=
  (wacF v E).codRestrict _ (fun y => Subring.subset_closure (Or.inr ⟨⟨y.1, y.2⟩, rfl⟩))

theorem wacFS_integral : (wacFS v E).IsIntegral := by
  intro x
  obtain ⟨p, hm, hp⟩ := wac_integral v x.1 x.2
  refine ⟨p, hm, Subtype.ext ?_⟩
  have := Polynomial.hom_eval₂ p (wacFS v E) (tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring).subtype x
  have h2 : ((tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring).subtype).comp (wacFS v E) = wacF v E := rfl
  rw [h2] at this
  exact this.trans hp

theorem wac_jac : ∃ ϖ : 𝓞 F, ϖ ≠ 0 ∧ ∀ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring,
    ∃ t ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring,
      (1 + inclE (F := F) (E := E) (v.adicCompletion F) (algebraMap F E (ϖ : F)) * s) * t = 1 := by
  obtain ⟨ϖ, hmem, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨ϖ, h0, fun s hs => ?_⟩
  set S := tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
    with hS
  let c : S := ⟨_, wac_dS (E := E) v ϖ⟩
  let u : S := 1 + c * ⟨s, hs⟩
  have hu : IsUnit u := by
    by_contra hnu
    obtain ⟨m, hm, hum⟩ := exists_max_ideal_of_mem_nonunits (show u ∈ nonunits S from hnu)
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (wacFS v E) (wacFS_integral v) m
    have hloc := IsLocalRing.eq_maximalIdeal hmax
    let w : v.adicCompletionIntegers F := ⟨_, levelaf_int_mem_v v ϖ⟩
    have hw : w ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hwu
      obtain ⟨y, hy⟩ := hwu.exists_right_inv
      have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) ϖ) * Valued.v (y : v.adicCompletion F)
          = 1 := by
        rw [← map_mul]
        have := congrArg Subtype.val hy
        simp only [w] at this
        rw [show algebraMap (𝓞 F) (v.adicCompletion F) ϖ * (y : v.adicCompletion F) = 1 from this,
          map_one]
      have h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) ϖ) < 1 := by
        rw [csApprox_val_int]
        exact (v.intValuation_lt_one_iff_mem ϖ).2 hmem
      have h3 : Valued.v (y : v.adicCompletion F) ≤ 1 := y.2
      have h4 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) ϖ) *
          Valued.v (y : v.adicCompletion F) < 1 :=
        lt_of_le_of_lt (by simpa using mul_le_mul' (le_refl _) h3) h2
      exact absurd h1 h4.ne
    rw [← hloc, Ideal.mem_comap] at hw
    have hc : wacFS v E w = c := by
      apply Subtype.ext
      show (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (v.adicCompletion F) ϖ) = _
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
      exact (wac_incl_base v _).symm
    rw [hc] at hw
    have h1 : (1 : S) ∈ m := by
      have : (1 : S) = u - c * ⟨s, hs⟩ := by simp [u]
      rw [this]
      exact sub_mem hum (m.mul_mem_right _ hw)
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  exact ⟨t.1, t.2, congrArg Subtype.val ht⟩

end WaNt

end Formalism.MainNotions.Gaps.CC.WA

end WacPartNt

noncomputable section WacPartTop

open Matrix TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.MainNotions.Gaps.CC.WA

open Formalism.UG Formalism.UG.P

section WacTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem wac_ctx (σ : E →ₐ[F] E) (hσσ : ∀ e, σ (σ e) = e) (v : HeightOneSpectrum (𝓞 F)) :
    WacCtx (O := 𝓞 F) (inclE (F := F) (E := E) (v.adicCompletion F)) (σ : E →+* E)
      (sigR σ (v.adicCompletion F))
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      ((algebraMap F E).comp (algebraMap (𝓞 F) F)) where
  comm e := by simp [sigR, inclE]
  fix r := by simp
  dS r := wac_dS v r
  tS s hs := wac_sig_S v σ s hs
  den a := wac_den v a
  dense a r hr := wac_dense v a r hr
  jac := wac_jac v
  ss := hσσ
  two := two_ne_zero
  nontriv := (inclE_injective F E (v.adicCompletion F)).nontrivial

theorem wac_core (σ : E →ₐ[F] E) (J : Matrix n n E) (hσσ : ∀ e, σ (σ e) = e)
    (hθ : ∃ θ, σ θ ≠ θ) (hJ : IsHerm (σ : E →+* E) J) (hJd : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (g : GL n (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ UPts σ J (v.adicCompletion F)) (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ γ ∈ UJ (σ : E →+* E) J, ∀ i j, ∃ s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
        (v.adicCompletionIntegers F).toSubring,
      (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
          inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
        inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s := by
  have H := wac_ctx σ hσσ v
  set ι := inclE (F := F) (E := E) (v.adicCompletion F) with hι
  set τ := sigR σ (v.adicCompletion F) with hτ
  set S := tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
    with hS
  set G : Matrix n n (E ⊗[F] v.adicCompletion F) := (g : Matrix n n (E ⊗[F] v.adicCompletion F))
    with hGdef
  have hG : cT τ G * J.map ι * G = J.map ι := hg
  obtain ⟨l, hl, hu⟩ := wac_scalar σ hσσ hθ v G
  have hl1 : ι l * ι (σ l) = 1 := by rw [← map_mul, hl, map_one]
  have hG1 : cT τ (ι (σ l) • G) * J.map ι * (ι (σ l) • G) = J.map ι := by
    have e : τ (ι (σ l)) = ι l := by
      have := H.comm (σ l)
      rw [this]; exact congrArg ι (hσσ l)
    rw [wac_cT_smul, e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hl1, one_smul,
      hG]
  obtain ⟨rl, hrl0, hrl⟩ := H.den (ι l)
  obtain ⟨Γ1, hΓ1, hsm⟩ := wac_cayley H J hJ hJd (ι (σ l) • G) hG1 hu (D * rl) (mul_ne_zero hD hrl0)
  have hΓ : cT (σ : E →+* E) (l • Γ1) * J * (l • Γ1) = J := by
    rw [wac_cT_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : (σ : E →+* E) l * l = 1 := by rw [mul_comm]; exact hl
    rw [this, one_smul, hΓ1]
  have hdet : (l • Γ1).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hΓ
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJd.ne_zero this.symm
  refine ⟨Matrix.nonsingInvUnit (l • Γ1) (IsUnit.mk0 _ hdet), hΓ, ?_⟩
  have hfin : G - (l • Γ1).map ι = ι l • (ι (σ l) • G - Γ1.map ι) := by
    rw [smul_sub, smul_smul, hl1, one_smul, Matrix.map_smul' _ _ _ (map_mul ι)]
  have hsm2 : WacSm S (ι ((algebraMap F E).comp (algebraMap (𝓞 F) F) D)) (G - (l • Γ1).map ι) := by
    rw [hfin]
    apply wac_sm_smul S _ _ (ι l) hrl
    rw [← map_mul, ← map_mul]; exact hsm
  intro i j
  obtain ⟨s, hs, e⟩ := hsm2 i j
  exact ⟨s, hs, e⟩

end WacTop

end Formalism.MainNotions.Gaps.CC.WA

end WacPartTop

noncomputable section WacPartFinal

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.WA

open Formalism.UG Formalism.MainNotions.Gaps.CC

theorem waCore : Surj.WACore :=
  fun _ _ _ _ _ _ _ _ _ _ σ J hσσ hθ hJ hJd v g hg D hD => wac_core σ J hσσ hθ hJ hJd v g hg D hD

theorem weakApprox1 : Surj.WeakApprox1 := Surj.wal_main waCore

theorem genusIn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
    (hfix : ∀ e, σ e = e → ∃ a : F, algebraMap F E a = e) (hθ : ∃ θ, σ θ ≠ θ) :
    GenusIn σ (1 : Matrix (Fin k) (Fin k) E) :=
  Surj.genusIn_of_core waCore σ hσ hfix hθ

end Formalism.MainNotions.Gaps.CC.WA

end WacPartFinal
