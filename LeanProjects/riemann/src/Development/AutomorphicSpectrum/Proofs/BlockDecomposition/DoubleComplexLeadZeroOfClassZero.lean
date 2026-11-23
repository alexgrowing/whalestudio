import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre.RowKer

variable {R : Type} [CommRing R] (K : DCx.{w} R)

theorem Dv_mem (W : ∀ p q, K.X p q) (p q : ℕ) : K.Dv W p q ∈ (K.col p).B q := by
  cases q with
  | zero =>
    have h : K.Dv W p 0 = 0 := by cases p <;> rfl
    rw [h]
    exact Submodule.zero_mem _
  | succ q => exact ⟨W p q, rfl⟩

theorem dv_low (W x : ∀ p q, K.X p q) (hD : K.D W = x) (k q : ℕ) (h0 : ∀ p q, p < k → W p q = 0)
    (hx : x k (q + 1) = 0) : K.dv k q (W k q) = 0 := by
  have h1 := congrFun (congrFun hD k) (q + 1)
  rw [DCx.D_apply, hx] at h1
  have h2 : K.Dh W k (q + 1) = 0 := by
    cases k with
    | zero => rfl
    | succ k =>
      show K.dh k (q + 1) (W k (q + 1)) = 0
      rw [h0 k _ (by omega), map_zero]
  rw [h2, zero_add] at h1
  exact Auxfb.zsm_cancel k _ h1

theorem push_step (n k q : ℕ) (hkq : k + q + 1 = n) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (h0 : ∀ p q, p < k → W p q = 0)
    (hv : K.dv k q (W k q) = 0) (hH : Subsingleton ((K.col k).H q)) (hq : 0 < q) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k + 1 → W' p q = 0 := by
  have hB : W k q ∈ (K.col k).B q :=
    ((P.cls_surj (K.col k) q).2.1 _ hv).1 (Subsingleton.elim _ _)
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨y, hy⟩ := hB
  have hy' : K.dv k q y = W k (q + 1) := hy
  have hsq : ((-1 : ℤ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have hDY : K.D (K.sgl k q ((-1 : ℤ) ^ k • y)) =
      K.sgl (k + 1) q (K.dh k q ((-1 : ℤ) ^ k • y)) + K.sgl k (q + 1) (W k (q + 1)) := by
    rw [K.D_sgl, map_zsmul (K.dv k q), hy', map_zsmul (K.sgl k (q + 1)), smul_smul, hsq, one_smul]
  refine ⟨W - K.D (K.sgl k q ((-1 : ℤ) ^ k • y)), fun p r h => ?_, ?_, fun p r hp => ?_⟩
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply, hs p r h,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1)]
    simp
  · rw [map_sub, K.DD, sub_zero]
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), zero_add]
    by_cases h : p = k ∧ r = q + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [K.sgl_self, sub_self]
    · rw [K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1), sub_zero]
      by_cases hpk : p < k
      · exact h0 p r hpk
      · exact hs p r (by omega)

theorem push (n a i : ℕ) (hn : n = a + (i + 1)) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (hx : ∀ p q, p < i + 1 → K.D W p q = 0)
    (hac : ∀ p q, a < q → Subsingleton ((K.col p).H q)) (k : ℕ) (hk : k ≤ i) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k → W' p q = 0 := by
  induction k with
  | zero => exact ⟨W, hs, rfl, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩
  | succ k ih =>
    obtain ⟨W₁, hs₁, hD₁, h₁⟩ := ih (by omega)
    have hv : K.dv k (a + i - k) (W₁ k (a + i - k)) = 0 :=
      dv_low K W₁ _ rfl k _ h₁ (by rw [hD₁]; exact hx k _ (by omega))
    obtain ⟨W₂, hs₂, hD₂, h₂⟩ := push_step K n k (a + i - k) (by omega) W₁ hs₁ h₁ hv
      (hac k _ (by omega)) (by omega)
    exact ⟨W₂, hs₂, hD₂.trans hD₁, h₂⟩

theorem exists_prim {n : ℕ} (z : K.tot.Z n) (hz : K.tot.cls z.1 z.2 = 0) :
    ∃ W : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W p q = 0) ∧ K.D W = z.1.1 := by
  have hB : z.1 ∈ K.tot.B n := ((P.cls_surj K.tot n).2.1 _ _).1 hz
  cases n with
  | zero =>
    have h : z.1 = 0 := (Submodule.mem_bot R).1 hB
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [h, map_zero]
    rfl
  | succ m =>
    obtain ⟨u, hu⟩ := hB
    exact ⟨u.1, fun p q h => u.2 p q (by omega), congrArg Subtype.val hu⟩

theorem leadE_eq_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  intro R _ K a j hac z hz
  obtain ⟨W, hs, hD⟩ := exists_prim K z.1 hz
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K _ (D_zero K z.1) j a z.2
  suffices h : leadC K j a z ∈ (colH K a).B j by
    rw [leadE_eq]
    exact ((P.cls_surj (colH K a) j).2.1 _ _).2 h
  cases j with
  | zero =>
    have h1 : z.1.1.1 0 a ∈ (K.col 0).B a := by
      rw [← hD, DCx.D_apply]
      have h2 : K.Dh W 0 a = 0 := rfl
      rw [h2, zero_add, pow_zero, one_smul]
      exact Dv_mem K W 0 a
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, leadC_eq K 0 a z hv]
    exact ((P.cls_surj _ a).2.1 _ hv).2 h1
  | succ i =>
    obtain ⟨W', -, hD', h0⟩ := push K (a + (i + 1)) a i rfl W hs
      (fun p q hp => by rw [hD]; exact z.2 p q hp) hac i le_rfl
    have hD'' : K.D W' = z.1.1.1 := hD'.trans hD
    have hy : K.dv i a (W' i a) = 0 := dv_low K W' _ hD'' i a h0 (z.2 i _ (by omega))
    have hb : (K.col (i + 1)).d a ((colMap K i).f a (W' i a)) = 0 := by
      rw [(colMap K i).comm]
      exact (congrArg _ hy).trans (map_zero _)
    refine ⟨(K.col i).cls _ hy, ?_⟩
    show (colMap K i).mapH a _ = leadC K (i + 1) a z
    rw [P.mapH_cls _ a _ hy hb, leadC_eq K (i + 1) a z hv]
    refine ((P.cls_surj _ a).2.2.1 _ _ hb hv).2 ?_
    have h2 : z.1.1.1 (i + 1) a = K.dh i a (W' i a) + (-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a := by
      rw [← hD'', DCx.D_apply]
      rfl
    have e : (colMap K i).f a (W' i a) - z.1.1.1 (i + 1) a =
        -((-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a) := by
      rw [h2]
      show K.dh i a (W' i a) - _ = _
      abel
    rw [e]
    exact Submodule.neg_mem _ (zsmul_mem (Dv_mem K W' (i + 1) a) _)

end GlobalTheory.CompanionTheory.CechSerre.RowKer
