import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Perturb

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem nv_irr {w : O} (hw : Irreducible w) : dvrOrderNat w = 1 := by
  unfold dvrOrderNat
  rw [IsDiscreteValuationRing.addVal_uniformizer hw]
  rfl

theorem ramE_two {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) : ramE p O = 2 := by
  unfold ramE
  rw [← h2, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hw]
  rfl

theorem vLEO_iff {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {x : O} (hx : x ≠ 0) (D : ℝ) :
    vLEO p x D ↔ (dvrOrderNat x : ℝ) / 2 ≤ D := by
  have h1 : ordW (algebraMap O (KK O) x) = (((dvrOrderNat x : ℤ) - (dvrOrderNat (1 : O) : ℤ) : ℤ) : WithTop ℤ) :=
    ord_eq_order_sub_of_fraction _ x 1 hx one_ne_zero (by rw [map_one, mul_one])
  have h0 : dvrOrderNat (1 : O) = 0 := by
    unfold dvrOrderNat
    rw [IsDiscreteValuationRing.addVal_one]
    rfl
  have hv : vO p x = (((dvrOrderNat x : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    unfold vO vK
    rw [h1, h0, ramE_two hw h2]
    simp
  unfold vLEO
  rw [hv]
  constructor
  · rintro ⟨q, hq, hqD⟩
    have hq' : q = (dvrOrderNat x : ℚ) / 2 := (WithTop.coe_inj.mp hq).symm
    subst hq'
    push_cast at hqD
    exact hqD
  · intro h
    exact ⟨_, rfl, by push_cast; exact h⟩

theorem eq_unit_pow {w : O} (hw : Irreducible w) {x : O} (hx : x ≠ 0) : ∃ u : Oˣ, x = (u : O) * w ^ dvrOrderNat x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hw
  refine ⟨u, ?_⟩
  have hn : dvrOrderNat ((u : O) * w ^ n) = n := by
    unfold dvrOrderNat
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hw, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
    simp
  rw [hn]

theorem isUnit_one_add {n : ℕ} {w : O} (hw : Irreducible w) (N : Matrix (Fin n) (Fin n) O) :
    IsUnit (1 + w • N : Matrix (Fin n) (Fin n) O) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hw0 : IsLocalRing.residue O w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hw.1
  have hmap : (IsLocalRing.residue O).mapMatrix (1 + w • N) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hw0]
    · simp [hij, hw0]
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hmap, Matrix.det_one]
  exact one_ne_zero

theorem factors_of_perturb {Kf V V' : Type} [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module O V]
    [AddCommGroup V'] [Module O V'] {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O))
    (be : V → V' → Kf) (A : Submodule O V) (A' : Submodule O V') (n c : ℕ) (D : ℝ) (hD : 4 * D < (c : ℝ))
    (x : Fin n → V) (y : Fin n → V') (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (δ : Fin n → O)
    (hδ : ∀ i, δ i ≠ 0 ∧ vLEO p (δ i) D) (ν : Fin n → Fin n → O)
    (hT : ∀ i j, be (x i) (y j) = algebraMap O Kf ((if i = j then δ i else 0) + w ^ c * ν i j)) :
    FactorsLE p be A A' n D := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inl hn
  right
  refine ⟨x, y, hx, hy, ?_⟩
  choose u hu using fun i => eq_unit_pow hw (hδ i).1
  obtain ⟨k, hkdef⟩ : ∃ k : Fin n → ℕ, ∀ i, k i = dvrOrderNat (δ i) := ⟨_, fun _ => rfl⟩
  have hu' : ∀ i, δ i = (u i : O) * w ^ k i := fun i => by rw [hkdef]; exact hu i
  have hk : ∀ i, k i < c := by
    intro i
    have h := (vLEO_iff hw h2 (hδ i).1 D).mp (hδ i).2
    rw [← hkdef] at h
    have h0 : (0 : ℝ) ≤ (k i : ℝ) := Nat.cast_nonneg _
    have : (k i : ℝ) < c := by linarith
    exact_mod_cast this
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ k ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin n) (Fin n) O,
      ∀ i j, N i j = (((u i)⁻¹ : Oˣ) : O) * w ^ (c - k i - 1) * ν i j :=
    ⟨Matrix.of fun i j => (((u i)⁻¹ : Oˣ) : O) * w ^ (c - k i - 1) * ν i j, fun _ _ => rfl⟩
  obtain ⟨zl, hzdef⟩ : ∃ zl : Fin n → O, ∀ l, zl l = (u i0 : O) * (((u l)⁻¹ : Oˣ) : O) * w ^ (k i0 - k l) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) O, (1 + w • N) * Q = 1 := by
    obtain ⟨U, hU⟩ := isUnit_one_add hw N
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  have hzl : ∀ l, δ l * zl l = δ i0 := by
    intro l
    have hle : k l ≤ k i0 := hi0 l (Finset.mem_univ _)
    rw [hu' l, hu' i0, hzdef]
    have hb : w ^ k i0 = w ^ k l * w ^ (k i0 - k l) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hb]
    have hu1 : (u l : O) * (((u l)⁻¹ : Oˣ) : O) = 1 := Units.mul_inv (u l)
    linear_combination (u i0 : O) * w ^ k l * w ^ (k i0 - k l) * hu1
  have hD1 : ∀ i j, δ i * (w * N i j) = w ^ c * ν i j := by
    intro i j
    have hc : w ^ c = w ^ k i * w * w ^ (c - k i - 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      have := hk i
      omega
    have hu1 : (u i : O) * (((u i)⁻¹ : Oˣ) : O) = 1 := Units.mul_inv (u i)
    rw [hNdef, hu' i, hc]
    linear_combination (w ^ k i * w * w ^ (c - k i - 1) * ν i j) * hu1
  have hB : ∀ i l, (if i = l then δ i else 0) + w ^ c * ν i l = δ i * (1 + w • N) i l := by
    intro i l
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, hD1 i l, Matrix.one_apply, mul_ite, mul_one,
      mul_zero]
  refine ⟨δ i0, Q * Matrix.diagonal zl, (hδ i0).1, (hδ i0).2, fun i j => ?_⟩
  have hBM : ∑ l, δ i * (1 + w • N) i l * (Q * Matrix.diagonal zl) l j = if i = j then δ i0 else 0 := by
    have hmul : ∑ l, (1 + w • N) i l * (Q * Matrix.diagonal zl) l j =
        ((1 + w • N) * (Q * Matrix.diagonal zl)) i j := by
      rw [Matrix.mul_apply]
    simp_rw [mul_assoc (δ i)]
    rw [← Finset.mul_sum, hmul, ← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.diagonal_apply]
    split_ifs with hij
    · exact hzl i
    · exact mul_zero _
  calc ∑ l, be (x i) (y l) * algebraMap O Kf ((Q * Matrix.diagonal zl) l j)
      = algebraMap O Kf (∑ l, δ i * (1 + w • N) i l * (Q * Matrix.diagonal zl) l j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hT, hB]
        simp only [map_mul]
    _ = if i = j then algebraMap O Kf (δ i0) else 0 := by
        rw [hBM]
        split_ifs <;> simp

end Perturb

theorem liftAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ}
    (h : LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc) : LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC Dj g hD0 hBD hc e he
  obtain ⟨F, G, δ, hF, hG, hδ, hT⟩ := h X W Qq O Kf ι σ jO w hS hH hC Dj g hD0 hBD hc e he
  choose ν hν using hT
  let eI : Fin (∏ j, g j) ≃ (∀ j, Fin (g j)) := (Fintype.equivFinOfCardEq (by simp)).symm
  refine factors_of_perturb hS.2.1 hS.1.w_sq _ _ _ _ X.c _ hc (fun a => F (eI a)) (fun a => G (eI a))
    (fun a => hF _) (fun a => hG _) (fun a => δ (eI a)) (fun a => hδ _) (fun a b => ν (eI a) (eI b)) ?_
  intro a b
  rw [hν]
  simp only [Equiv.apply_eq_iff_eq]

theorem restLift_of (h : RestLiftVec) : RestLift :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ ⟨Ct0, h0, hCt⟩ => ⟨Ct0, h0, fun Ct h' => liftAt_of (hCt Ct h')⟩) h

end Formalism.MainNotions.ColumnSystems.Pf
