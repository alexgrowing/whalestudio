import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.ColDefs
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsNonnegDualFnumSubLeOfDemandNearMul
import Development.AutomorphicArithmetic.OrbitLabellings.KvalGeOfNormMfactMulCoeffLe
import Development.AutomorphicArithmetic.OrbitLabellings.NormMfactMulCoeffLeOfB0S

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G UpperTheory.G2 Classical

namespace UpperTheory.OrbitRadiiBounds

open Formalism.IncomingBounds in
private theorem lpF_eq (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) : Formalism.BasicNotions.lpF l d D = Fnum l d D := by
  unfold Formalism.BasicNotions.lpF Fnum maxFlow Formalism.IncomingBounds.gam
  congr 2
  ext y
  simp only [Formalism.BasicNotions.lpFeasible, Set.mem_ofPred_eq, IsFlow, flowVal, oddLevels]
  constructor
  · rintro ⟨xs, h0, hz, hD, rfl⟩
    have hf : ∀ (f : ℕ → ℝ), (∀ i, ¬ Odd i → f i = 0) →
        ∑ i ∈ (Finset.range d).filter Odd, f i = ∑ i ∈ Finset.range d, f i := by
      intro f hf0
      exact Finset.sum_filter_of_ne (fun i _ h => by by_contra ho; exact h (hf0 i ho))
    refine ⟨xs, ⟨h0, fun s => ?_⟩, ?_⟩
    · rw [hf _ (fun i ho => by rw [hz s i (Or.inl ho), mul_zero]),
        hf _ (fun i ho => hz _ i (Or.inl ho))]
      exact hD s
    · apply Finset.sum_congr rfl; intro s _
      exact hf _ (fun i ho => hz s i (Or.inl ho))
  · rintro ⟨x, ⟨h0, hD⟩, rfl⟩
    have e1 : ∀ (f : ℕ → ℝ), ∑ i ∈ Finset.range d, (if Odd i ∧ i < d then f i else 0) =
        ∑ i ∈ (Finset.range d).filter Odd, f i := by
      intro f; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi; by_cases ho : Odd i <;> simp [ho, hi]
    refine ⟨fun s i => if Odd i ∧ i < d then x s i else 0, ?_, ?_, ?_, ?_⟩
    · intro s i; dsimp only; split_ifs <;> simp [h0]
    · intro s i h; dsimp only; rw [if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h; exact h h1; omega
    · intro s
      have h2 : ∀ i, (l : ℝ) ^ i * (if Odd i ∧ i < d then x s i else 0) =
          (if Odd i ∧ i < d then (l : ℝ) ^ i * x s i else 0) := by intro i; split_ifs <;> simp
      simp only [h2]
      rw [e1 (fun i => (l : ℝ) ^ i * x s i), e1 (fun i => x (s - (i : ZMod d)) i)]
      exact hD s
    · apply Finset.sum_congr rfl; intro s _
      exact (e1 (fun i => x s i)).symm

private theorem orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D) (hS : OrbitPlaces.Shape D L X E)
    (p : ℕ) (h5 : 5 ≤ p) (hc : IsResidueClassZero D p) (hh : hP D p ≠ 0) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (r : OrbitPlaces.Pl D) :
    ∃ sig : ZMod (nP D p) → ℝ, (∀ s, 0 ≤ sig s) ∧ Formalism.IncomingBounds.IsDualAll p (nP D p) sig ∧
      (if r ∉ kindA D p then FOrb D (i + 1) p r -
          ((D.R.k : ℝ) - 1) * (∑ s, wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) / (p : ℝ) ^ 3 -
          8 * (∑ s, wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) / p else 0) ≤
        ∑ s, E.size u i (OrbitPlaces.orbMap D p r s) * (Formalism.IncomingBounds.gam p - sig s) := by
  have hs : ¬ IsSg D p := by
    intro h4
    have h3 : D.host.cls p = _ := hc
    have h4' : D.host.cls p = _ := h4
    rw [h4'] at h3; simp at h3
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5
  split_ifs with hr
  · refine ⟨fun _ => 1 / ((p : ℝ) + 1), fun _ => by positivity, ?_, ?_⟩
    · intro s e he
      have h1 : (p : ℝ) ≤ (p : ℝ) ^ e := le_self_pow₀ (by linarith) he.pos.ne'
      have h2 : (p : ℝ) * (1 / ((p : ℝ) + 1)) + 1 / ((p : ℝ) + 1) = 1 := by field_simp
      have h3 : (p : ℝ) * (1 / ((p : ℝ) + 1)) ≤ (p : ℝ) ^ e * (1 / ((p : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      show 1 ≤ (p : ℝ) ^ e * (1 / ((p : ℝ) + 1)) + 1 / ((p : ℝ) + 1)
      linarith
    · refine Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) ?_
      unfold Formalism.IncomingBounds.gam
      rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by nlinarith)]
      nlinarith
  · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
    have h2 : 2 ≤ nP D p := by
      have h0 : nP D p ≠ 0 := NeZero.ne _
      have h1 : nP D p ≠ 1 := by rw [hn]; exact fun h => hh (AddMonoid.addOrderOf_eq_one_iff.1 h)
      omega
    have hk : (0 : ℝ) < (D.R.k : ℝ) - 1 := by
      have h1 := hS.rankA
      have h2 : 0 ≤ Real.logb 5 (L.sc.a ^ 2) := Real.logb_nonneg (by norm_num) (by nlinarith [hS.xa.2])
      linarith
    have hnt : ∀ s, ¬ IsTopPl D (OrbitPlaces.orbMap D p r s) := by
      intro s ht
      apply hr
      rw [← OrbitPlaces.memA_orb p r s]
      unfold kindA
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs, ht.1⟩
    obtain ⟨sig, h0, hd, hb⟩ := UpperTheory.exists_nonneg_dual_fnum_sub_le_of_demand_near_mul p (nP D p) h5 h2 ((D.R.k : ℝ) - 1)
      (fun s => wPl D (i + 1) (OrbitPlaces.orbMap D p r s)) (fun s => E.size u i (OrbitPlaces.orbMap D p r s)) hk
      (fun s => (hS.wpos i hi _).le)
      (fun s => by obtain ⟨a, b⟩ := hS.low u i hi _ (hnt s); constructor <;> linarith)
    refine ⟨sig, h0, hd, ?_⟩
    rw [← lpF_eq] at hb
    exact hb

private theorem radii (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D) (hS : OrbitPlaces.Shape D L X E)
    (p : ℕ) (h5 : 5 ≤ p) (hc : IsResidueClassZero D p) (hh : hP D p ≠ 0) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) :
    ∃ sig : OrbitPlaces.Pl D → ℝ, IsRadii p (posPl D p) sig ∧
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 -
        8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p ≤ ∑ z, E.size u i z * (Formalism.IncomingBounds.gam p - sig z) := by
  choose σ h0 hd hb using orbit D L X E hS p h5 hc hh u i hi
  have hR := OrbitPlaces.isReps_repsPl X p
  set R := OrbitPlaces.repsPl X p
  have hpos : 0 < nP D p := Nat.pos_of_ne_zero (NeZero.ne _)
  have hex : ∀ z, ∃ r ∈ R, ∃ s, OrbitPlaces.orbMap D p r s = z := by
    intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    exact ⟨r, hr, (e : ZMod (nP D p)), by unfold OrbitPlaces.orbMap; rw [ZMod.val_natCast, posPl_mod, he]⟩
  choose rr hrr ss hss using hex
  have key : ∀ r ∈ R, ∀ s, σ (rr (OrbitPlaces.orbMap D p r s)) (ss (OrbitPlaces.orbMap D p r s)) = σ r s := by
    intro r hr s
    have h := hss (OrbitPlaces.orbMap D p r s)
    have h1 : rr (OrbitPlaces.orbMap D p r s) = r :=
      (hR (OrbitPlaces.orbMap D p r s)).unique ⟨hrr _, _, h⟩ ⟨hr, s.val, rfl⟩
    rw [h1] at h ⊢
    rw [ZMod.val_injective _ (posPl_inj D p r _ _ (ZMod.val_lt _) (ZMod.val_lt _) h)]
  refine ⟨fun z => σ (rr z) (ss z), ⟨fun z => h0 _ _, fun z e he => ?_⟩, ?_⟩
  · have e1 : posPl D p z e = OrbitPlaces.orbMap D p (rr z) (ss z + (e : ZMod (nP D p))) := by
      conv_lhs => rw [← hss z]
      unfold OrbitPlaces.orbMap
      rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p _ _ (e % nP D p), posPl_mod, posPl_add]
    show 1 ≤ (p : ℝ) ^ e * σ (rr z) (ss z) + σ (rr (posPl D p z e)) (ss (posPl D p z e))
    rw [e1, key _ (hrr z)]
    exact hd _ _ e he
  · have hn : (nP D p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    have eF : (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) =
        ∑ r ∈ R.filter (fun r => r ∉ kindA D p), FOrb D (i + 1) p r := by
      rw [← OrbitPlaces.sum_orbBC p _ R hR, Finset.sum_div]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hc : ∀ s : ZMod (nP D p), FOrb D (i + 1) p (OrbitPlaces.orbMap D p r s) = FOrb D (i + 1) p r :=
        fun s => FOrb_step D (i + 1) p r s.val
      rw [Finset.sum_congr rfl (fun s _ => hc s), Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        mul_div_cancel_left₀ _ hn]
    have hsum := Finset.sum_le_sum (fun r (_ : r ∈ R) => hb r)
    rw [← Finset.sum_filter] at hsum
    rw [eF, ← OrbitPlaces.sum_orbBC p (wPl D (i + 1)) R hR, ← OrbitPlaces.sum_orb p _ R hR]
    refine le_trans (le_of_eq ?_) (le_trans hsum (le_of_eq ?_))
    · rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.mul_sum,
        ← Finset.mul_sum]
    · exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s _ => by simp only [key r hr s]

private theorem NN_le (D : D7) (i : ℕ) (hi : i < D.R.m) : (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ Nm D ^ 2 := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m := Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have h1' : (D.R.N i : ℝ) ≤ Nm D := by unfold Nm; exact_mod_cast h1
  have h2' : (D.R.N (i + 1) : ℝ) ≤ Nm D := by unfold Nm; exact_mod_cast h2
  rw [sq]
  exact mul_le_mul h1' h2' (by positivity) (le_trans (by positivity) h1')

end UpperTheory.OrbitRadiiBounds

open UpperTheory.OrbitRadiiBounds in
theorem UpperTheory.kvalGe_theta_of_shape :
    ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (E : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X E →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → IsResidueClassZero D p → hP D p ≠ 0 → ∀ [NeZero (nP D p)], (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m,
    ∀ Th : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[p], HasThetaProductForm p (nP D p) (posPl D p) Th →
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th
      ((∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 - 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p -
        3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a) := by
  intro D L X E hS p hp h5 hc hh _ hpX u i hi Th hTh
  obtain ⟨sig, hsig, hb⟩ := radii D L X E hS p h5 hc hh u i hi
  refine UpperTheory.kvalGe_of_norm_mfact_mul_coeff_le p _ _ _ _ _ _ fun κ hκ => ?_
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hnorm : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hA : ∀ v, (κ v : ℝ) ≤ L.sc.a ^ 2 := by
    rintro ⟨t, ab⟩
    refine le_trans ?_ (hS.sizeA u i hi t)
    unfold OrbitPlaces.Ent.size
    rw [← hκ t]
    exact_mod_cast Finset.single_le_sum (f := fun ab => κ (t, ab)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ab)
  have h := UpperTheory.norm_mfact_mul_coeff_le_of_B0S ℂ_[p] p (nP D p) hp.out hodd (by rw [hnorm]; exact inv_lt_one_of_one_lt₀ hp1)
    _ _ (posPl D p) ⟨posPl_zero D p, posPl_add D p, posPl_period D p⟩ Th hTh sig hsig κ (L.sc.a ^ 2)
    (by nlinarith [hS.xa.2]) hA
  refine h.trans ?_
  rw [hnorm, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le (neg_le_neg ?_)
  have e1 : (∑ v : OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1)), (κ v : ℝ) * (Formalism.IncomingBounds.gam p - sig v.1)) =
      ∑ z, E.size u i z * (Formalism.IncomingBounds.gam p - sig z) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold OrbitPlaces.Ent.size
    rw [← hκ z, Nat.cast_sum, Finset.sum_mul]
  have e2 : (Fintype.card (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) : ℝ) =
      (D.R.f : ℝ) * ((D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ)) := by
    rw [Fintype.card_prod, Fintype.card_prod (Fin _), Fintype.card_fin, Fintype.card_fin, Nat.cast_mul, Nat.cast_mul,
      OrbitPlaces.card_Pl]
  have hpa : (p : ℝ) ≤ L.sc.a := le_trans hpX hS.xa.1
  have hLg : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]; exact hpa
  have hlog2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    unfold Real.logb; rw [Real.log_pow]; push_cast; ring
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hB : (D.R.f : ℝ) * ((D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ)) * (2 * Real.logb p L.sc.a + 1) ≤
      ((D.R.f : ℝ) * Nm D ^ 2) * (3 * Real.logb p L.sc.a) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (NN_le D i hi) hf) (by linarith) (by linarith) (by positivity)
  rw [e1, e2, hlog2]
  linarith
