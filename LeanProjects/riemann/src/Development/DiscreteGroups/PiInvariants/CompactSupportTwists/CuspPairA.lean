import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem abs_add_le_abs_add_abs (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem lAbs_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem lAbs_rat (γ : GL (Fin n) E) : logAbs (ratGL E n γ).val.det = 0 := by
  have h : (ratGL E n γ).val.det = algebraMap E (Ad E) γ.val.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (D1.logAbsBasic E).2.2 _ (Matrix.isUnits_det_units γ).ne_zero

theorem lAbs_one : logAbs (1 : GA E n).val.det = 0 := by
  have h := lAbs_mul (E := E) (n := n) 1 1
  rw [mul_one] at h
  linarith

theorem lAbs_pow (k : GA E n) (m : ℕ) : logAbs (k ^ m).val.det = m * logAbs k.val.det := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact lAbs_one
  | succ m ih => rw [pow_succ, lAbs_mul, ih]; push_cast; ring

theorem eq_zero_of_nat_mul_le {a C : ℝ} (h : ∀ m : ℕ, (m : ℝ) * |a| ≤ C) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  obtain ⟨m, hm⟩ := exists_nat_gt (C / |a|)
  have h1 := h m
  have h2 : C / |a| * |a| < m * |a| := mul_lt_mul_of_pos_right hm hpos
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

theorem lAbs_maxCompact {k : GA E n} (hk : k ∈ maxCompact (K := E) (n := n)) : logAbs k.val.det = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_maxCompact (K := E) (n := n)).exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  refine eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (k ^ m) (pow_mem hk m)
  rw [Real.norm_eq_abs, lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h

theorem lAbs_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    logAbs ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = Module.finrank ℚ E * Real.log ρ := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_congr hρ (Real.exp_pos (Real.log ρ)) (Real.exp_log hρ).symm,
    PositivityTheory.Rg.BcB.E1.posIdele_val, PositivityTheory.Rg.BcB.E1.logAbs_pA]

theorem lAbs_prod (s : Finset (Fin n)) (u : Fin n → (Ad E)ˣ) :
    logAbs (∏ i ∈ s, (u i : Ad E)) = ∑ i ∈ s, logAbs (u i : Ad E) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty]
    have h := (D1.logAbsBasic E).2.2 (1 : E) one_ne_zero
    rwa [map_one] at h
  · intro a s ha ih
    have hu : IsUnit (∏ i ∈ s, (u i : Ad E)) := by rw [← Units.coe_prod]; exact Units.isUnit _
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (D1.logAbsBasic E).2.1 _ _ (u a).isUnit hu, ih]

theorem lAbs_diag (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    logAbs (diagUnits n (fun i => posIdele (K := E) (r i) (hr i))).val.det =
      Module.finrank ℚ E * ∑ i, Real.log (r i) := by
  rw [coe_diagUnits, Matrix.det_diagonal]
  refine (lAbs_prod Finset.univ fun i => (posIdele (K := E) (r i) (hr i) : (Ad E)ˣ)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => lAbs_posIdele (r i) (hr i)

theorem sum_sr (ℓ : Fin n → ℝ) (hn : 0 < n) :
    ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r = ℓ ⟨0, hn⟩ - ℓ ⟨n - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : PositivityTheory.Rg.Rs.An.sr ℓ 0 = 0 := by simp [PositivityTheory.Rg.Rs.An.sr]
  rw [h0, add_zero]
  have h1 : ∀ k ∈ Finset.range m, PositivityTheory.Rg.Rs.An.sr ℓ (k + 1) = ext0 ℓ k - ext0 ℓ (k + 1) := fun k hk => by
    rw [Finset.mem_range] at hk
    rw [sr_eq ℓ (by omega) (by omega), Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub']
  rw [ext0, ext0, dif_pos (by omega), dif_pos (by omega)]
  rfl

theorem coord_bound (ℓ : Fin n → ℝ) (hn : 0 < n) (t₀ S : ℝ) (ht : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr ℓ r)
    (hS : |∑ i, ℓ i| ≤ S) (i : Fin n) :
    |ℓ i| ≤ S + 2 * (∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀) := by
  have hc0 : n - 1 < n := by omega
  set c := ℓ ⟨n - 1, hc0⟩ with hcdef
  set x' : Fin n → ℝ := fun j => ℓ j - c with hx'
  have hsr : ∀ r, PositivityTheory.Rg.Rs.An.sr x' r = PositivityTheory.Rg.Rs.An.sr ℓ r := fun r => by
    unfold PositivityTheory.Rg.Rs.An.sr; split_ifs <;> simp [hx']
  have hx'' : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr x' r := fun r => (hsr r).symm ▸ ht r
  have hlast : ∀ j : Fin n, (j : ℕ) + 1 = n → x' j = 0 := fun j hj => by
    have hj' : j = ⟨n - 1, hc0⟩ := Fin.ext (by simp only; omega)
    simp only [hx', hcdef, hj', sub_self]
  have hS' : ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr x' r = ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r :=
    Finset.sum_congr rfl fun r _ => hsr r
  set B := ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀ with hB
  have hB0 : 0 ≤ B := bound_nonneg ℓ t₀ ht
  have hb : ∀ j, |ℓ j - c| ≤ B := fun j => by
    have h := abs_le_bound x' t₀ hx'' hlast j
    rw [hS'] at h
    exact h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hS
  have e : (n : ℝ) * c = ∑ j, ℓ j - ∑ j, (ℓ j - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h1 : |∑ j, (ℓ j - c)| ≤ n * B := by
    calc _ ≤ ∑ j, |ℓ j - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hb j
      _ = n * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : |(n : ℝ) * c| ≤ S + n * B := by
    rw [e]
    exact (abs_sub_le_abs_add_abs _ _).trans (add_le_add hS h1)
  rw [abs_mul, abs_of_pos hnpos] at h2
  have h3 : (n : ℝ) * |c| ≤ n * (S + B) := by nlinarith [mul_nonneg (sub_nonneg.2 hn1) hS0]
  have hc : |c| ≤ S + B := le_of_mul_le_mul_left h3 hnpos
  calc |ℓ i| = |(ℓ i - c) + c| := by rw [sub_add_cancel]
    _ ≤ |ℓ i - c| + |c| := abs_add_le_abs_add_abs _ _
    _ ≤ B + (S + B) := add_le_add (hb i) hc
    _ = S + 2 * B := by ring

end DiscreteGroups.T1.G.CP

end
