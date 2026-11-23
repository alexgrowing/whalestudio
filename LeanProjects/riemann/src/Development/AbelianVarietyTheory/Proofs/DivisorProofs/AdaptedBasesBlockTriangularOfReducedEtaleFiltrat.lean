import Mathlib
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEntryOfSemilinearModSubspaceStatement

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame PowerSeries Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachBlock

theorem finrank_sup_span_singleton_of_not_mem : ∀ (K : Type) [Field K] (n : ℕ) (W : Submodule K (Fin n → K)) (x : Fin n → K), x ∉ W → Module.finrank K ↥(W ⊔ Submodule.span K {x}) = Module.finrank K W + 1 := by
  intro K _ n W x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  have hinf : W ⊓ Submodule.span K {x} = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzW, hzs⟩ := Submodule.mem_inf.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hzs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using W.smul_mem c⁻¹ hzW) hx
  have := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {x})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0] at this
  exact this

theorem laurent_eq_unit_mul_X_zpow : ∀ (F : Type) [Field F] (x : LaurentSeries F), x ≠ 0 → ∃ (w : (PowerSeries F)ˣ) (k : ℤ), x = ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
  intro F _ x hx
  have hsingle : ∀ k : ℤ, (HahnSeries.single k (1 : F) : LaurentSeries F) = ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k := by
    intro k
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · rw [zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      try simp
    · rw [zpow_neg, zpow_natCast, ← map_pow, HahnSeries.ofPowerSeries_X_pow]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [HahnSeries.single_mul_single]
      simp
  have hunit : IsUnit x.powerSeriesPart := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      LaurentSeries.powerSeriesPart_coeff, Nat.cast_zero, add_zero]
    exact isUnit_iff_ne_zero.2 (fun h => hx (HahnSeries.coeff_order_eq_zero.1 h))
  refine ⟨hunit.unit, x.order, ?_⟩
  rw [IsUnit.unit_spec, ← hsingle, mul_comm]
  exact (LaurentSeries.single_order_mul_powerSeriesPart x).symm

theorem sub_coord_smul_col_mem : ∀ (F : Type) [Field F] (n : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (z : Fin n → PowerSeries F) (p : Fin n), (∀ a : Fin n, a ≠ p → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) a ≠ 0 → (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) ∈ U) → (fun c => ((z c : PowerSeries F) : LaurentSeries F)) - (((((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec z) p : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c p : PowerSeries F) : LaurentSeries F)) ∈ U := by
  intro F _ n U g z p h
  set v := (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F))).mulVec z with hv
  have hz : z = (g : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hsum : (fun c => ((z c : PowerSeries F) : LaurentSeries F)) =
      ∑ a, ((v a : PowerSeries F) : LaurentSeries F) • (fun c => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) c a : PowerSeries F) : LaurentSeries F)) := by
    funext c
    conv_lhs => rw [hz]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p), add_sub_cancel_left]
  refine U.sum_mem fun a ha => ?_
  by_cases h0 : v a = 0
  · simp [h0]
  · exact U.smul_mem _ (h a (Finset.ne_of_mem_erase ha) h0)

theorem adapted_bases_of_redFilt : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  intro ι σ l n t F _ un P D Pψ Dψ hl hne hR
  classical
  obtain ⟨R, V, rs, e, m, hrs, hV, hdim, hphi, hgam, hline, hrelP, hrelG⟩ := hR
  obtain ⟨i0⟩ := hne
  let K := LaurentSeries F
  let d : Fin (R + 1) → ℕ := fun k => Module.finrank K (V i0 k)
  have hdi : ∀ i k, Module.finrank K (V i k) = d k := fun i k => hdim k i i0
  have hdmono : Monotone d := fun a b hab => Submodule.finrank_mono ((hV i0).2.2 hab)
  have hdlast : d (Fin.last R) = n := by
    show Module.finrank K (V i0 (Fin.last R)) = n
    rw [(hV i0).2.1, finrank_top, Module.finrank_fin_fun]
  have hdle : ∀ k, d k ≤ n := fun k => hdlast ▸ hdmono (Fin.le_last k)

  choose g hg using fun i => GlobalTheory.T.exists_unit_matrix_adapted_to_flag F n R (V i) (hV i).2.2
  have hg' : ∀ i k (j : Fin n), (j : ℕ) < d k → lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a j) ∈ V i k :=
    fun i k j hj => hg i k j (by rw [hdi]; exact hj)

  have hex : ∀ j : Fin n, ∃ k, ∃ h : k < R + 1, (j : ℕ) < d ⟨k, h⟩ :=
    fun j => ⟨R, Nat.lt_succ_self R, by have := hdlast; simp only [Fin.last] at this; rw [this]; exact j.2⟩
  let b : Fin n → ℕ := fun j => Nat.find (hex j)
  have hbR : ∀ j, b j < R + 1 := fun j => (Nat.find_spec (hex j)).1
  have hb : ∀ (j : Fin n) (k : Fin (R + 1)), (j : ℕ) < d k ↔ b j ≤ (k : ℕ) := by
    intro j k
    constructor
    · intro h
      exact Nat.find_min' (hex j) ⟨k.2, h⟩
    · intro h
      obtain ⟨h1, h2⟩ := Nat.find_spec (hex j)
      exact lt_of_lt_of_le h2 (hdmono (show (⟨b j, h1⟩ : Fin (R + 1)) ≤ k from h))

  have hentP : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi, phiV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hentG : ∀ i (a j : Fin n), Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) a j =
      (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
        (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c j)) a := by
    intro i a j
    simp only [Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam, gamV, Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hbtP : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentP]
    have hmem := hphi i ⟨b j, hbR j⟩ _ (hg' (σ i) ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))
  have hbtG : ∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b := by
    intro i a j hlt
    rw [hentG]
    have hmem := hgam i ⟨b j, hbR j⟩ _ (hg' i ⟨b j, hbR j⟩ j ((hb j _).2 le_rfl))
    refine GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i ⟨b j, hbR j⟩) (g i) (fun j' hj' => hg i _ j' hj') _ hmem a ?_
    rw [hdi]
    exact Nat.le_of_not_lt (fun h => absurd ((hb a _).1 h) (Nat.not_le.2 hlt))

  have hstep : ∀ s, d (rs s).succ = d (rs s).castSucc + 1 := by
    intro s
    show Module.finrank K (V i0 (rs s).succ) = Module.finrank K (V i0 (rs s).castSucc) + 1
    rw [(hline i0 s).2]
    exact finrank_sup_span_singleton_of_not_mem K n _ _ (hline i0 s).1
  let pos : Fin t → Fin n := fun s => ⟨d (rs s).castSucc, by have := hstep s; have := hdle (rs s).succ; omega⟩
  have hpos_lt : ∀ s, (pos s : ℕ) < d (rs s).succ := fun s => by simp only [pos]; rw [hstep]; omega
  have hpos_nlt : ∀ s, ¬ (pos s : ℕ) < d (rs s).castSucc := fun s => by simp [pos]
  have hsing : ∀ s j, b j = b (pos s) → j = pos s := by
    intro s j h
    have h1 : (j : ℕ) < d (rs s).succ := (hb j _).2 (h ▸ (hb (pos s) _).1 (hpos_lt s))
    have h2 : ¬ (j : ℕ) < d (rs s).castSucc := fun hj => hpos_nlt s ((hb (pos s) _).2 (h ▸ (hb j _).1 hj))
    rw [hstep] at h1
    ext
    simp only [pos]
    omega
  have hbpos : ∀ s, b (pos s) = (rs s : ℕ) + 1 := by
    intro s
    have h1 := (hb (pos s) _).1 (hpos_lt s)
    have h2 : ¬ b (pos s) ≤ ((rs s).castSucc : ℕ) := fun h => hpos_nlt s ((hb (pos s) _).2 h)
    simp only [Fin.val_succ, Fin.coe_castSucc] at h1 h2
    omega
  have hinj : Function.Injective pos := by
    intro s s' h
    have h' : b (pos s) = b (pos s') := by rw [h]
    rw [hbpos, hbpos] at h'
    exact hrs (Fin.ext (by omega))

  have hcoef : ∀ i s, ∃ c : K, c ≠ 0 ∧ lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) - c • lau (e i s) ∈
      V i (rs s).castSucc := by
    intro i s
    have hmem := hg' i (rs s).succ (pos s) (hpos_lt s)
    rw [(hline i s).2, Submodule.mem_sup] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      rw [zero_smul, add_zero] at hyz
      have h0 := GlobalTheory.T.laurentSeries_adapted_basis_coords_vanish_beyond_finrank F n (V i (rs s).castSucc) (g i) (fun j' hj' => hg i _ j' hj') _ (hyz ▸ hy) (pos s)
        (by rw [hdi] <;> exact Nat.le_of_not_lt (hpos_nlt s))
      have h1 : (((g i)⁻¹ : (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) F⟦X⟧).mulVec
          (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) (pos s) = 1 := by
        have := congrFun (congrFun (Units.inv_mul (g i)) (pos s)) (pos s)
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
      rw [h1] at h0
      exact one_ne_zero h0
    · rw [← hyz, add_sub_cancel_right]
      exact hy
  choose c hc0 hc using hcoef
  choose w k hwk using fun i s => laurent_eq_unit_mul_X_zpow F (c i s) (hc0 i s)
  have hc' : ∀ i s, lau (fun a => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) a (pos s)) -
      (((w i s : F⟦X⟧) : K) * ((X : F⟦X⟧) : K) ^ k i s) • lau (e i s) ∈ V i (rs s).castSucc :=
    fun i s => hwk i s ▸ hc i s
  have hcoe : ∀ p : F⟦X⟧, p ≠ 0 → ((p : F⟦X⟧) : K) ≠ 0 := fun p hp h =>
    hp (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  have hX : ((X : F⟦X⟧) : K) ≠ 0 := hcoe _ X_ne_zero
  have hlow : ∀ s (a : Fin n), a ≠ pos s → ¬ b (pos s) < b a → (a : ℕ) < d (rs s).castSucc := by
    intro s a ha hlt
    refine (hb a _).2 ?_
    have h1 : b a ≠ b (pos s) := fun h => ha (hsing s a h)
    have h2 := hbpos s
    simp only [Fin.coe_castSucc]
    omega

  let θF : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow (R := F) hl.ne')).toRingHom
  have hθF : ∀ y, θF y = frob0 l y := fun y => by simp [θF, frob0, PowerSeries.coe_substAlgHom]
  have hθFX : θF X = X ^ l := by
    rw [hθF, frob0, PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hl.ne')]
  have hrelF : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * (k (σ i) s + m (σ i) s)) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdP := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (phiV l (P i) (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentP]; exact hbtP i h))))
    rw [← hentP] at hdP
    have hθFe : ⇑θF = frob0 l := funext hθF
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θF (P i) (V (σ i) (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g (σ i) : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e (σ i) s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w (σ i) s) (w i s) (k (σ i) s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s))
      (((X : F⟦X⟧) : K) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i : F⟦X⟧) : K))
      (by rw [hθFX]; exact hcoe _ (pow_ne_zero _ X_ne_zero))
      (fun y hy => by rw [hθFe]; exact hphi i _ y hy) (hc' (σ i) s) (hc' i s) (hline i s).1
      (by rw [hθFe]; exact hdP) (by rw [hθFe]; exact hrelP i s)
    rw [hθFX, hθF] at key
    simp only [map_pow] at key
    rw [mul_add, zpow_add₀ hX, zpow_add₀ hX, zpow_mul, zpow_natCast]
    linear_combination key

  have hgs : (gamSer 0 un : F⟦X⟧) ≠ 0 := by
    refine mul_ne_zero X_ne_zero (fun h => ?_)
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  have hgc : MvPowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0 := by
    show PowerSeries.constantCoeff (gamSer 0 un : F⟦X⟧) = 0
    simp [gamSer]
  let θG : F⟦X⟧ →+* F⟦X⟧ := (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hgc)).toRingHom
  have hθG : ∀ y, θG y = gam0 0 un y := fun y => by simp [θG, gam0, PowerSeries.coe_substAlgHom]
  have hθGX : θG X = gamSer 0 un := by
    rw [hθG, gam0, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hgc)]
  have hrelΓ : ∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ (k i s + m i s) := by
    intro i s
    have hdG := sub_coord_smul_col_mem F n (V i (rs s).castSucc) (g i) (gamV un (D i) (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s))) (pos s)
      (fun a ha hne => hg' i _ a (hlow s a ha (fun h => hne (by rw [← hentG]; exact hbtG i h))))
    rw [← hentG] at hdG
    have hθGe : ⇑θG = gam0 0 un := funext hθG
    have key := GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt F n θG (1 + (X : F⟦X⟧) • D i) (V i (rs s).castSucc) (V i (rs s).castSucc)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (fun c => (g i : Matrix (Fin n) (Fin n) F⟦X⟧) c (pos s)) (e i s)
      (w i s) (w i s) (k i s) (k i s) (m i s) (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s))
      (((gamSer 0 un : F⟦X⟧) : K) ^ m i s * ((1 + X * Dψ s i : F⟦X⟧) : K))
      (by rw [hθGX]; exact hcoe _ hgs)
      (fun y hy => by rw [hθGe]; exact hgam i _ y hy) (hc' i s) (hc' i s) (hline i s).1
      (by rw [hθGe]; exact hdG) (by rw [hθGe]; exact hrelG i s)
    rw [hθGX, hθG] at key
    rw [zpow_add₀ (hcoe _ hgs), zpow_add₀ hX]
    linear_combination key
  exact ⟨g, b, pos, w, fun i s => k i s + m i s, ⟨hinj, hsing⟩, hbtP, hbtG, hrelF, hrelΓ⟩

end GlobalTheory.WachBlock

end
