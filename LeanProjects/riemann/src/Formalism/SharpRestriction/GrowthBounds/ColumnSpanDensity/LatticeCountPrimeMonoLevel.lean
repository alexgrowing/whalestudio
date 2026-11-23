import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem vLEO_mono {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {z : O} {D D' : ℝ}
    (h : D ≤ D') (hz : vLEO p z D) : vLEO p z D' := by
  obtain ⟨q, hq, hle⟩ := hz
  exact ⟨q, hq, hle.trans h⟩

theorem FactorsLE_mono {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A B : Submodule O V} {A' B' : Submodule O V'} {n : ℕ} {D D' : ℝ} (hA : A ≤ B) (hA' : A' ≤ B') (hD : D ≤ D')
    (h : FactorsLE p be A A' n D) : FactorsLE p be B B' n D' := by
  rcases h with h | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, y, fun i => hA (hx i), fun i => hA' (hy i), z, M, hz, vLEO_mono hD hv, hM⟩

theorem RhoGE_mono {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] {p : ℕ} {be : V → V' → Kf}
    {A B : Submodule O V} {A' B' : Submodule O V'} {D D' X X' : ℝ} (hA : A ≤ B) (hA' : A' ≤ B') (hD : D ≤ D')
    (hX : X' ≤ X) (h : RhoGE p be A A' D X) : RhoGE p be B B' D' X' := by
  obtain ⟨n, hn, hf⟩ := h
  exact ⟨n, hX.trans hn, FactorsLE_mono hA hA' hD hf⟩

theorem scale_neg_mono {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (w : O) (hw : algebraMap O Kf w ≠ 0) {t t' : ℕ} (h : t ≤ t')
    (M : Submodule O X) :
    scale (algebraMap O Kf w ^ (-(t : ℤ))) M ≤ scale (algebraMap O Kf w ^ (-(t' : ℤ))) M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨(w ^ (t' - t)) • y, M.smul_mem _ hy, ?_⟩
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
  rw [← algebraMap_smul Kf (w ^ (t' - t)) y, smul_smul, map_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ hw]
  congr 1
  push_cast [Nat.cast_sub h]
  ring

theorem RS.w_ne {p n' : ℕ} (R : RS p n') : algebraMap R.O R.Kf R.w ≠ 0 := by
  haveI := R.std.1.frac_O
  intro h
  exact R.std.2.1.ne_zero (IsFractionRing.injective R.O R.Kf (h.trans (map_zero _).symm))

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem lattice_count_mono_level {t t' : ℕ} (h : t ≤ t') (c : ℕ) (e : Edge R.W R.Qq (m + 1)) :
    CCL R lam0 t c e ≤ CCL R lam0 t' c e := by
  unfold CCL
  exact inf_le_inf_right _ (inf_le_inf_right _ (scale_neg_mono _ (RS.w_ne R) h _))

theorem lattice_count_prime_mono_level {t t' : ℕ} (h : t ≤ t') (c : ℕ) (e : Edge R.W R.Qq (m + 1)) :
    CCL' R lam0 t c e ≤ CCL' R lam0 t' c e := by
  unfold CCL'
  exact inf_le_inf_right _ (inf_le_inf_right _ (scale_neg_mono _ (RS.w_ne R) h _))

theorem RhoL_mono {t t' c : ℕ} {D D' X X' : ℝ} (ht : t ≤ t') (hD : D ≤ D') (hX : X' ≤ X)
    (h : RhoL R lam0 t c D X) : RhoL R lam0 t' c D' X' := by
  intro e he
  exact RhoGE_mono (lattice_count_mono_level R lam0 ht c e) (lattice_count_prime_mono_level R lam0 ht c e) hD hX (h e he)

theorem RhoL_zero (t c : ℕ) (D : ℝ) {X : ℝ} (hX : X ≤ 0) : RhoL R lam0 t c D X := by
  intro e _
  exact ⟨0, by simpa using hX, Or.inl rfl⟩

theorem normalized_group_order_nonneg (R : RS p n') (k : ℕ) : 0 ≤ gaussianNumber (p ^ n') k := by
  unfold gaussianNumber
  generalize p ^ n' = q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rcases k with _ | k <;> simp
  · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ hq')) (sub_nonneg.mpr hq')

theorem dL_nonneg : 0 ≤ dL R lam0 := by
  unfold dL
  exact div_nonneg (Nat.cast_nonneg _) (normalized_group_order_nonneg R _)

theorem rho_inf_mem (t c : ℕ) (D : ℝ) :
    RhoL R lam0 t c D ((1 - sInf {κ : ℝ | 0 ≤ κ ∧ RhoL R lam0 t c D ((1 - κ) * dL R lam0)}) * dL R lam0) := by
  set S : Set ℝ := {κ : ℝ | 0 ≤ κ ∧ RhoL R lam0 t c D ((1 - κ) * dL R lam0)} with hS
  have h1 : (1 : ℝ) ∈ S := ⟨zero_le_one, by
    rw [sub_self, zero_mul]; exact RhoL_zero R lam0 t c D le_rfl⟩
  rcases (dL_nonneg R lam0).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact RhoL_zero R lam0 t c D le_rfl
  set Xs := (1 - sInf S) * dL R lam0 with hXs
  intro e he
  by_cases hle : Xs ≤ 0
  · exact ⟨0, by simpa using hle, Or.inl rfl⟩
  push_neg at hle
  have hceil : (⌈Xs⌉₊ : ℝ) - 1 < Xs := by linarith [Nat.ceil_lt_add_one hle.le]
  have hδ : 0 < (Xs - ((⌈Xs⌉₊ : ℝ) - 1)) / dL R lam0 := div_pos (sub_pos.mpr hceil) hpos
  obtain ⟨κ, hκS, hκlt⟩ := exists_lt_of_csInf_lt ⟨1, h1⟩
    (lt_add_of_pos_right (sInf S) hδ)
  obtain ⟨n, hn, hf⟩ := hκS.2 e he
  refine ⟨n, ?_, hf⟩
  have h2 : κ * dL R lam0 < sInf S * dL R lam0 + (Xs - ((⌈Xs⌉₊ : ℝ) - 1)) := by
    have := mul_lt_mul_of_pos_right hκlt hpos
    rwa [add_mul, div_mul_cancel₀ _ hpos.ne'] at this
  have h3 : (⌈Xs⌉₊ : ℝ) < (n : ℝ) + 1 := by
    have : (1 - κ) * dL R lam0 = dL R lam0 - κ * dL R lam0 := by ring
    have : Xs = dL R lam0 - sInf S * dL R lam0 := by rw [hXs]; ring
    linarith
  have h4 : ⌈Xs⌉₊ < n + 1 := by exact_mod_cast h3
  calc Xs ≤ (⌈Xs⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ n := by exact_mod_cast (by omega : ⌈Xs⌉₊ ≤ n)

end Clean

theorem kF_mem (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) :
    RhoL R (flatW X.m al be) (X.tStar K al be) X.c4 (X.D1 K)
      ((1 - X.kF K R al be) * dL R (flatW X.m al be)) := by
  unfold Dat.kF
  exact rho_inf_mem R _ _ _ _

theorem kF_nonneg' (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be := by
  unfold Dat.kF
  exact Real.sInf_nonneg fun x hx => hx.1

theorem kF_le_one (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : X.kF K R al be ≤ 1 := by
  unfold Dat.kF
  refine csInf_le ⟨0, fun x hx => hx.1⟩ ⟨zero_le_one, ?_⟩
  rw [sub_self, zero_mul]
  exact RhoL_zero R _ _ _ _ le_rfl

theorem lpprime_of_one_le {p n' : ℕ} (R : RS p n') {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ)
    (κ : ℝ) (cStar : ℕ) (hc : 4 * (D + 1) ≤ cStar) (hκ : 1 ≤ κ) :
    LPprime (W := R.W) p n' R.ι R.σ R.w r lam0 t D κ cStar := by
  unfold LPprime LPprimeAt GoodRankK
  refine ⟨hc, fun L _ => ?_⟩
  refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 0, ?_,
    0, 0, fun _ j => j.elim0⟩
  push_cast
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)

theorem ex_mono {n' : ℕ} {TT : Finset (Fin n')} {f g : TT → ℕ} (h : ∀ s, f s ≤ g s) (s : Fin n') :
    ex f s ≤ ex g s := by
  unfold ex
  split_ifs
  · exact h _
  · exact le_rfl

theorem initial_level_mono_weights (X : Dat) (K : Cst) {al be al' be' : X.TT → ℕ} (ha : ∀ s, al s ≤ al' s) (hb : ∀ s, be s ≤ be' s) :
    X.t0 K al be ≤ X.t0 K al' be' := by
  unfold Dat.t0 t0I t0G4
  gcongr
  all_goals first | exact ex_mono hb _ | exact ex_mono ha _

theorem tStar_mono (X : Dat) (K : Cst) {al be al' be' : X.TT → ℕ} (ha : ∀ s, al s ≤ al' s)
    (hb : ∀ s, be s ≤ be' s) : X.tStar K al be ≤ X.tStar K al' be' := by
  unfold Dat.tStar
  exact Nat.ceil_mono (by linarith [initial_level_mono_weights X K ha hb])

theorem topW_base {n' m : ℕ} {TT : Finset (Fin n')} {aw bw : Fin n' → ℤ} {c : ℕ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsBaseWeight TT aw bw c lam0) :
    IsBaseWeight TT aw bw c (topW TT lam0) := by
  intro s
  refine ⟨fun hs => ?_, fun hs i => ?_⟩
  · simp only [topW, if_pos hs]
    exact (h s).1 hs
  · simp [topW, hs]

theorem topW_dom {n' m : ℕ} {TT : Finset (Fin n')} {lam0 : Fin n' → Fin (m + 1) → ℤ} (h : IsDominant lam0) :
    IsDominant (topW TT lam0) := by
  intro s
  by_cases hs : s ∈ TT
  · simp only [topW, if_pos hs]
    exact h s
  · simp only [topW, if_neg hs]
    exact antitone_const

theorem topW_zero {n' m : ℕ} {TT : Finset (Fin n')} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') (hs : s ∉ TT) :
    topW TT lam0 s = 0 := by
  simp [topW, hs]

open Classical in

theorem midLP_of (h60c : RhoLowerBoundLargeConductor) (h62 : CloudWeightLowerBound) (h63 : ResidueClassCount) : ∀ K C, MidLP K C := by
  intro K C X hF R aw bw lam0 hW t ht
  have hcst := hF.cst
  by_cases h1 : 1 ≤ X.kText K R (fun s => aw s) (fun s => bw s)
  · exact lpprime_of_one_le R 1 lam0 t X.Dp _ X.cStar (by omega) h1
  push_neg at h1
  have heps : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' :=
    div_nonneg (by unfold Dat.k; positivity) hF.bpos.le

  have hins : X.Inside (fun s => aw s) (fun s => bw s) := by
    by_contra hn
    apply absurd h1
    push_neg
    have := kF_nonneg' X K R (fun s => ((fun s : X.TT => aw s) s + X.ccl).toNat)
      (fun s => ((fun s : X.TT => bw s) s + X.ccl).toNat)
    simp only [Dat.kText, if_neg hn]
    linarith
  have hAs : ∀ s : X.TT, (((aw s - X.ccl).toNat : ℕ) : ℤ) = aw s - X.ccl := fun s =>
    Int.toNat_of_nonneg (by have h3 : (X.a : ℤ) ≤ aw s - X.ccl := (hins s).1; omega)
  have hbl : 0 < X.bl := by linarith [hF.lowb, hF.bpos]
  have hBs : ∀ s : X.TT, (((bw s - X.ccl).toNat : ℕ) : ℤ) = bw s - X.ccl := fun s =>
    Int.toNat_of_nonneg (by
      have h : X.bl ≤ ((bw s - X.ccl : ℤ) : ℝ) := (hins s).2
      have : (0 : ℝ) ≤ ((bw s - X.ccl : ℤ) : ℝ) := by linarith
      exact_mod_cast this)
  have hA2 : (fun s : X.TT => (aw s - X.ccl).toNat + 2 * X.ccl) = fun s : X.TT => (aw s + X.ccl).toNat := by
    funext s
    have h0 := hAs s
    have h2 : (((aw s + X.ccl).toNat : ℕ) : ℤ) = aw s + X.ccl :=
      Int.toNat_of_nonneg (by have h3 : (X.a : ℤ) ≤ aw s - X.ccl := (hins s).1; omega)
    omega
  have hB2 : (fun s : X.TT => (bw s - X.ccl).toNat + 2 * X.ccl) = fun s : X.TT => (bw s + X.ccl).toNat := by
    funext s
    have h0 := hBs s
    have h2 : (((bw s + X.ccl).toNat : ℕ) : ℤ) = bw s + X.ccl :=
      Int.toNat_of_nonneg (by have := hBs s; omega)
    omega
  have r1 : RhoL R (flatW X.m (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat))
      (X.tStar K (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat)) X.c4 (X.D1 K)
      ((1 - X.kF K R (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat)) *
        dL R (flatW X.m (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat))) :=
    RhoL_mono R _ (tStar_mono X K (fun s => Int.toNat_le_toNat (by omega))
      (fun s => Int.toNat_le_toNat (by omega))) le_rfl le_rfl (kF_mem X K R _ _)
  have r2 : RhoL R (flatW X.m (fun s : X.TT => (aw s - X.ccl).toNat + 2 * X.ccl)
        (fun s : X.TT => (bw s - X.ccl).toNat + 2 * X.ccl))
      (X.tStar K (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat)) X.c4 (X.D1 K)
      ((1 - X.kF K R (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat)) *
        dL R (flatW X.m (fun s : X.TT => (aw s - X.ccl).toNat + 2 * X.ccl)
          (fun s : X.TT => (bw s - X.ccl).toNat + 2 * X.ccl))) := by
    rw [hA2, hB2]
    exact kF_mem X K R _ _
  have r62 := h62 X.p X.n' R X.m hF.m2 X.TT X.a X.ccl X.b' aw bw (topW X.TT lam0)
    (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat)
    (topW_base hW.1) (topW_dom hW.2.1) (fun s hs => topW_zero lam0 s hs)
    (fun s => ⟨hAs s, hBs s⟩) hF.bpos
    (fun s => ⟨by
        have h0 := hAs s
        have h3 : (X.a : ℤ) ≤ aw s - X.ccl := (hins s).1
        have : X.a ≤ (aw s - X.ccl).toNat := by omega
        have : (X.a : ℝ) ≤ ((aw s - X.ccl).toNat : ℝ) := by exact_mod_cast this
        linarith [hF.lowa],
      by
        have h0 : (((bw s - X.ccl).toNat : ℕ) : ℝ) = ((bw s - X.ccl : ℤ) : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (hBs s)
        have : X.bl ≤ ((bw s - X.ccl : ℤ) : ℝ) := (hins s).2
        linarith [hF.lowb]⟩)
    hF.a8 hF.eps
    (X.tStar K (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat)) X.c4 (X.D1 K)
    (X.kF K R (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat))
    (X.kF K R (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat))
    hF.D1nn hF.four_depth_lt_conductor (by show 2 * X.TT.card * X.ccl ≤ X.cStar + 2 * X.TT.card * X.ccl + 2 * X.n' * X.ccl; omega)
    (kF_nonneg' X K R _ _) (kF_le_one X K R _ _) (kF_nonneg' X K R _ _) r1 r2
  have r63 := h63 X.p X.n' R X.m X.TT X.ccl aw bw lam0 hW.1 hW.2.1 _ _ _ _
    (by show 2 * X.n' * X.ccl ≤ X.cStar + 2 * X.TT.card * X.ccl + 2 * X.n' * X.ccl - 2 * X.TT.card * X.ccl; omega)
    r62
  have hc : X.c4 - 2 * X.TT.card * X.ccl - 2 * X.n' * X.ccl = X.cStar := by
    show X.cStar + 2 * X.TT.card * X.ccl + 2 * X.n' * X.ccl - 2 * X.TT.card * X.ccl - 2 * X.n' * X.ccl = X.cStar
    omega
  rw [hc] at r63
  have htt : X.tStar K (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat) +
      2 * X.n' * X.ccl ≤ t := by
    have := hF.tle aw bw hW.2.2
    have h5 : ((X.tStar K (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat) +
        2 * X.n' * X.ccl : ℕ) : ℝ) ≤ t := by push_cast; linarith
    exact_mod_cast h5
  refine h60c X.p X.n' R X.m lam0 hW.2.1 t X.cStar X.Dp _ (by omega) (by omega) ?_
  have hκ : X.kText K R (fun s => aw s) (fun s => bw s) =
      X.kF K R (fun s : X.TT => (aw s - X.ccl).toNat) (fun s : X.TT => (bw s - X.ccl).toNat) +
        2 * X.kF K R (fun s : X.TT => (aw s + X.ccl).toNat) (fun s : X.TT => (bw s + X.ccl).toNat) +
        12 * (X.TT.card : ℝ) * ((X.m : ℝ) + 1) * X.ccl / X.b' := by
    simp only [Dat.kText, if_pos hins]
    rfl
  rw [hκ]
  exact RhoL_mono R lam0 htt hF.dle le_rfl r63

end Formalism.MainNotions.flipOneThree.Pf

end
