import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineFiltrationAntitone

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem coeff_alg_mul (o : O) (F : PowerSeries LL) (j : ℕ) :
    coeff j (algebraMap O (PowerSeries LL) o * F) = algebraMap O LL o * coeff j F := by
  rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
  first
    | rw [← PowerSeries.smul_eq_C_mul]; simp
    | simp [Algebra.algebraMap_eq_smul_one]

theorem dv_smul' (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (r : LL) (c : Fin d → LL) :
    dv W T e b (r • c) = r • dv W T e b c := by
  rw [← dvL_apply, map_smul, dvL_apply]

variable [IsDomain O] [NeZero n] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem secIn_of_fil (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (f : Fin d → W.EE) (u : Fin d → LetA O n) (hu : ∀ m, u m ∈ W.AΔ)
    (hf : ∀ m, algebraMap (LetA O n) W.EE (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) * f m =
      algebraMap (LetA O n) W.EE (letE (c' + ((e + 1 : ℕ) : ZMod n)) *
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e) * u m))
    (hfil : ∀ j : ℕ, (j : ℤ) < 2 * (A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) →
      dv W T (e + 1) b (fun m => coeff j (W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e * u m))) ∈
        FilS W T (c' + ((e + 1 : ℕ) : ZMod n)) 0
          ((A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) - j)) :
    ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
      (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m := by
  set a : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha
  set H : ℕ := A.Hs a (e + 1) 0 with hH
  set LU := Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e with hLU
  have hinj := C.hinj
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W

  let Gf : ℤ → Submodule LL (Fin d → LL) := fun w => (FilS W T a 0 w).comap (dvL W T (e + 1) b)
  have hGa : Antitone Gf := fun _ _ h => Submodule.comap_mono (crystalline_filtration_antitone W T a h)
  have hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T a 0 (-(H : ℤ)) := fun c₀ =>
    Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W C.hbij A hA c' hc' T hT b hb (e + 1) 0 (by omega) c₀
  have hGtop : Gf (-(H : ℤ)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    show dv W T (e + 1) b c ∈ FilS W T a 0 (-(H : ℤ))
    have hc : c = ∑ m, c m • (Pi.single m (1 : LL) : Fin d → LL) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [hc, ← dvL_apply, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [map_smul, dvL_apply]
    refine Submodule.smul_mem _ _ ?_
    have h1 := hlow (Pi.single m 1)
    have h2 : dvO W T (e + 1) b (Pi.single m 1) = dv W T (e + 1) b (Pi.single m 1) := by
      unfold dvO; congr 1; funext k; by_cases hk : k = m
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rwa [h2] at h1
  obtain ⟨I, P, Q, h, hPQ, hPG, hlev, hvan⟩ :=
    Formalism.MainNotions.UnusedSlot80.CrA.adapted Gf hGa (-(H : ℤ)) (H : ℤ) (by omega) hGtop
  obtain ⟨κ1, hP1⟩ := exists_lpow_fin W.v_l C.hO2 (fun im : Fin I × Fin d => P im.1 im.2)
  obtain ⟨κ2, hQ1⟩ := exists_lpow_fin W.v_l C.hO2 (fun im : Fin I × Fin d => Q im.1 im.2)
  choose P' hP' using hP1
  choose Q' hQ' using hQ1

  let k : Fin I → ℕ := fun i => ((H : ℤ) - h i).toNat
  let Vp : Fin I → LetA O n := fun i => ∑ m, algebraMap O (LetA O n) (Q' (i, m)) * u m
  let g : Fin I → W.EE := fun i => ∑ m, algebraMap O W.EE (Q' (i, m)) * f m
  let c₀ : Fin I → Fin d → O := fun i m => P' (i, m)
  let α : Fin I → ℕ → ℤ := fun i s => if s = 0 then (k i : ℤ) - H else (A.Hs a (e + 1) s : ℤ)
  have hVpA : ∀ i, Vp i ∈ W.AΔ := fun i =>
    Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hu m)

  have hvan' : ∀ i, ∀ j < k i, coeff j (W.lev a ζ (Vp i)) = 0 := by
    intro i
    apply X_pow_dvd_of_unit (cc_lev_piLamUp W C.hR A c' e a ζ hζ)
    intro j hj
    have hjH : (j : ℤ) < (H : ℤ) - h i := Int.lt_toNat.mp hj
    have hk2 : (j : ℤ) < 2 * (H : ℤ) := by
      have := (hlev i).1
      omega
    have hmem : (fun m => coeff j (W.lev a ζ (W.π₀ * LU * u m))) ∈ Gf ((H : ℤ) - j) := hfil j hk2
    have hz := hvan ((H : ℤ) - j) (by omega) _ hmem i (by omega)
    rw [← map_mul]
    have e1 : W.π₀ * LU * Vp i = ∑ m, algebraMap O (LetA O n) (Q' (i, m)) * (W.π₀ * LU * u m) := by
      simp only [Vp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have e2 : ∀ m, coeff j (W.lev a ζ (algebraMap O (LetA O n) (Q' (i, m)) * (W.π₀ * LU * u m))) =
        (PD.p : LL) ^ κ2 * (Q i m * coeff j (W.lev a ζ (W.π₀ * LU * u m))) := by
      intro m
      rw [map_mul, AlgHom.commutes, coeff_alg_mul, hQ']
      ring
    rw [e1, map_sum, map_sum, Finset.sum_congr rfl (fun m _ => e2 m), ← Finset.mul_sum, hz, mul_zero]

  have hdiv : ∀ i, ∃ h' ∈ W.AΔ, letE a * Vp i = ps W 0 ^ k i * h' := fun i =>
    Formalism.MainNotions.UnusedSlot80.DivLevR.divLev_of (W := W) C.hR (not_isUnit_p W C.hV) C.hinj a ζ hζ (Vp i) (hVpA i)
      (k i) (hvan' i)
  choose h' hh'A hh' using hdiv

  have hgV : ∀ i, algebraMap (LetA O n) W.EE (ps W 0 ^ H) * g i =
      algebraMap (LetA O n) W.EE (letE a * (W.π₀ * LU) * Vp i) := by
    intro i
    simp only [g, Vp, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, hf m, ← map_mul]
    congr 1; ring
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (ps W 0)) := Formalism.MainNotions.UnusedSlot80.LevC.ps_unitE W C.hR 0
  refine ⟨κ1 + κ2, I, g, c₀, α, fun i => ⟨?_, ?_⟩, fun m => ?_⟩
  ·
    have hnum : ∏ s ∈ Finset.range (e + 1), ps W s ^ (α i s).toNat =
        LU * ps W 0 ^ ((k i : ℤ) - H).toNat := by
      rw [Finset.prod_range_succ', hLU, lamUp_eq]
      congr 1
      all_goals (try (refine Finset.prod_congr rfl fun s _ => ?_; simp only [α, if_neg (Nat.succ_ne_zero s), Int.toNat_natCast]))
    have hden : ∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α i s)).toNat =
        ps W 0 ^ ((H : ℤ) - k i).toNat := by
      rw [Finset.prod_range_succ']
      have h1 : ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i (s + 1))).toNat = 1 :=
        Finset.prod_eq_one fun s _ => by
          simp only [α, if_neg (Nat.succ_ne_zero s)]
          rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
      rw [h1, one_mul]
      simp only [α, if_pos rfl, neg_sub]
    refine ⟨W.π₀ * h' i, W.AΔ.mul_mem C.hR.1 (hh'A i), ?_⟩
    rw [hnum, hden]
    have hk : ((H : ℤ) - k i).toNat + k i = H + ((k i : ℤ) - H).toNat := by omega
    have hl2 : letE a * Vp i = letE a * (ps W 0 ^ k i * h' i) := by
      rw [← hh' i, ← mul_assoc, Formalism.MainNotions.UnusedSlot80.DivLevR.letE_idem]
    apply (hunit.pow (k i)).mul_left_cancel
    rw [← map_pow, ← mul_assoc, ← map_mul, ← pow_add, add_comm, hk, pow_add, map_mul, mul_comm
      (algebraMap (LetA O n) W.EE (ps W 0 ^ H)), mul_assoc, hgV i, ← map_mul, ← map_mul]
    congr 1
    have e3 : letE a * (W.π₀ * LU) * Vp i = (W.π₀ * LU) * (letE a * Vp i) := by ring
    rw [e3, hl2]
    ring
  ·
    intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · have e1 : -(α i 0) = (H : ℤ) - k i := by simp only [α, if_pos rfl]; ring
      rw [e1]
      have e2 : dvO W T (e + 1) b (c₀ i) = ((PD.p : LL) ^ κ1) • dv W T (e + 1) b (P i) := by
        unfold dvO
        rw [← dv_smul']
        congr 1; funext m; simp [c₀, hP', smul_eq_mul]
      rw [e2]
      refine Submodule.smul_mem _ _ (crystalline_filtration_antitone W T a ?_ (hPG i))
      have := (hlev i).1
      show (H : ℤ) - ((H : ℤ) - h i).toNat ≤ h i
      omega
    · have e1 : α i s = (A.Hs a (e + 1) s : ℤ) := by simp only [α, if_neg (by omega : s ≠ 0)]
      rw [e1]
      exact Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W C.hbij A hA c' hc' T hT b hb (e + 1) s hs (c₀ i)
  ·
    have hδ : ∀ m', ∑ i, Q' (i, m') * P' (i, m) =
        if m = m' then ((PD.p : ℕ) : O) ^ (κ1 + κ2) else 0 := by
      intro m'
      apply hinj
      have h1 := congrFun (hPQ (Pi.single m' 1)) m
      have h2 : ∀ i, ∑ m'', Q i m'' * (Pi.single m' (1 : LL) : Fin d → LL) m'' = Q i m' := by
        intro i; simp [Pi.single_apply]
      simp only [h2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [map_sum]
      simp_rw [map_mul, hQ', hP']
      have h3 : ∑ i, (PD.p : LL) ^ κ2 * Q i m' * ((PD.p : LL) ^ κ1 * P i m) =
          (PD.p : LL) ^ (κ1 + κ2) * ∑ i, Q i m' * P i m := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h3, ← h1]
      by_cases hmm : m = m'
      · subst hmm; simp
      · simp [hmm, Pi.single_apply, Ne.symm hmm]
    show lE W (κ1 + κ2) * f m = ∑ i, g i * algebraMap O W.EE (c₀ i m)
    simp only [g, c₀, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h4 : ∀ m', ∑ i, algebraMap O W.EE (Q' (i, m')) * f m' * algebraMap O W.EE (P' (i, m)) =
        f m' * algebraMap O W.EE (∑ i, Q' (i, m') * P' (i, m)) := by
      intro m'
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    simp_rw [h4, hδ]
    rw [Finset.sum_eq_single m]
    · simp [lE, mul_comm]
    · intro m' _ hm'; simp [Ne.symm hm']
    · intro h0; exact absurd (Finset.mem_univ m) h0

end Formalism.MainNotions.UnusedSlot80.CrD
