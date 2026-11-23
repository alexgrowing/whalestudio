import Formalism.SharpRestriction.LevelLetterCocycles.IndepStep

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem indep (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) : ∀ m, c m = 0 := by
  obtain ⟨h3r, -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hπU := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3r)
  have key : ∀ k : ℕ, ∀ c : Fin d → LetA O n, (∀ m, c m ∈ W.AΔ) →
      (∀ m, letE (c' + (e : ZMod n)) * c m = c m) → ∑ m, c m • ((W.φD T) ^ e) (b m) = 0 →
      ∀ m, ∃ c₁ : LetA O n, c m = W.π₀ ^ k * c₁ := by
    intro k
    induction k with
    | zero => intro c _ _ _ m; exact ⟨c m, by simp⟩
    | succ k ih =>
      intro c hc hcl h0 m
      choose c₁ hc₁ hc₁l hcm using indep_step W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb e c hc hcl h0
      have h0' : ∑ m, c₁ m • ((W.φD T) ^ e) (b m) = 0 := by
        refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T hπU ?_
        rw [smul_zero, Finset.smul_sum, ← h0]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← hcm m]
      obtain ⟨c₂, hc₂⟩ := ih c₁ hc₁ hc₁l h0' m
      exact ⟨c₂, by rw [hcm m, hc₂, pow_succ]; ring⟩
  intro m
  obtain ⟨w, -, hw⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀_comp hR
  funext i
  refine PowerSeries.ext fun j => ?_
  obtain ⟨c₁, hc₁⟩ := key (j + 1) c hc hcl h0 m
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hdvd : (PowerSeries.X : PowerSeries O) ^ ((PD.p - 1) * (j + 1)) ∣ c m i := by
    rw [hc₁, Pi.mul_apply, Pi.pow_apply, show W.π₀ i = W.π₀₁ from rfl, hw, mul_pow, ← pow_mul]
    exact ⟨w ^ (j + 1) * c₁ i, by ring⟩
  rw [PowerSeries.X_pow_dvd_iff.1 hdvd j (by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ PD.p)])]
  simp

omit [NeZero n] in

theorem frame_inv_poly' (hinj : Function.Injective (algebraMap O LL)) {d : ℕ}
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ)
    (yy : Fin d → ℕ → Fin d → O) (hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m)
    (zz : ℕ → Fin d → Fin d → O)
    (hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m))
    {R : Type} [CommRing R] [Algebra O R] (Y : R) (k k' : Fin d) :
    ∃ ρ : Polynomial O, ∑ m, (∑ r ∈ Finset.range M, algebraMap O R (zz r k m) * Y ^ r) *
        (∑ r ∈ Finset.range M, algebraMap O R (yy k' r m) * Y ^ r) =
      algebraMap O R (((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0) + Y ^ M * Polynomial.aeval Y ρ := by
  set Hps : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hHps
  have hdet : IsUnit Hps.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (PowerSeries.constantCoeff : PowerSeries LL →+* LL).mapMatrix Hps = 1 := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHps, Matrix.of_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk, hsol0,
        Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hinv : Hps⁻¹ * Hps = 1 := Matrix.nonsing_inv_mul Hps hdet
  have hcoef : ∀ t, ∑ m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t,
      PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m = if t = 0 ∧ k = k' then 1 else 0 := by
    intro t
    have h := congrArg (fun Q : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff t (Q k k')) hinv
    simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, hHps, Matrix.of_apply,
      PowerSeries.coeff_mk] at h
    rw [h, Matrix.one_apply]
    by_cases hm : k = k'
    · by_cases ht : t = 0
      · subst ht; simp [hm]
      · simp [hm, ht, PowerSeries.coeff_one]
    · simp [hm]
  let GP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (zz r k m) * Polynomial.X ^ r
  let HP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (yy k' r m) * Polynomial.X ^ r
  have hGPc : ∀ m i, (GP m).coeff i = if i < M then zz i k m else 0 := by
    intro m i
    simp only [GP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hHPc : ∀ m i, (HP m).coeff i = if i < M then yy k' i m else 0 := by
    intro m i
    simp only [HP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  set cst : O := ((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0 with hcst
  set Q : Polynomial O := ∑ m, GP m * HP m - Polynomial.C cst with hQdef
  have hQ : ∀ t < M, Q.coeff t = 0 := by
    intro t ht
    apply hinj
    rw [map_zero, hQdef, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C, map_sub,
      map_sum]
    have hk : ∀ m, algebraMap O LL ((GP m * HP m).coeff t) = (PD.p : LL) ^ (2 * κ) *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m := by
      intro m
      rw [Polynomial.coeff_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hGPc, hHPc, if_pos (by omega), if_pos (by omega), map_mul, hzz x.1 (by omega),
        hyy k' x.2 (by omega)]
      ring
    rw [Finset.sum_congr rfl fun m _ => hk m, ← Finset.mul_sum, hcoef t, hcst]
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hm : k = k' <;> simp [hm]
    · simp [ht0]
  obtain ⟨ρ, hρ⟩ := (Polynomial.X_pow_dvd_iff).2 hQ
  refine ⟨ρ, ?_⟩
  have h := congrArg (Polynomial.aeval Y) hρ
  simp only [hQdef, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, GP, HP,
    Polynomial.aeval_X] at h
  rw [← h]
  ring

theorem sec_unique (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ)
    (x : W.DD T) (f g : Fin d → W.EE)
    (hf : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hg : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x g)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (hgr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (g k)) :
    ∃ t : ℕ, ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1
      (lE W t * (f k - g k)) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  set M : ℕ := A.M PD.p with hMdef
  obtain ⟨U, hU⟩ := lam_unit W hR A a e
  have hΛc : ∀ y z : W.EE, algebraMap (LetA O n) W.EE Λ * y = algebraMap (LetA O n) W.EE Λ * z → y = z :=
    fun y z h => by
      have hU' : (U : W.EE) = algebraMap (LetA O n) W.EE Λ := hU
      rw [← hU'] at h
      have := congrArg (fun w => ((U⁻¹ : W.EEˣ) : W.EE) * w) h
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  have h0 := repVV_sub W hinj T c' e M Λ b sol x x f g hf hg
  rw [sub_self, repVV_iff] at h0
  obtain ⟨κ, Hh, hHh, hRV⟩ := h0
  set K : ℕ := κ + Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M with hKdef
  have hRV' := rv_up W T c' e Λ κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) Hh 0 (f - g) hRV
  obtain ⟨κ', aa, haa, hP⟩ := hRV'
  choose yy hyy hHe using fun k => horTr_scale W T b sol M κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) k (hHh k)

  choose uf huf hfu using hfr
  choose ug hug hgu using hgr
  have haa_eq : ∀ k, aa k = letE a * (uf k - ug k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2, Pi.sub_apply, mul_sub, hfu k, hgu k, ← map_sub]
    congr 1; ring
  have haal : ∀ k, letE a * aa k = aa k := by
    intro k; rw [haa_eq k, ← mul_assoc, letE_mul_self]

  simp only [smul_zero, zero_sub, smul_neg] at hP
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨δ, hδ, hpδ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 p hp
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  have hφH : ∀ k, ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
      ∑ m, HY m k • ((W.φD T) ^ e) (b m) := by
    intro k
    rw [hHe k, Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

  let E : Fin d → LetA O n := fun m => lA W ^ κ' * ∑ k, aa k * HY m k
  have hrel : ∑ m, (letE a * (E m + W.π₀ * Λ ^ 2 * δ m)) • ((W.φD T) ^ e) (b m) = 0 := by
    have h1 : lA W ^ κ' • ∑ k, aa k • ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
        ∑ m, E m • ((W.φD T) ^ e) (b m) := by
      simp only [hφH, Finset.smul_sum, smul_smul, E]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
    have h2 : ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) = 0 := by
      rw [show ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) =
          (∑ m, E m • ((W.φD T) ^ e) (b m)) + (W.π₀ * Λ ^ 2) • p by
        simp only [add_smul, Finset.sum_add_distrib, hpδ, Finset.smul_sum, mul_smul], ← h1, ← hpe,
        add_neg_cancel]
    simp only [mul_smul]
    rw [← Finset.smul_sum, h2, smul_zero]
  have hEl : ∀ m, letE a * E m = E m := by
    intro m
    simp only [E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← haal k]; ring_nf; rw [sq, letE_mul_self]
  have hind := indep W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb.1 e _
    (fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a)
      (W.AΔ.add_mem (W.AΔ.mul_mem (lA_mem W κ') (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
        (W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r))))
        (W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A a e) 2)) (hδ m))))
    (fun m => by rw [← mul_assoc, letE_mul_self]) hrel
  have hEm : ∀ m, E m = -(W.π₀ * Λ ^ 2 * (letE a * δ m)) := by
    intro m
    have := hind m
    rw [mul_add, hEl m] at this
    linear_combination this

  have hHc := hH hCA T hT.1 c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (K - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ K *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle : Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r ≤ K :=
      (Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le).trans (Nat.le_add_left _ _)
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  choose ρ hρ using fun k k' =>
    frame_inv_poly' (PD := PD) hinj sol (fun k => (hb.2 k).2) M K yy hyy zz hzz Y k k'
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA a e
  have hYM' : Y ^ M = W.π₀ * Λ ^ 2 * ν := by rw [hYdef, hMdef, hYM]
  let GY : Fin d → Fin d → LetA O n := fun k m =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m) * Y ^ r
  have hGY : ∀ k m, GY k m ∈ W.AΔ := fun k m => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  have hpK : algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (2 * K)) = lA W ^ (2 * K) := by
    rw [map_pow, map_natCast]; rfl
  refine ⟨κ' + 2 * K, fun k₀ => ?_⟩
  set θ : LetA O n := -(∑ m, GY k₀ m * (letE a * δ m)) -
    lA W ^ κ' * ν * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) with hθ
  have hθΔ : θ ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.neg_mem (W.AΔ.sum_mem fun m _ => W.AΔ.mul_mem (hGY k₀ m)
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hδ m))))
    (W.AΔ.mul_mem (W.AΔ.mul_mem (lA_mem W κ') hν) (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
      (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _)))
  have hkey : lA W ^ (κ' + 2 * K) * aa k₀ = W.π₀ * Λ ^ 2 * θ := by
    have hS1 : ∑ m, GY k₀ m * E m = lA W ^ κ' * ∑ k, aa k * (∑ m, GY k₀ m * HY m k) := by
      simp only [E, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
    have hS2 : ∑ k, aa k * (∑ m, GY k₀ m * HY m k) =
        lA W ^ (2 * K) * aa k₀ + Y ^ M * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
      have : ∀ k, aa k * (∑ m, GY k₀ m * HY m k) =
          lA W ^ (2 * K) * ((if k₀ = k then 1 else 0) * aa k) + Y ^ M * (aa k * Polynomial.aeval Y (ρ k₀ k)) := by
        intro k
        have h := hρ k₀ k
        simp only [GY, HY] at h ⊢
        rw [h, map_mul, hpK, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
        ring
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hS3 : ∑ m, GY k₀ m * E m = -(W.π₀ * Λ ^ 2 * ∑ m, GY k₀ m * (letE a * δ m)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [hEm m]; ring
    rw [hS1, hS2, hYM'] at hS3
    rw [hθ, pow_add]
    linear_combination hS3
  have hlet : ∀ k, algebraMap (LetA O n) W.EE (letE a) * (f - g) k = (f - g) k := by
    intro k
    apply hΛc
    rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE Λ), mul_assoc, (haa k).2, ← map_mul, haal k]
  have hX : letE a * ∑ m, GY k₀ m * (letE a * δ m) = ∑ m, GY k₀ m * (letE a * δ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    linear_combination (GY k₀ m * δ m) * (letE_mul_self (O := O) a)
  have hZ : letE a * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) = ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, haal k]
  have hθl : letE a * θ = θ := by
    rw [hθ]
    linear_combination -hX - (lA W ^ κ' * ν) * hZ
  refine ⟨θ, hθΔ, ?_⟩
  rw [map_one, one_mul]
  apply hΛc
  have hfg : algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀) = algebraMap (LetA O n) W.EE (aa k₀) := (haa k₀).2
  have hlE : lE W (κ' + 2 * K) = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K)) := by
    unfold lE lA; rw [map_pow, map_natCast]
  calc algebraMap (LetA O n) W.EE Λ * (lE W (κ' + 2 * K) * (f k₀ - g k₀))
      = lE W (κ' + 2 * K) * (algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀)) := by ring
    _ = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K) * aa k₀) := by rw [hfg, hlE, map_mul]
    _ = algebraMap (LetA O n) W.EE Λ * algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * θ) := by
      rw [hkey, ← map_mul]
      refine congrArg (algebraMap (LetA O n) W.EE) ?_
      conv_lhs => rw [← hθl]
      ring

end Formalism.MainNotions.UnusedSlot80.LevC
