import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem acoord_tele {R : Type*} [CommRing R] {d : ℕ} (J : Ideal R) (c t : R) (N : ℕ) (hN : t ^ N ∈ J)
    (Z : Matrix (Fin d) (Fin d) R) (v : Fin d → R)
    (h : ∀ m, Matrix.vecMul v (c • (1 : Matrix (Fin d) (Fin d) R) + t • Z) m ∈ J) :
    ∀ m, c ^ N * v m ∈ J := by
  have hw : ∀ l, Matrix.vecMul v (c • (1 : Matrix (Fin d) (Fin d) R) + t • Z) l =
      c * v l + t * Matrix.vecMul v Z l := by
    intro l
    simp [Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one]
  have key : ∀ k m, c ^ k * v m - (-t) ^ k * Matrix.vecMul v (Z ^ k) m ∈ J := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have hZ : Matrix.vecMul v (Z ^ (k + 1)) m = Matrix.vecMul (Matrix.vecMul v Z) (Z ^ k) m := by
        rw [pow_succ', Matrix.vecMul_vecMul]
      have hsum : c * Matrix.vecMul v (Z ^ k) m + t * Matrix.vecMul (Matrix.vecMul v Z) (Z ^ k) m ∈ J := by
        have e1 : c * Matrix.vecMul v (Z ^ k) m + t * Matrix.vecMul (Matrix.vecMul v Z) (Z ^ k) m =
            ∑ l, (c * v l + t * Matrix.vecMul v Z l) * (Z ^ k) l m := by
          simp only [Matrix.vecMul, dotProduct]
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [e1]
        exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (by rw [← hw]; exact h l)
      have e : c ^ (k + 1) * v m - (-t) ^ (k + 1) * Matrix.vecMul v (Z ^ (k + 1)) m =
          c * (c ^ k * v m - (-t) ^ k * Matrix.vecMul v (Z ^ k) m) +
            (-t) ^ k * (c * Matrix.vecMul v (Z ^ k) m + t * Matrix.vecMul (Matrix.vecMul v Z) (Z ^ k) m) := by
        rw [hZ]
        ring
      rw [e]
      exact J.add_mem (J.mul_mem_left _ (ih m)) (J.mul_mem_left _ hsum)
  intro m
  have h1 := key N m
  have h2 : (-t) ^ N * Matrix.vecMul v (Z ^ N) m ∈ J := by
    rw [neg_pow]
    exact J.mul_mem_right _ (J.mul_mem_left _ hN)
  have h3 := J.add_mem h1 h2
  simpa using h3

theorem acoord_sum_vecMul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d r : ℕ}
    (w : Fin d → R) (A : Matrix (Fin d) (Fin r) R) (β : Fin r → M) :
    ∑ m, w m • ∑ j, A m j • β j = ∑ j, Matrix.vecMul w A j • β j := by
  simp only [Matrix.vecMul, dotProduct, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

open Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.PhiPowers Formalism.MainNotions.UnusedSlot80.SatW Formalism.MainNotions.UnusedSlot80.SatPW in

theorem repVV_zero_coord [FiniteDimensional Qp LL] (W : LocWach PD LL O v n)
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c' : ZMod n) (e M : ℕ) (hM : 1 ≤ M) (Λ : LetA O n)
    (hΛ : Λ ∈ W.AΔ) (hΛu : IsUnit (algebraMap (LetA O n) W.EE Λ))
    (hN : ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ e) W.π₀) ^ N = W.π₀ * Λ ^ 2 * w)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol)
    (g : Fin d → W.EE) (hg : RepVV W T c' e M Λ b sol 0 g) :
    ∃ K : ℕ, ∀ k, ∃ u ∈ W.AΔ,
      algebraMap (LetA O n) W.EE (letE (c' + (e : ZMod n))) * (lE W K * g k) =
        algebraMap (LetA O n) W.EE (letE (c' + (e : ZMod n)) * (W.π₀ * Λ) * u) := by
  classical
  obtain ⟨hbij, hs, hp⟩ := hcase
  obtain ⟨hring, hmod⟩ := (hP9 T hT hs hp).2.2 (finrank_one_of_bij' hbij)
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  obtain ⟨⟨r, B₀, hB₀, huniq, hΔ⟩, _⟩ := hmod
  have hq : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
    obtain ⟨w, hw⟩ := hring.2.2.2.2.1
    rw [hw, Eat_π₀]
    exact isUnit_EE_of_UPi W ((UPi.unit _ w).mul (UPi_π₀ W h3).add_p)
  have hli := linInd_φ_pow W T hT hs B₀ hB₀ huniq hq e
  obtain ⟨N, wN, hwN, hNeq⟩ := hN
  set φe : LetA O n →ₐ[O] LetA O n := W.φA ^ e with hφe
  set E : LetA O n := letE (c' + (e : ZMod n)) with hE
  have hEΔ : E ∈ W.AΔ := letE_mem_AΔ W _
  have hEE : E * E = E := letE_mul_self _
  have hφc' : φe (letE c') = E := φA_pow_letE W c' e
  set β : Fin r → W.DD T := fun j => ((W.φD T) ^ e) ((letE c' : LetA O n) • B₀ j) with hβ
  have hfr := hb.1

  have hbm : ∀ m, (letE c' : LetA O n) • b m = b m := by
    intro m
    obtain ⟨y, -, hy⟩ := Submodule.mem_map.1 (hfr.1 m).2
    rw [← hy, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]

  choose α hαΔ hα using fun m => hΔ (b m) (hfr.1 m).1
  have hB₀c : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c' ((letE c' : LetA O n) • B₀ j) := fun j =>
    ⟨Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (letE_mem_AΔ W c') (hB₀ j),
      Submodule.mem_map.2 ⟨B₀ j, (hB₀ j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  choose α' hα' using fun j => (hfr.2 _ (hB₀c j)).exists
  have hbα : ∀ m, b m = ∑ j, α m j • ((letE c' : LetA O n) • B₀ j) := by
    intro m
    conv_lhs => rw [← hbm m, hα m]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
  have hαα' : ∀ m m', ∑ j, α m j * α' j m' = if m' = m then (letE c' : LetA O n) else 0 := by
    intro m
    obtain ⟨_, _, huq⟩ := hfr.2 (b m) (hfr.1 m)
    have e1 := huq (fun m' => ∑ j, α m j * α' j m') ⟨fun m' => ⟨W.AΔ.sum_mem fun j _ =>
        W.AΔ.mul_mem (hαΔ m j) ((hα' j).1 m').1, by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by
            rw [mul_left_comm, ((hα' j).1 m').2]⟩, by
      rw [hbα m]
      simp only [(fun j => (hα' j).2), Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]⟩
    have e2 := huq (fun m' => if m' = m then (letE c' : LetA O n) else 0) ⟨fun m' => ⟨by
        dsimp only
        split_ifs
        · exact letE_mem_AΔ W c'
        · exact W.AΔ.zero_mem, by dsimp only; split_ifs <;> simp [letE_mul_self]⟩, by
      simp [hbm m]⟩
    intro m'
    rw [← e2] at e1
    exact congrFun e1 m'

  obtain ⟨κ, κ', Hh, a', hHh, ha', hP⟩ := hg
  simp only [smul_zero, zero_sub] at hP
  obtain ⟨y, hyP, hy⟩ := hP
  obtain ⟨γc, hγΔ, rfl⟩ := Pp_coords W T B₀ hΔ c' e y hyP
  choose yk hyk hHhk using hHh
  set Hm : Matrix (Fin d) (Fin d) (LetA O n) :=
    Matrix.of fun k m => ∑ r ∈ Finset.range M, W.π₀ ^ r * algebraMap O (LetA O n) (yk k r m) with hHm
  have hHh' : ∀ k, Hh k = ∑ m, Hm k m • b m := by
    intro k
    rw [hHhk k]
    simp only [hHm, Matrix.of_apply, Formalism.MainNotions.LiftingTheory.vecB, Finset.smul_sum, Finset.sum_smul, smul_smul,
      ← algebraMap_smul (LetA O n) (yk k _ _) (b _)]
    rw [Finset.sum_comm]

  set Hφ := Hm.map φe with hHφ
  set αφ : Matrix (Fin d) (Fin r) (LetA O n) := (Matrix.of α).map φe with hαφ
  set α'φ : Matrix (Fin r) (Fin d) (LetA O n) := (Matrix.of α').map φe with hα'φ
  have hφb : ∀ m, ((W.φD T) ^ e) (b m) = ∑ j, αφ m j • β j := by
    intro m
    conv_lhs => rw [hbα m]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [φD_pow_smulA]; rfl
  have hφHh : ∀ k, ((W.φD T) ^ e) (Hh k) = ∑ j, Matrix.vecMul (Hφ k) αφ j • β j := by
    intro k
    rw [hHh' k, map_sum, ← acoord_sum_vecMul]
    exact Finset.sum_congr rfl fun m _ => by rw [φD_pow_smulA, hφb m]; rfl
  have hSig : ∑ k, a' k • ((W.φD T) ^ e) (Hh k) = ∑ j, Matrix.vecMul a' (Hφ * αφ) j • β j := by
    simp only [hφHh]
    rw [show Hφ * αφ = Matrix.of fun k j => Matrix.vecMul (Hφ k) αφ j from Matrix.ext fun _ _ => rfl]
    exact acoord_sum_vecMul a' _ β
  have hLHS : lA W ^ κ' • -∑ k, a' k • ((W.φD T) ^ e) (Hh k) =
      ∑ j, (-(lA W ^ κ' * Matrix.vecMul a' (Hφ * αφ) j)) • β j := by
    rw [hSig, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
    simp only [smul_smul, neg_smul]
  have hRHS : (W.π₀ * Λ ^ 2) • ∑ j, γc j • ((W.φD T) ^ e) ((letE c' : LetA O n) • B₀ j) =
      ∑ j, (W.π₀ * Λ ^ 2 * γc j) • β j := by
    rw [Finset.smul_sum]; simp only [smul_smul]; rfl
  rw [hLHS, hRHS] at hy
  have hcoef := fun j => coeff_eq W T B₀ c' e hli _ _ hy j

  have hαφα'φ : αφ * α'φ = E • (1 : Matrix (Fin d) (Fin d) (LetA O n)) := by
    refine Matrix.ext fun m m' => ?_
    rw [hαφ, hα'φ, ← Matrix.map_mul]
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [hαα' m m']
    split_ifs with h1 h2 h2
    · rw [hφc', mul_one]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [map_zero, mul_zero]
  have hkey : ∀ m₀, E * lA W ^ κ' * Matrix.vecMul a' Hφ m₀ =
      W.π₀ * Λ ^ 2 * (-(E * Matrix.vecMul γc α'φ m₀)) := by
    intro m₀
    have hV : (fun j => (-(lA W ^ κ' * Matrix.vecMul a' (Hφ * αφ) j)) * E) =
        fun j => W.π₀ * Λ ^ 2 * γc j * E := funext hcoef
    have h0 := congrFun (congrArg (fun V => Matrix.vecMul V α'φ) hV) m₀
    have hu : Matrix.vecMul (Matrix.vecMul a' (Hφ * αφ)) α'φ m₀ = E * Matrix.vecMul a' Hφ m₀ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, hαφα'φ, Matrix.mul_smul, Matrix.mul_one]
      simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hl : Matrix.vecMul (fun j => (-(lA W ^ κ' * Matrix.vecMul a' (Hφ * αφ) j)) * E) α'φ m₀ =
        -(lA W ^ κ' * E) * Matrix.vecMul (Matrix.vecMul a' (Hφ * αφ)) α'φ m₀ := by
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hr : Matrix.vecMul (fun j => W.π₀ * Λ ^ 2 * γc j * E) α'φ m₀ =
        W.π₀ * Λ ^ 2 * E * Matrix.vecMul γc α'φ m₀ := by
      simp only [Matrix.vecMul, dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hl, hr, hu] at h0
    linear_combination (-1 : LetA O n) * h0 - (lA W ^ κ' * Matrix.vecMul a' Hφ m₀) * hEE

  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  set Xm : Matrix (Fin d) (Fin d) (LetA O n) :=
    Matrix.of fun k m => ∑ r ∈ Finset.range M', W.π₀ ^ r * algebraMap O (LetA O n) (yk k (r + 1) m) with hXm
  have hy0 : ∀ k m, algebraMap O (LetA O n) (yk k 0 m) = lA W ^ κ * (1 : Matrix (Fin d) (Fin d) (LetA O n)) k m := by
    intro k m
    have h0 := hyk k 0 (by omega) m
    rw [(hb.2 k).2, Pi.single_apply] at h0
    have : yk k 0 m = ((PD.p : ℕ) : O) ^ κ * (if m = k then 1 else 0) := by
      apply hinj
      rw [h0, map_mul, map_pow, map_natCast]
      split_ifs <;> simp
    rw [this, Matrix.one_apply, map_mul, map_pow, map_natCast]
    simp only [lA]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hHmX : Hm = lA W ^ κ • (1 : Matrix (Fin d) (Fin d) (LetA O n)) + W.π₀ • Xm := by
    refine Matrix.ext fun k m => ?_
    simp only [hHm, hXm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_range_succ', pow_zero, one_mul, hy0, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by ring
  have hHφX : Hφ = lA W ^ κ • (1 : Matrix (Fin d) (Fin d) (LetA O n)) + φe W.π₀ • Xm.map φe := by
    rw [hHφ, hHmX]
    refine Matrix.ext fun k m => ?_
    have hφl : φe (lA W) = lA W := by simp only [lA, map_natCast]
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add,
      map_mul, map_pow, hφl]
    split_ifs <;> simp only [map_one, map_zero, mul_one, mul_zero]

  have hπ₀Δ : W.π₀ ∈ W.AΔ := Formalism.MainNotions.N.FrobeniusPowerSeries.GS.π₀_mem W
  have hlAΔ : lA W ∈ W.AΔ := natCast_mem W.AΔ PD.p
  have hXmΔ : ∀ k m, Xm k m ∈ W.AΔ := fun k m => by
    simp only [hXm, Matrix.of_apply]
    exact W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.pow_mem hπ₀Δ r) (W.AΔ.algebraMap_mem _)
  have hvΔ : ∀ k, E * lA W ^ κ' * a' k ∈ W.AΔ := fun k =>
    W.AΔ.mul_mem (W.AΔ.mul_mem hEΔ (W.AΔ.pow_mem hlAΔ κ')) (ha' k).1
  have hγα'Δ : ∀ m, -(E * Matrix.vecMul γc α'φ m) ∈ W.AΔ := fun m => by
    refine W.AΔ.neg_mem (W.AΔ.mul_mem hEΔ ?_)
    simp only [Matrix.vecMul, dotProduct, hα'φ, Matrix.map_apply, Matrix.of_apply]
    exact W.AΔ.sum_mem fun j _ => W.AΔ.mul_mem (hγΔ j) (φA_pow_mem_AΔ W ((hα' j).1 m).1 e)
  have hπΛΔ : W.π₀ * Λ ^ 2 ∈ W.AΔ := W.AΔ.mul_mem hπ₀Δ (W.AΔ.pow_mem hΛ 2)
  let vv : Fin d → W.AΔ := fun k => ⟨_, hvΔ k⟩
  let cc : W.AΔ := ⟨_, W.AΔ.pow_mem hlAΔ κ⟩
  let tt : W.AΔ := ⟨_, φA_pow_mem_AΔ W hπ₀Δ e⟩
  let ZZ : Matrix (Fin d) (Fin d) W.AΔ := Matrix.of fun k m => ⟨_, φA_pow_mem_AΔ W (hXmΔ k m) e⟩
  let JJ : Ideal W.AΔ := Ideal.span {⟨_, hπΛΔ⟩}
  have hNJ : tt ^ N ∈ JJ := Ideal.mem_span_singleton'.2 ⟨⟨wN, hwN⟩, Subtype.ext (by
    simp only [tt, SubmonoidClass.coe_pow, Subalgebra.coe_mul]
    rw [hNeq]; ring)⟩
  have hmapM : (cc • (1 : Matrix (Fin d) (Fin d) W.AΔ) + tt • ZZ).map W.AΔ.val = Hφ := by
    rw [hHφX]
    refine Matrix.ext fun k m => ?_
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp only [map_add, map_mul, map_one, map_zero, mul_one, mul_zero] <;> rfl
  have hcond : ∀ m, Matrix.vecMul vv (cc • (1 : Matrix (Fin d) (Fin d) W.AΔ) + tt • ZZ) m ∈ JJ := by
    intro m
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, hγα'Δ m⟩, Subtype.ext ?_⟩
    have h2 : ((Matrix.vecMul vv (cc • (1 : Matrix (Fin d) (Fin d) W.AΔ) + tt • ZZ) m : W.AΔ) : LetA O n) =
        Matrix.vecMul (fun k => E * lA W ^ κ' * a' k) Hφ m := by
      rw [← hmapM]
      exact RingHom.map_vecMul (W.AΔ.val : W.AΔ →+* LetA O n) _ vv m
    rw [Subalgebra.coe_mul, h2]
    show -(E * Matrix.vecMul γc α'φ m) * (W.π₀ * Λ ^ 2) = _
    have : Matrix.vecMul (fun k => E * lA W ^ κ' * a' k) Hφ m = E * lA W ^ κ' * Matrix.vecMul a' Hφ m := by
      simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hkey m]
    ring
  have htel := acoord_tele JJ cc tt N hNJ ZZ vv hcond
  refine ⟨κ * N + κ', fun k => ?_⟩
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (htel k)
  have hu' : (u : LetA O n) * (W.π₀ * Λ ^ 2) = (lA W ^ κ) ^ N * (E * lA W ^ κ' * a' k) := by
    have := congrArg Subtype.val hu
    simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow] at this
    exact this
  refine ⟨u, u.2, ?_⟩
  have h1 := congrArg (algebraMap (LetA O n) W.EE) hu'
  simp only [map_mul, map_pow] at h1
  rw [← (ha' k).2] at h1
  simp only [lA, map_natCast] at h1
  have hee : algebraMap (LetA O n) W.EE E * algebraMap (LetA O n) W.EE E = algebraMap (LetA O n) W.EE E := by
    rw [← map_mul, hEE]
  apply (hΛu.mul_left_inj).1
  simp only [map_mul, lE]
  linear_combination (-(algebraMap (LetA O n) W.EE E)) * h1 -
    (((PD.p : ℕ) : W.EE) ^ (κ * N + κ') * algebraMap (LetA O n) W.EE Λ * g k) * hee

end Formalism.MainNotions.N.FrobeniusPowerSeries
