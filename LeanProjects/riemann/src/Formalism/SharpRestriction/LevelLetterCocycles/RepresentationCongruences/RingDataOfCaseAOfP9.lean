import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.GS

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem ringData_of_caseA_of_p9 [FiniteDimensional Qp LL] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) : RD W := by
  obtain ⟨hK, hs, hp⟩ := hcase
  have hK1 : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hK).toLinearEquiv.finrank_eq, Module.finrank_self]
  obtain ⟨-, -, h3⟩ := hP9 W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W) hs hp
  obtain ⟨⟨-, huniq, hw1, -, -, hφ, hγ, -⟩, -⟩ := h3 hK1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qA W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  refine ⟨hw1, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hφ
    exact ⟨w, by rw [hw, hE]⟩
  · obtain ⟨w, hw⟩ := hγ
    exact ⟨w, by rw [hw, hE]⟩
  · intro a ha
    obtain ⟨f, hf, -⟩ := huniq a ha
    exact ⟨f, hf⟩

theorem p_ne_zero (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 := W.v_l
  have h2 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL) PD.p, h, map_zero]
  rw [h2, AddValuation.map_zero] at h1
  simp at h1

section Dvr

variable {W : LocWach PD LL O v n} [IsDomain O] [IsDiscreteValuationRing O]

theorem res_C_ϖ {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : PowerSeries O).map (IsLocalRing.residue O) = 0 := by
  have h0 : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  rw [PowerSeries.map_C, h0, map_zero]

theorem dvd_of_res {ϖ : O} (hϖ : Irreducible ϖ) {h : PowerSeries O}
    (h0 : h.map (IsLocalRing.residue O) = 0) : C ϖ ∣ h := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hc : ∀ k, ϖ ∣ PowerSeries.coeff k h := by
    intro k
    have hk : IsLocalRing.residue O (PowerSeries.coeff k h) = 0 := by
      have := congrArg (PowerSeries.coeff k) h0
      simpa [PowerSeries.coeff_map] using this
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at hk
    exact hk
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext k
  simp [PowerSeries.coeff_C_mul, hc k]

theorem dvd_right {ϖ : O} (hϖ : Irreducible ϖ) {g h : PowerSeries O}
    (hg : g.map (IsLocalRing.residue O) ≠ 0) (hd : C ϖ ∣ g * h) : C ϖ ∣ h := by
  obtain ⟨k, hk⟩ := hd
  have h1 : (g * h).map (IsLocalRing.residue O) = 0 := by
    rw [hk, map_mul, res_C_ϖ hϖ, zero_mul]
  rw [map_mul] at h1
  exact dvd_of_res hϖ ((mul_eq_zero.1 h1).resolve_left hg)

theorem peel {ϖ : O} (hϖ : Irreducible ϖ) {g : PowerSeries O} (hg : g.map (IsLocalRing.residue O) ≠ 0)
    (N : ℕ) : ∀ z y : PowerSeries O, C ϖ ^ N * z = g * y → ∃ y', z = g * y' := by
  have hne : (C ϖ : PowerSeries O) ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    simpa using congrArg PowerSeries.constantCoeff h0
  induction N with
  | zero =>
    intro z y h
    exact ⟨y, by simpa using h⟩
  | succ N ih =>
    intro z y h
    have hd : C ϖ ∣ g * y := ⟨C ϖ ^ N * z, by rw [← h]; ring⟩
    obtain ⟨y₁, hy₁⟩ := dvd_right hϖ hg hd
    apply ih z y₁
    apply mul_left_cancel₀ hne
    rw [hy₁] at h
    linear_combination h

theorem res_ne_of_isUnit {g : PowerSeries O} (hg : IsUnit g) : g.map (IsLocalRing.residue O) ≠ 0 := (hg.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero

theorem isUnit_letter {a : LetA O n} (ha : IsUnit a) (i : ZMod n) : IsUnit (a i) := ha.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) i)

theorem dist_π₀ (hR : RD W) (i : ZMod n) : (W.π₀ i).map (IsLocalRing.residue O) ≠ 0 := by
  obtain ⟨⟨w, hw⟩, -, -, -⟩ := hR
  rw [hw, Pi.mul_apply, map_mul]
  refine mul_ne_zero (res_ne_of_isUnit (isUnit_letter w.isUnit i)) ?_
  rw [Pi.pow_apply, map_pow]
  exact pow_ne_zero _ (by simp [letπ])

theorem cc_φpow (hR : RD W) (m : ℕ) (i : ZMod n) : constantCoeff ((W.φA ^ m) W.π₀ i) = 0 := by
  have hp1 : PD.p - 1 ≠ 0 := by
    intro h
    have h1 := W.v_l
    have : PD.p = 0 ∨ PD.p = 1 := by omega
    rcases this with h0 | h0 <;> rw [h0] at h1 <;> simp at h1
  obtain ⟨⟨w, hw⟩, ⟨w', hw'⟩, -, -⟩ := id hR
  induction m generalizing i with
  | zero =>
    rw [pow_zero, AlgHom.one_apply, hw]
    simp [letπ, zero_pow hp1]
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, hw']
    simp only [map_mul, map_pow, Pi.mul_apply, Pi.pow_apply, ih i, mul_zero, zero_mul]

theorem ps_letter (m : ℕ) (i : ZMod n) :
    ps W m i = (W.φA ^ m) W.π₀ i + C ((PD.p : ℕ) : O) := by
  show ((W.φA ^ m) (W.π₀ + ((PD.p : ℕ) : LetA O n))) i = _
  simp only [map_add, map_natCast, Pi.add_apply, Pi.natCast_apply]

theorem dist_ps (hR : RD W) (m : ℕ) (hD : ∀ i, ((W.φA ^ m) W.π₀ i).map (IsLocalRing.residue O) ≠ 0)
    (i : ZMod n) : (ps W m i).map (IsLocalRing.residue O) ≠ 0 := by
  rw [ps_letter, map_add, PowerSeries.map_C]
  intro h0
  have hcc : ∀ f : PowerSeries O, PowerSeries.constantCoeff (PowerSeries.map (IsLocalRing.residue O) f) =
      IsLocalRing.residue O (PowerSeries.constantCoeff f) := by
    intro f
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hc : IsLocalRing.residue O ((PD.p : ℕ) : O) = 0 := by
    have := congrArg PowerSeries.constantCoeff h0
    rw [map_add, PowerSeries.constantCoeff_C, hcc, cc_φpow hR m i, map_zero, zero_add, map_zero] at this
    exact this
  rw [hc, map_zero, add_zero] at h0
  exact hD i h0

theorem dist_φpow (hR : RD W) (m : ℕ) :
    ∀ i, ((W.φA ^ m) W.π₀ i).map (IsLocalRing.residue O) ≠ 0 := by
  obtain ⟨-, ⟨w', hw'⟩, -, -⟩ := id hR
  induction m with
  | zero =>
    intro i
    rw [pow_zero, AlgHom.one_apply]
    exact dist_π₀ hR i
  | succ k ih =>
    intro i
    rw [pow_succ, AlgHom.mul_apply, hw']
    simp only [map_mul, map_pow, Pi.mul_apply, Pi.pow_apply]
    refine mul_ne_zero (mul_ne_zero ?_ (ih i)) (pow_ne_zero _ ?_)
    · exact res_ne_of_isUnit (isUnit_letter (w'.isUnit.map (W.φA ^ k)) i)
    · exact dist_ps hR k ih i

theorem dist_piPs (hR : RD W) {f : LetA O n} (hf : f ∈ PiPs W) (i : ZMod n) :
    (f i).map (IsLocalRing.residue O) ≠ 0 := by
  unfold PiPs at hf
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨m, rfl⟩
    · exact dist_π₀ hR i
    · exact dist_ps hR m (dist_φpow hR m) i
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Pi.mul_apply, map_mul]
    exact mul_ne_zero hx hy

theorem cancel_l (hp0 : ((PD.p : ℕ) : O) ≠ 0) (k : ℕ) {a b : LetA O n}
    (h : lA W ^ k * a = lA W ^ k * b) : a = b := by
  funext i
  have h' := congrFun h i
  simp only [lA, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h'
  refine mul_left_cancel₀ (pow_ne_zero _ ?_) h'
  intro h0
  apply hp0
  simpa using congrArg PowerSeries.constantCoeff h0

theorem sat_A_core (hR : RD W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) {f z y : LetA O n} (hf : f ∈ PiPs W)
    (hy : y ∈ W.AΔ) (k : ℕ) (hky : lA W ^ k * z = f * y) : ∃ y' ∈ W.AΔ, z = f * y' := by
  have memΔ : ∀ a : LetA O n, a ∈ W.AΔ ↔ ∀ δ ∈ W.DelF, W.γA δ a = a := fun _ => Iff.rfl
  have hγ : ∀ (g : W.Gam) (a : LetA O n) (i : ZMod n), W.γA g a i = W.γ₀ g (a i) :=
    fun _ _ _ => rfl
  have hcomm : ∀ (g : W.Gam) (a : LetA O n), W.γA g (W.φA a) = W.φA (W.γA g a) :=
    fun g a => funext fun i => (W.γ₀_comm g (a (i - 1))).symm
  have hcommP : ∀ (m : ℕ) (g : W.Gam) (a : LetA O n),
      W.γA g ((W.φA ^ m) a) = (W.φA ^ m) (W.γA g a) := by
    intro m
    induction m with
    | zero => intro g a; rfl
    | succ m ih =>
      intro g a
      rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, ih, hcomm]
  have hS : ∀ δ' ∈ W.DelF, ∀ x : PowerSeries O,
      W.γ₀ δ' (∑ δ ∈ W.DelF, W.γ₀ δ x) = ∑ δ ∈ W.DelF, W.γ₀ δ x := by
    intro δ' hδ' x
    rw [map_sum]
    refine Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      try simp only [Finset.mem_coe] at ha ⊢
      show δ' * a ∈ W.DelF
      rw [W.DelF_def] at hδ' ha ⊢
      obtain ⟨k₁, hk₁, h₁⟩ := hδ'
      obtain ⟨k₂, hk₂, h₂⟩ := ha
      exact ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by
        rw [mul_pow, pow_mul, h₁, one_pow, one_mul, mul_comm k₁ k₂, pow_mul, h₂, one_pow]⟩
    · intro a ha
      try simp only [Finset.mem_coe] at ha ⊢
      show δ'⁻¹ * a ∈ W.DelF
      rw [W.DelF_def] at hδ' ha ⊢
      obtain ⟨k₁, hk₁, h₁⟩ := hδ'
      obtain ⟨k₂, hk₂, h₂⟩ := ha
      exact ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, by
        rw [mul_pow, inv_pow, pow_mul, h₁, one_pow, inv_one, one_mul, mul_comm k₁ k₂, pow_mul, h₂,
          one_pow]⟩
    · intro a _
      exact inv_mul_cancel_left δ' a
    · intro a _
      exact mul_inv_cancel_left δ' a
    · intro a _
      simp only [map_mul, AlgHom.mul_apply]
  have hπ₀ : W.π₀ ∈ W.AΔ := by
    rw [memΔ]
    intro δ hδ
    funext i
    rw [hγ]
    show W.γ₀ δ W.π₀₁ = W.π₀₁
    unfold Formalism.BasicNotions.LocWach.π₀₁
    rw [map_add, map_sub, map_one, map_natCast, hS δ hδ]
  have hps : ∀ m, ps W m ∈ W.AΔ := by
    intro m
    rw [memΔ]
    intro δ hδ
    show W.γA δ ((W.φA ^ m) (qA W)) = (W.φA ^ m) (qA W)
    rw [hcommP, qA, lA, map_add, map_natCast, (memΔ _).1 hπ₀ δ hδ]
  have hPi : PiPs W ≤ W.AΔ.toSubmonoid := by
    unfold PiPs
    rw [Submonoid.closure_le]
    rintro x (rfl | ⟨m, rfl⟩)
    · exact hπ₀
    · exact hps m
  have hfΔ : f ∈ W.AΔ := hPi hf
  have hzΔ : ∀ δ ∈ W.DelF, W.γA δ z = z := by
    intro δ hδ
    refine cancel_l (W := W) hp0 k ?_
    have h1 : W.γA δ (lA W ^ k * z) = lA W ^ k * z := by
      rw [hky]
      exact (memΔ _).1 (W.AΔ.mul_mem hfΔ hy) δ hδ
    rw [map_mul, map_pow] at h1
    rw [lA] at h1 ⊢
    rw [map_natCast] at h1
    exact h1
  have hfne : ∀ i, f i ≠ 0 := fun i h0 => dist_piPs hR hf i (by rw [h0, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hpC : ((PD.p : ℕ) : PowerSeries O) = C (u : O) * C ϖ ^ e := by
    rw [← map_pow, ← map_mul, ← hu, map_natCast]
  have hcomp : ∀ i, ∃ t : PowerSeries O, z i = f i * t := by
    intro i
    have hi := congrFun hky i
    simp only [Pi.mul_apply, Pi.pow_apply, lA, Pi.natCast_apply] at hi
    obtain ⟨t, ht⟩ := peel hϖ (dist_piPs hR hf i) (e * k) (C (u : O) ^ k * z i) (y i) (by
      rw [← hi, hpC]
      ring)
    refine ⟨C ((u⁻¹ : Oˣ) : O) ^ k * t, ?_⟩
    calc z i = C ((u⁻¹ : Oˣ) : O) ^ k * (C (u : O) ^ k * z i) := by
          rw [← mul_assoc, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow, one_mul]
      _ = f i * (C ((u⁻¹ : Oˣ) : O) ^ k * t) := by rw [ht]; ring
  choose t ht using hcomp
  have hzt : z = f * t := funext fun i => ht i
  refine ⟨t, ?_, hzt⟩
  rw [memΔ]
  intro δ hδ
  have hfy : f * W.γA δ t = f * t := by
    have h2 := hzΔ δ hδ
    rw [hzt, map_mul, (memΔ _).1 hfΔ δ hδ] at h2
    exact h2
  funext i
  exact mul_left_cancel₀ (hfne i) (congrFun hfy i)

end Dvr

end Formalism.MainNotions.N.FrobeniusPowerSeries.GS
