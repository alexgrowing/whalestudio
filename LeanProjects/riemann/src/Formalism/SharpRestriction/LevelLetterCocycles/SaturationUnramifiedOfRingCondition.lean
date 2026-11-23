import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.SatW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Ring

variable {O : Type} [CommRing O] {n : ℕ}

def UPi (p : ℕ) (g : LetA O n) : Prop :=
  ∃ (u : (LetA O n)ˣ) (m : ℕ) (r : LetA O n), g = (u : LetA O n) * letπ ^ m + ((p : ℕ) : LetA O n) * r

theorem UPi.mul {p : ℕ} {g h : LetA O n} (hg : UPi p g) (hh : UPi p h) : UPi p (g * h) := by
  obtain ⟨u, m, r, rfl⟩ := hg
  obtain ⟨u', m', r', rfl⟩ := hh
  refine ⟨u * u', m + m', (u : LetA O n) * letπ ^ m * r' + r * ((u' : LetA O n) * letπ ^ m') +
    ((p : ℕ) : LetA O n) * r * r', ?_⟩
  rw [Units.val_mul, pow_add]
  ring

theorem UPi.unit (p : ℕ) (u : (LetA O n)ˣ) : UPi p (u : LetA O n) := by
  refine ⟨u, 0, 0, ?_⟩
  rw [pow_zero, mul_one, mul_zero, add_zero]

theorem UPi.one (p : ℕ) : UPi p (1 : LetA O n) := by
  have h := UPi.unit (O := O) (n := n) p 1
  rwa [Units.val_one] at h

theorem UPi.pow {p : ℕ} {g : LetA O n} (hg : UPi p g) (k : ℕ) : UPi p (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact UPi.one p
  | succ k ih => rw [pow_succ]; exact ih.mul hg

theorem UPi.add_p {p : ℕ} {g : LetA O n} (hg : UPi p g) : UPi p (g + ((p : ℕ) : LetA O n)) := by
  obtain ⟨u, m, r, rfl⟩ := hg
  exact ⟨u, m, r + 1, by ring⟩

theorem UPi.prod {p : ℕ} {ι : Type} (s : Finset ι) (g : ι → LetA O n) (hg : ∀ i ∈ s, UPi p (g i)) :
    UPi p (∏ i ∈ s, g i) := by
  exact Finset.prod_induction g (UPi p) (fun a b ha hb => ha.mul hb) (UPi.one p) hg

theorem p_cancel {p : ℕ} (hO : ∀ c : O, ((p : ℕ) : O) * c = 0 → c = 0) {a b : LetA O n}
    (h : ((p : ℕ) : LetA O n) * a = ((p : ℕ) : LetA O n) * b) : a = b := by
  have h1 : ((p : ℕ) : LetA O n) * (a - b) = 0 := by rw [mul_sub, h, sub_self]
  rw [← sub_eq_zero]
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.sub_apply, Pi.zero_apply] at h2
  simp only [Pi.sub_apply, Pi.zero_apply]
  refine PowerSeries.ext fun k => ?_
  have h3 := (PowerSeries.ext_iff.mp h2) k
  rw [← nsmul_eq_mul, map_nsmul, map_zero, nsmul_eq_mul] at h3
  rw [map_zero]
  exact hO _ h3

theorem p_pow_cancel {p : ℕ} (hO : ∀ c : O, ((p : ℕ) : O) * c = 0 → c = 0) (k : ℕ) {a b : LetA O n}
    (h : ((p : ℕ) : LetA O n) ^ k * a = ((p : ℕ) : LetA O n) ^ k * b) : a = b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply p_cancel hO
    rw [← mul_assoc, ← mul_assoc, ← pow_succ']
    exact h

theorem dvd_of_X_pow {p : ℕ} {m : ℕ} {a c : LetA O n}
    (h : ((p : ℕ) : LetA O n) * c = letπ ^ m * a) : ∃ a' : LetA O n, a = ((p : ℕ) : LetA O n) * a' := by
  refine ⟨fun i => PowerSeries.mk fun k => PowerSeries.coeff (R := O) (k + m) (c i), ?_⟩
  funext i
  have h2 := congrFun h i
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, letπ] at h2
  refine PowerSeries.ext fun k => ?_
  have h3 := (PowerSeries.ext_iff.mp h2) (k + m)
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, PowerSeries.coeff_X_pow_mul] at h3
  simp only [Pi.mul_apply, Pi.natCast_apply]
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, PowerSeries.coeff_mk, h3]

theorem dvd_of_UPi {p : ℕ} (hO : ∀ c : O, ((p : ℕ) : O) * c = 0 → c = 0) {g : LetA O n}
    (hg : UPi p g) (k : ℕ) : ∀ (a c : LetA O n), ((p : ℕ) : LetA O n) ^ k * c = g * a →
      ∃ a' : LetA O n, a = ((p : ℕ) : LetA O n) ^ k * a' := by
  obtain ⟨u, m, r, rfl⟩ := hg
  induction k with
  | zero => intro a c _; exact ⟨a, by rw [pow_zero, one_mul]⟩
  | succ k ih =>
    intro a c h
    have h1 : ((p : ℕ) : LetA O n) * (((p : ℕ) : LetA O n) ^ k * c - r * a) =
        letπ ^ m * ((u : LetA O n) * a) := by
      rw [mul_sub, ← mul_assoc, ← pow_succ', h]
      ring
    obtain ⟨a1, ha1⟩ := dvd_of_X_pow h1
    have ha : a = ((p : ℕ) : LetA O n) * ((↑u⁻¹ : LetA O n) * a1) := by
      rw [mul_left_comm, ← ha1, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 : ((p : ℕ) : LetA O n) ^ k * c =
        ((u : LetA O n) * letπ ^ m + ((p : ℕ) : LetA O n) * r) * ((↑u⁻¹ : LetA O n) * a1) := by
      apply p_cancel hO
      rw [← mul_assoc, ← pow_succ', h, ha]
      ring
    obtain ⟨a', ha'⟩ := ih _ _ h2
    exact ⟨a', by rw [ha, ha', ← mul_assoc, ← pow_succ']⟩

end Ring

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem p_nzd_O (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL)) (c : O)
    (h : ((PD.p : ℕ) : O) * c = 0) : c = 0 := by
  have hp : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := W.v_l
    rw [h0, AddValuation.map_zero] at h1
    simp at h1
  have h2 : algebraMap O LL (((PD.p : ℕ) : O) * c) = 0 := by rw [h, map_zero]
  rw [map_mul, map_natCast] at h2
  have h3 : algebraMap O LL c = 0 := (mul_eq_zero.mp h2).resolve_left hp
  exact hinj (by rw [h3, map_zero])

theorem isUnit_one_add_p (W : LocWach PD LL O v n) (y : W.EE) :
    IsUnit (1 + ((PD.p : ℕ) : W.EE) * y) := by
  haveI := W.EE_complete
  have hp : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  have h := Ideal.mem_jacobson_bot.mp hp y
  rwa [add_comm] at h

theorem isUnit_EE_of_UPi (W : LocWach PD LL O v n) {g : LetA O n} (hg : UPi PD.p g) :
    IsUnit (algebraMap (LetA O n) W.EE g) := by
  obtain ⟨u, m, r, rfl⟩ := hg
  have hU : IsUnit (algebraMap (LetA O n) W.EE ((u : LetA O n) * letπ ^ m)) := by
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (W.EE_π.pow m)
  obtain ⟨U, hU'⟩ := hU
  have key : (U : W.EE) * ((↑U⁻¹ : W.EE) * algebraMap (LetA O n) W.EE r) =
      algebraMap (LetA O n) W.EE r := Units.mul_inv_cancel_left U _
  have e : algebraMap (LetA O n) W.EE ((u : LetA O n) * letπ ^ m + ((PD.p : ℕ) : LetA O n) * r) =
      (U : W.EE) * (1 + ((PD.p : ℕ) : W.EE) * ((↑U⁻¹ : W.EE) * algebraMap (LetA O n) W.EE r)) := by
    rw [map_add, ← hU', map_mul, map_natCast, mul_add, mul_one, mul_left_comm (U : W.EE), key]
  rw [e]
  exact U.isUnit.mul (isUnit_one_add_p W _)

theorem smul_cancel (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {g : LetA O n}
    (hg : IsUnit (algebraMap (LetA O n) W.EE g)) {x y : W.DD T} (h : g • x = g • y) : x = y := by
  rw [← algebraMap_smul W.EE g x, ← algebraMap_smul W.EE g y] at h
  exact hg.smul_left_cancel.mp h

theorem γD_smulA' (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n)
    (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem smul_mem_NΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {a : LetA O n} (ha : a ∈ W.AΔ)
    {b : W.DD T} (hb : b ∈ W.NΔ T) : a • b ∈ W.NΔ T := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hb' : b ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ b = b := hb
  show a • b ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (a • b) = a • b
  refine ⟨(W.N T).smul_mem a hb'.1, fun δ hδ => ?_⟩
  rw [γD_smulA' W T δ a b, ha' δ hδ, hb'.2 δ hδ]

theorem mem_AΔ_of_p_pow (W : LocWach PD LL O v n) (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    (k : ℕ) {a : LetA O n} (ha : ((PD.p : ℕ) : LetA O n) ^ k * a ∈ W.AΔ) : a ∈ W.AΔ := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ (((PD.p : ℕ) : LetA O n) ^ k * a) =
      ((PD.p : ℕ) : LetA O n) ^ k * a := ha
  show ∀ δ ∈ W.DelF, W.γA δ a = a
  intro δ hδ
  have h1 := ha' δ hδ
  rw [map_mul, map_pow, map_natCast] at h1
  exact p_pow_cancel hO k h1

theorem sat_basis (W : LocWach PD LL O v n) (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    (T : LocLat G Qp LL O) {r : ℕ} (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.NΔ T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hΔ : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, a j ∈ W.AΔ) ∧ x = ∑ j, a j • b j)
    {f f' : LetA O n} (hf : UPi PD.p f) (hf' : UPi PD.p f') (x : W.DD T) (hx : f' • x ∈ W.NΔ T)
    (k : ℕ) (y : W.DD T) (hy : y ∈ W.NΔ T) (hk : ((PD.p : ℕ) : LetA O n) ^ k • x = f • y) :
    ∃ z ∈ W.NΔ T, x = f • z := by
  classical
  have hx' : f' • x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (f' • x) = f' • x := hx
  obtain ⟨a, haΔ, hya⟩ := hΔ y hy
  obtain ⟨c, -, hxc⟩ := hΔ (f' • x) hx
  have hmem : (((PD.p : ℕ) : LetA O n) ^ k) • (f' • x) ∈ W.N T := (W.N T).smul_mem _ hx'.1
  have e1 : (((PD.p : ℕ) : LetA O n) ^ k) • (f' • x) =
      ∑ j, (((PD.p : ℕ) : LetA O n) ^ k * c j) • b j := by
    rw [hxc, Finset.smul_sum]
    simp only [smul_smul]
  have e2 : (((PD.p : ℕ) : LetA O n) ^ k) • (f' • x) = ∑ j, (f' * f * a j) • b j := by
    rw [smul_smul, mul_comm _ f', ← smul_smul, hk, hya, smul_smul, Finset.smul_sum]
    simp only [smul_smul]
  obtain ⟨a0, -, huq⟩ := huniq _ hmem
  have hca : ∀ j, ((PD.p : ℕ) : LetA O n) ^ k * c j = f' * f * a j := by
    intro j
    have q1 := huq (fun j => ((PD.p : ℕ) : LetA O n) ^ k * c j) e1
    have q2 := huq (fun j => f' * f * a j) e2
    exact congrFun (q1.trans q2.symm) j
  have hdiv : ∀ j, ∃ a' : LetA O n, a j = ((PD.p : ℕ) : LetA O n) ^ k * a' :=
    fun j => dvd_of_UPi hO (UPi.mul hf' hf) k (a j) (c j) (hca j)
  choose a' ha' using hdiv
  have ha'Δ : ∀ j, a' j ∈ W.AΔ := fun j =>
    mem_AΔ_of_p_pow W hO k (by rw [← ha' j]; exact haΔ j)
  refine ⟨∑ j, a' j • b j, sum_mem fun j _ => smul_mem_NΔ W T (ha'Δ j) (hb j), ?_⟩
  apply smul_cancel W T (isUnit_EE_of_UPi W hf')
  rw [hxc, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  apply p_pow_cancel hO k
  rw [hca j, ha' j]
  ring

end Core

end Formalism.MainNotions.UnusedSlot80.SatW

namespace Formalism.MainNotions.UnusedSlot80.SatW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Inst

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem Eat_π₀ (W : LocWach PD LL O v n) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      W.π₀ + ((PD.p : ℕ) : LetA O n) := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]

theorem UPi_φpow (W : LocWach PD LL O v n)
    (h3 : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (h6 : ∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * (W.π₀ + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1))
    (s : ℕ) : UPi PD.p ((W.φA ^ s) W.π₀) := by
  obtain ⟨w, hw⟩ := h6
  induction s with
  | zero =>
    rw [pow_zero, AlgHom.one_apply]
    obtain ⟨w0, hw0⟩ := h3
    exact ⟨w0, PD.p - 1, 0, by rw [hw0, mul_zero, add_zero]⟩
  | succ s ih =>
    rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul, map_pow, map_add, map_natCast]
    obtain ⟨w', hw'⟩ := w.isUnit.map (W.φA ^ s)
    rw [← hw']
    exact ((UPi.unit _ w').mul ih).mul (ih.add_p.pow _)

theorem UPi_qpow (W : LocWach PD LL O v n)
    (h3 : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (h6 : ∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * (W.π₀ + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1))
    (s : ℕ) : UPi PD.p ((W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  rw [map_add, map_natCast]
  exact (UPi_φpow W h3 h6 s).add_p

theorem UPi_π₀ (W : LocWach PD LL O v n)
    (h3 : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) : UPi PD.p W.π₀ := by
  obtain ⟨w, hw⟩ := h3
  exact ⟨w, PD.p - 1, 0, by rw [hw, mul_zero, add_zero]⟩

theorem ring_clauses (W : LocWach PD LL O v n)
    (h : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) :
    (∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) ∧
    (∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * (W.π₀ + ((PD.p : ℕ) : LetA O n)) ^ (PD.p - 1)) := by
  obtain ⟨-, -, h3, -, -, h6, -, -⟩ := h
  refine ⟨h3, ?_⟩
  obtain ⟨w, hw⟩ := h6
  exact ⟨w, by rw [hw, Eat_π₀ W]⟩

theorem finrank_one_of_bij' (h : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 := by
  exact (AlgEquiv.ofBijective (Algebra.ofId K₀ K) h).toLinearEquiv.finrank_eq.symm.trans
    (Module.finrank_self K₀)

theorem satCore_of (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL))
    (h9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p9 W T) : Formalism.MainNotions.ArcLiftingSetup.SATcore W := by
  rintro ⟨hbij, hs, hp⟩ T f f' hT hf hf' x hx ⟨k, y, hy, hyk⟩
  obtain ⟨-, -, h1⟩ := h9 T hT hs hp
  obtain ⟨hring, hmod⟩ := h1 (finrank_one_of_bij' hbij)
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, -⟩ := hmod
  have hUP : ∀ g ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W, UPi PD.p g := by
    intro g hg
    let S : Submonoid (LetA O n) :=
      { carrier := {g | UPi PD.p g}
        mul_mem' := fun ha hb => UPi.mul ha hb
        one_mem' := UPi.one PD.p }
    have hsub : insert W.π₀ (Set.range (Formalism.MainNotions.ArcLiftingSetup.ps W)) ⊆ (S : Set (LetA O n)) := by
      rintro g (rfl | ⟨s, rfl⟩)
      · exact UPi_π₀ W h3
      · exact UPi_qpow W h3 h6 s
    exact (Submonoid.closure_le.mpr hsub) hg
  exact sat_basis W (p_nzd_O W hinj) T b hb huniq hΔ (hUP f hf) (hUP f' hf') x hx k y hy hyk

theorem sat_of (W : LocWach PD LL O v n) (hinj : Function.Injective (algebraMap O LL)) (hs : W.s = 1)
    (hp : PD.p ≠ 2) (hK : Module.finrank K₀ K = 1)
    (h9 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p9 W T) : Formalism.MainNotions.WachCoordinates.Sat W := by
  rintro T f f' hT hf hf' x - hx ⟨k, y, hy, hyk⟩
  obtain ⟨-, -, h1⟩ := h9 T hT hs hp
  obtain ⟨hring, hmod⟩ := h1 hK
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, -⟩ := hmod
  have hUP : ∀ g, Formalism.MainNotions.WachCoordinates.IsPiPs W g → UPi PD.p g := by
    rintro g ⟨e, g', ⟨kk, m, rfl⟩, rfl⟩
    exact (UPi.pow (UPi_π₀ W h3) e).mul
      (UPi.prod _ _ fun s _ => (UPi_qpow W h3 h6 s).pow (kk s))
  exact sat_basis W (p_nzd_O W hinj) T b hb huniq hΔ (hUP f hf) (hUP f' hf') x hx k y hy hyk

end Inst

end Formalism.MainNotions.UnusedSlot80.SatW

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem saturation_general_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : SaturationArcLifting D HW F := by
  intro l _ K LL hG _ _
  exact SatW.satCore_of _ (fun a b hab => Subtype.ext hab) (h9 l K 1 LL hG)

theorem saturation_unramified_of_ring_condition (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : SaturationEtale D HW F := by
  intro l _ K LL h h5
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective,
      fun y => ⟨⟨y.1, IntermediateField.mem_inf.mpr ⟨y.2, h.1 y.2⟩⟩, Subtype.ext rfl⟩⟩
  exact SatW.sat_of _ (fun a b hab => Subtype.ext hab) ((HW l).W_s K 1 LL h.2.2)
    (fun e => h.2.1 (((D.loc l).PD_p K).symm.trans e)) (SatW.finrank_one_of_bij' hbij) (h9 l K 1 LL h.2.2)

theorem saturation_general_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SaturationTheoremArcLifting D HW F := fun h => saturation_general_of_ring_condition D HW F h.2

theorem saturation_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SaturationTheoremEtale D HW F := fun h => saturation_unramified_of_ring_condition D HW F h.2

end Formalism.MainNotions.UnusedSlot80
