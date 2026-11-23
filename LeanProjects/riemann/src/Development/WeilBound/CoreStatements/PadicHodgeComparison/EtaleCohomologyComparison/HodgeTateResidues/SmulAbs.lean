import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RhoExA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb

namespace RhoA

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ok_dv (a : OK l K) (ha : a ≠ 0) : ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  have h0 : 0 < ‖((a : K) : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast ha')
  have e : (((l : ℕ) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  have h1 : ‖(((l : ℕ) : K) : PadicAlgCl l)‖ < 1 := by
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨k, ⟨(a : K)⁻¹ * (l : K) ^ k, (mem_OK _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow, norm_mul, norm_inv, norm_pow]
    rw [inv_mul_le_iff₀ h0, mul_one]
    exact hk.le
  · change (((l : OK l K) ^ k : OK l K) : K) = (a : K) * ((a : K)⁻¹ * (l : K) ^ k)
    rw [mul_inv_cancel_left₀ ha']
    simp

theorem tf_dom {O : Type} [CommRing O] [IsDomain O] [CharZero O] {l : ℕ} (hl : l ≠ 0)
    (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s := by
  have hb : ∀ r, 1 ≤ r → pdP (dividedPowersBot O) r = ⊥ := fun r hr => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    refine le_bot_iff.1 (le_trans ?_ (GlobalTheory.CompanionTheory.LiftLat.dividedPowerFiltration_one_eq (dividedPowersBot O)).le)
    refine Ideal.span_mono ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact ⟨L, h1, by omega, rfl⟩
  refine ⟨hb s hs, fun r x hx => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x this
    · rw [hb r hr, Ideal.mem_bot] at hx ⊢
      exact (mul_eq_zero.1 hx).resolve_left (Nat.cast_ne_zero.2 hl)
  · obtain ⟨k, u, hu⟩ := hdv n (Nat.cast_ne_zero.2 hn)
    exact ⟨k, u, hu.symm⟩

section Abs
variable {A B Λ : Type} [CommRing A] [CommRing B] [CommRing Λ] {ι : A →+* B} {Z W : Type 1} [AddCommGroup Z] [Module A Z]
  [AddCommGroup W] [Module B W] (b : Z →ₛₗ[ι] W) {Zn : ℕ → Type 1} [∀ n, AddCommGroup (Zn n)] [∀ n, Module A (Zn n)]
  (red : ∀ n, Z →ₗ[A] Zn n) (l : ℕ)

theorem b_pow (e : ℕ) (z : Z) : b ((l : A) ^ e • z) = (l : B) ^ e • b z := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]

theorem exu (hu : IsUnit (l : B)) (x : ∀ n, Zn n) (e₀ : ℕ) (z₀ : Z) (h₀ : ∀ n, red n z₀ = (l : A) ^ e₀ • x n) (k : ℕ)
    (hs : ∀ z, (∀ n, red n z = 0) → (l : A) ^ k • z = 0) :
    ∃! w : W, ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z := by
  have key : ∀ (w w' : W) e z e' z', (∀ n, red n z = (l : A) ^ e • x n) → (l : B) ^ e • w = b z →
      (∀ n, red n z' = (l : A) ^ e' • x n) → (l : B) ^ e' • w' = b z' → w = w' := by
    intro w w' e z e' z' h1 h2 h3 h4
    have h5 := hs ((l : A) ^ e' • z - (l : A) ^ e • z') fun n => by
      rw [map_sub, map_smul, map_smul, h1, h3, smul_comm, sub_self]
    have h6 := congrArg b h5
    rw [b_pow, map_sub, b_pow, b_pow, ← h2, ← h4, map_zero, smul_comm ((l : B) ^ e) ((l : B) ^ e') w', ← smul_sub, ← smul_sub,
      smul_smul, smul_smul] at h6
    exact sub_eq_zero.1 (((((hu.pow k).mul (hu.pow e')).mul (hu.pow e)).smul_eq_zero).1 h6)
  obtain ⟨u, hu'⟩ := (hu.pow e₀).exists_right_inv
  have hw : (l : B) ^ e₀ • (u • b z₀) = b z₀ := by rw [smul_smul, hu', one_smul]
  exact ⟨u • b z₀, ⟨e₀, z₀, h₀, hw⟩, fun w ⟨e, z, h1, h2⟩ => key _ _ _ _ _ _ h1 h2 h₀ hw⟩

theorem add_abs (x y : ∀ n, Zn n) (w w' : W) (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z)
    (h' : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • y n) ∧ (l : B) ^ e • w' = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (x n + y n)) ∧ (l : B) ^ e • (w + w') = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  obtain ⟨e', z', h3, h4⟩ := h'
  refine ⟨e + e', (l : A) ^ e' • z + (l : A) ^ e • z', fun n => ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, h1, h3, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : A) ^ e')]
  · rw [map_add, b_pow, b_pow, ← h2, ← h4, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : B) ^ e')]

theorem smul_abs (x : ∀ n, Zn n) (w : W) (a : A)
    (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (a • x n)) ∧ (l : B) ^ e • (ι a • w) = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  refine ⟨e, a • z, fun n => ?_, ?_⟩
  · rw [map_smul, h1, smul_comm]
  · rw [LinearMap.map_smulₛₗ, ← h2, smul_comm]

end Abs

variable {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

theorem unit_B : IsUnit (l : L.B) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) : IsUnit (l : K)).map (algebraMap K L.B)
  rwa [map_natCast] at this

theorem rS_tr (r j n : ℕ) (x : CH.H (Y.SS M r (n + 1)).fn j) :
    (L.rS M r n).pull j ((pdOm (Y.redM M n) (RingHom.id _) (Y.rd_c n) r).pull j x) =
      trG (L.QA M) (l : L.A) n r j ((L.rS M r (n + 1)).pull j x) :=
  sub_trans (L.d (n + 1)) (L.d n) m {⊤} (Y.redM M n) (Y.c (n + 1)) (Y.c n) L.lam (L.d_lam (n + 1)) (L.d_lam n) (Y.rd_c n)
    (fun _ _ => rfl) (Y.c_surj (n + 1)) r j x

theorem ex [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (r j : ℕ) (hr : r < m) (x : Y.Fam M r j) (hx : CB.Comp x) : ∃! w, L.Rho x w := by
  haveI := AdicGeo.proper_p hM.1
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  obtain ⟨k, h1, h2⟩ := lift_gr afgA L.γ l m ok_dv (tf_dom (Fact.out : l.Prime).ne_zero ok_dv (by omega)) L.lat M.p U r hr j
  obtain ⟨z, hz⟩ := h1 (fun n => (L.rS M r n).pull j (x n)) fun n =>
    (rS_tr L M r j n (x (n + 1))).symm.trans (congrArg ((L.rS M r n).pull j) (hx n))
  exact exu (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l (unit_B L) (fun n => (L.rS M r n).pull j (x n))
    (2 * k) z hz k h2

theorem add (r j : ℕ) (x y : Y.Fam M r j) (w w' : HG (L.QB M) r j) (h : L.Rho x w) (h' : L.Rho y w') : L.Rho (x + y) (w + w') := by
  obtain ⟨e, z, h1, h2⟩ := add_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) (fun n => (L.rS M r n).pull j (y n)) w w' h h'
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (map_add ((L.rS M r n).pull j) (x n) (y n)).symm), h2⟩

theorem smul (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) (w : HG (L.QB M) r j) (h : L.Rho x w) : L.Rho (c • x) (L.ι (L.lam c) • w) := by
  obtain ⟨e, z, h1, h2⟩ := smul_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) w (L.lam c) h
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (LinearMap.map_smulₛₗ ((L.rS M r n).pull j) c (x n)).symm), h2⟩

end RhoA

theorem rhoEx {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K] : RhoEx l K where
  ex L M hM r j hr x hx := RhoA.ex L M hM r j hr x hx
  add L M r j x y w w' := RhoA.add L M r j x y w w'
  smul L M r j c x w := RhoA.smul L M r j c x w

end CrystallineSemistableComparison.HT
