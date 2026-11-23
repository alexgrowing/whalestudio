import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatSmulMemOfFg

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.CommonRef

section

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] [Module E W] [IsScalarTower (𝓞 E) E W]

theorem exists_nat_mul_integral (a : E) : ∃ n : ℕ, 0 < n ∧ ∃ r : 𝓞 E, (n : E) * a = algebraMap (𝓞 E) E r := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_natCast] at this
      rwa [this] at hint
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [this, neg_mul] at hint
      simpa using hint.neg
  exact ⟨⟨_, h2⟩, rfl⟩

theorem full_of_span {M : Submodule (𝓞 E) W} (hM : Submodule.span E (M : Set W) = ⊤) : Full M := by
  intro x
  have hx : x ∈ Submodule.span E (M : Set W) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, r, hr⟩ := exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : 𝓞 E) • a • x = r • (n : 𝓞 E) • x := by
      simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_natCast, ← hr]
      congr 1
      push_cast
      ring
    rw [this]
    exact M.smul_mem _ hx

omit [Module E W] [IsScalarTower (𝓞 E) E W] in
theorem exists_nat_smul_le {M N : Submodule (𝓞 E) W} (hM : Full M) (hN : N.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : 𝓞 E) • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | (apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg ..)

theorem smul_mem_locP {M N : Submodule (𝓞 E) W} {m : ℕ} (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (Q : HeightOneSpectrum (𝓞 E))
    {x : W} (hx : x ∈ localization₂ Q.asIdeal N) : (m : E) • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := h _ hx
  rwa [smul_comm, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem mem_localization_of_inv_smul_mem {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : (m : E)⁻¹ • x ∈ localization₂ Q.asIdeal N) : x ∈ localization₂ Q.asIdeal M := by
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_mem_locP h Q hx
  rwa [smul_smul, mul_inv_cancel₀ hmE, one_smul] at this

theorem dom_twO [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m)
    (h₁ : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (h₂ : ∀ x ∈ M, (m : 𝓞 E) • x ∈ N)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N) :
    Dom S M (twist₂ N m (expS S)) ∧ Dom S (twist₂ N m fun Q => -expS S Q) M := by
  have hb := expS_bound S
  have hb' : ∀ Q, -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := fun Q => by have := hb Q; omega
  refine ⟨⟨fun P hP x hx => ?_, fun Q hS x hx => ?_⟩, fun P hP x hx => ?_, fun Q hS x hx => ?_⟩
  · rw [mem_localization_twist N hm hb] at hx
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_one] at hx
    exact mem_localization_of_inv_smul_mem hm h₁ P hx
  · rw [mem_localization_twist N hm hb]
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, zpow_neg_one, inv_inv]
      exact smul_mem_locP h₂ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, zpow_zero, inv_one, one_smul, ← hQ Q hS hc]
      exact hx
  · rw [mem_localization_twist N hm hb']
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_neg_one, inv_inv]
    exact smul_mem_locP h₂ P hx
  · rw [mem_localization_twist N hm hb'] at hx
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, neg_neg, zpow_one] at hx
      exact mem_localization_of_inv_smul_mem hm h₁ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, neg_zero, zpow_zero, inv_one, one_smul, ← hQ Q hS hc] at hx
      exact hx

end

theorem common_refinement : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (M₁ M₂ : Submodule (𝓞 E) (Sp E n)) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat M₁ → IsSdLat M₂ → (∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M₁ = localization₂ Q.asIdeal M₂) → ∃ F G : Submodule (𝓞 E) (Sp E n), IsSdLat F ∧ IsSdLat G ∧ Dom S M₁ F ∧ Dom S M₂ F ∧ Dom S G M₁ ∧ Dom S G M₂ := by
  intro E _ _ _ n M₁ M₂ S hS h₁ h₂ hQ
  obtain ⟨a, ha, hA⟩ := exists_nat_smul_le (full_of_span h₁.1.span_eq_top) h₂.1.fg
  obtain ⟨b, hb, hB⟩ := exists_nat_smul_le (full_of_span h₂.1.span_eq_top) h₁.1.fg
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hA' : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₁ := fun x hx => by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact M₁.smul_mem _ (hA x hx)
  have hB' : ∀ x ∈ M₁, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => by
    rw [Nat.cast_mul, mul_smul]; exact M₂.smul_mem _ (hB x hx)
  have hC : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => M₂.smul_mem _ hx
  obtain ⟨hF, hG⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS E n M₂ (a * b) S hS h₂ hm
  obtain ⟨d₁, d₂⟩ := dom_twO S hm hA' hB' hQ
  obtain ⟨d₃, d₄⟩ := dom_twO S hm hC hC fun _ _ _ => rfl
  exact ⟨_, _, hF, hG, d₁, d₃, d₂, d₄⟩

end GlobalTheory.ThetaMove.CommonRef
