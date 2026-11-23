import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntSmulMemAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

section Idx

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {W : Type} [AddCommGroup W] [Module (Fv F v) W]

theorem sdc_unifEx_holds : UnifEx v := ⟨unifV v, by rw [IsUnif, unifV_val]; rfl⟩

theorem smulSub_smulSub (s t : Fv F v) (P : AddSubgroup W) :
    smulSub s (smulSub t P) = smulSub (s * t) P := by
  ext z
  simp only [mem_smulSub]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [smul_smul]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨t • p, ⟨p, hp, rfl⟩, by rw [smul_smul]⟩

theorem smulSub_one (P : AddSubgroup W) : smulSub (1 : Fv F v) P = P := by
  ext z
  simp [mem_smulSub]

theorem relIndex_smulSub {t : Fv F v} (ht : t ≠ 0) (H G : AddSubgroup W) :
    (smulSub t H).relIndex (smulSub t G) = H.relIndex G :=
  AddSubgroup.relIndex_map_map_of_injective H G (smul_right_injective W ht)

theorem smulSub_le {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub s P ≤ P := by
  intro z hz
  rw [mem_smulSub] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact hP s hs p hp

theorem smulSub_unit {u : Fv F v} (hu : u ∈ v.adicCompletionIntegers F)
    (hu' : u⁻¹ ∈ v.adicCompletionIntegers F) (hu0 : u ≠ 0) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub u P = P := by
  apply le_antisymm (smulSub_le v hu P hP)
  intro z hz
  rw [mem_smulSub]
  exact ⟨u⁻¹ • z, hP _ hu' z hz, by rw [smul_smul, mul_inv_cancel₀ hu0, one_smul]⟩

theorem relIndex_pow {ϖ : Fv F v} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ v.adicCompletionIntegers F)
    (P : AddSubgroup W) (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (k : ℕ) :
    (smulSub (ϖ ^ k) P).relIndex P = ((smulSub ϖ P).relIndex P) ^ k := by
  induction k with
  | zero => simp [smulSub_one]
  | succ k ih =>
    have e : smulSub (ϖ ^ (k + 1)) P = smulSub (ϖ ^ k) (smulSub ϖ P) := by
      rw [smulSub_smulSub, pow_succ]
    have h2 : smulSub (ϖ ^ k) P ≤ P := smulSub_le v (pow_mem hϖ k) P hP
    have h1 : smulSub (ϖ ^ k) (smulSub ϖ P) ≤ smulSub (ϖ ^ k) P := by
      intro z hz
      rw [mem_smulSub] at hz ⊢
      obtain ⟨p, hp, rfl⟩ := hz
      exact ⟨p, smulSub_le v hϖ P hP hp, rfl⟩
    rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2, relIndex_smulSub v (pow_ne_zero k hϖ0), ih]
    ring

theorem exists_unit_pow {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {d : Fv F v} (hd0 : d ≠ 0)
    (hd : d ∈ v.adicCompletionIntegers F) :
    ∃ k : ℕ, ∃ u : Fv F v, u ∈ v.adicCompletionIntegers F ∧ u⁻¹ ∈ v.adicCompletionIntegers F ∧
      u ≠ 0 ∧ d = ϖ ^ k * u ∧ absV v d = qv v ^ (-(k : ℤ)) := by
  have hϖ0 := unif_ne_zero v hϖ
  have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hv) with hmdef
  have hvm : Valued.v d = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [m]
  have hm : m ≤ 0 := by
    have h1 : Valued.v d ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd
      exact hd
    rw [hvm] at h1
    have h2 : (Multiplicative.ofAdd m : Multiplicative ℤ) ≤ 1 := by exact_mod_cast h1
    rw [← ofAdd_zero] at h2
    exact Multiplicative.ofAdd_le.1 h2
  have hk : ((m.natAbs : ℕ) : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm
  have hvk : Valued.v (ϖ ^ m.natAbs) = Valued.v d := by
    rw [map_pow, hϖ, hvm, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 2
    rw [nsmul_eq_mul, hk]
    ring
  have hϖk : ϖ ^ m.natAbs ≠ 0 := pow_ne_zero _ hϖ0
  have hu1 : Valued.v ((ϖ ^ m.natAbs)⁻¹ * d) = 1 := by
    rw [map_mul, map_inv₀, hvk, inv_mul_cancel₀ hv]
  refine ⟨m.natAbs, (ϖ ^ m.natAbs)⁻¹ * d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu1, inv_one]
  · exact mul_ne_zero (inv_ne_zero hϖk) hd0
  · rw [← mul_assoc, mul_inv_cancel₀ hϖk, one_mul]
  · unfold absV
    rw [dif_neg hv]
    unfold qv
    congr 1
    rw [hk]
    simp [m]

end Idx

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E))

def IdxPiW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
      ((smulSub ϖ (LW v Λ a)).relIndex (LW v Λ a) : ℝ) = qv v ^ (2 * n * a)

def IdxPiH (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem relIndex_dV {W : Type} [AddCommGroup W] [Module (Fv F v) W] (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (N : ℕ) (e : ℝ)
    (hN : ∀ ϖ : Fv F v, IsUnif v ϖ → ((smulSub ϖ P).relIndex P : ℝ) = qv v ^ N)
    (he : e = -(N : ℝ)) :
    (P.relIndex (smulSub (dV v)⁻¹ P) : ℝ) = absV v (dV v) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := sdc_unifEx_holds v
  have hd0 := dV_ne_zero v
  obtain ⟨k, u, hu, hu', hu0, hd, habs⟩ := exists_unit_pow v hϖ hd0 (dV_int v)
  have e1 : P.relIndex (smulSub (dV v)⁻¹ P) = (smulSub ϖ P).relIndex P ^ k := by
    rw [← relIndex_smulSub v hd0, smulSub_smulSub, mul_inv_cancel₀ hd0, smulSub_one, hd,
      ← smulSub_smulSub, smulSub_unit v hu hu' hu0 P hP,
      relIndex_pow v (unif_ne_zero v hϖ) (unif_int v hϖ) P hP]
  rw [e1, Nat.cast_pow, hN ϖ hϖ, habs, he]
  have hq := qv_pos v
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← pow_mul, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem idxW_of (a : ℕ) (h : IdxPiW v Λ a) : IdxW v Λ a := by
  intro hL hU
  exact relIndex_dV v (LW v Λ a) (fun s hs x hx => smul_mem_LW v Λ hs hx) (2 * n * a) _
    (fun ϖ hϖ => h hL hU ϖ hϖ) (by push_cast; ring)

theorem idxHO_of (a : ℕ) (h : IdxPiH σ v a) : IdxHO σ v a := by
  intro hU ϖ hϖ
  refine ⟨relIndex_dV v (HO σ v a) (fun s hs x hx => smul_mem_HO σ v hs hx) (a ^ 2) _
    (fun ϖ hϖ => h hU ϖ hϖ) (by push_cast; ring), h hU ϖ hϖ⟩

end Steps

end PI.OmLocU
