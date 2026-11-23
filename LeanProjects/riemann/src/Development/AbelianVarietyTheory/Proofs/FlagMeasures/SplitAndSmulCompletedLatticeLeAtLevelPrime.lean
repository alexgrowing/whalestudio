import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.LocCong

set_option maxHeartbeats 1000000 in

theorem qsmul_latP_le_gS : ∀ (D : D7) (Z : LocDat D) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ sg : Loc.SplitG (Z.M (below D P)).L, (Z.M (below D P)).split = some sg ∧ ∀ (Λ : LV D) (v : Vp D (below D P)), v ∈ (locH Z (below D P)).smulLat (algebraMap (D.s.atP (below D P)).Fp (D.s.atP (below D P)).Ep (sg.q : (D.s.atP (below D P)).Fp)) (lattice₂ D Z.M (below D P) Λ) → v ∈ lattice₂ D Z.M (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D Z P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  obtain ⟨j, hne, hgg⟩ : ∃ j : Fin 2, D.host.g i ≠ D.host.g j ∧ gS D = D.host.g i * D.host.g j := by
    fin_cases i
    · exact ⟨1, D.host.g_ne, rfl⟩
    · exact ⟨0, D.host.g_ne.symm, by simp [gS, mul_comm]⟩
  have hsome : (D.s.atP p).split.isSome := (D.s_split p).2 (by
    rw [hchar]; fin_cases i <;> simp)
  obtain ⟨sg0, hsg0⟩ := Option.isSome_iff_exists.1 hsome
  have hag := (Z.agree p).2.2.2.2.2
  rcases hZs : (Z.M p).split with _ | sg
  · rw [hZs, hsg0] at hag; exact hag.elim
  rw [hZs, hsg0] at hag
  refine ⟨sg, rfl, ?_⟩
  have hq : ((sg.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) := by
    rw [hag.2, sg0.q_eq, hchar]
  have hqO : (sg.q : 𝒪[(D.s.atP p).Fp]) = ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    apply Subtype.ext; rw [hq]; push_cast; rfl
  have hcop : Nat.Coprime (D.host.g i) (D.host.g j) :=
    (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hne
  have hbez : (1 : ℤ) = (D.host.g i : ℤ) * Int.gcdA (D.host.g i) (D.host.g j) +
      (D.host.g j : ℤ) * Int.gcdB (D.host.g i) (D.host.g j) := by
    have := Int.gcd_eq_gcd_ab (D.host.g i : ℤ) (D.host.g j : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at this
    exact_mod_cast this
  have hunit : IsUnit ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) := by
    have hqn : ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) ∈ IsLocalRing.maximalIdeal 𝒪[(D.s.atP p).Fp] := by
      rw [← hqO]; exact sg.q_irr.not_isUnit
    have h1 : IsUnit (1 - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp])) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right _ _ hqn)
    have h2 : (1 : 𝒪[(D.s.atP p).Fp]) - ((D.host.g i : ℕ) : 𝒪[(D.s.atP p).Fp]) *
        (Int.gcdA (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) =
        ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) * (Int.gcdB (D.host.g i) (D.host.g j) : 𝒪[(D.s.atP p).Fp]) := by
      have := congrArg (Int.cast : ℤ → 𝒪[(D.s.atP p).Fp]) hbez
      push_cast at this
      rw [this]; ring
    rw [h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨w, hw⟩ : ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp) = 1 := by
    refine ⟨((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_⟩
    have h1 : ((hunit.unit⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]) * ((D.host.g j : ℕ) : 𝒪[(D.s.atP p).Fp]) = 1 := by
      have := hunit.unit.inv_mul
      rwa [IsUnit.unit_spec] at this
    have h2 := congrArg Subtype.val h1
    exact_mod_cast h2
  have hwO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) ∈ (Z.M p).L.O := by
    rw [(Z.agree p).2.2.2.1, (D.s.atP p).O_def]
    exact isIntegral_algebraMap
  have hsc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (w : (D.s.atP p).Fp) * ((gS D : ℕ) : (D.s.atP p).Ep) := by
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, hq, hgg]
    congr 1
    push_cast
    calc ((D.host.g i : ℕ) : (D.s.atP p).Fp) = ((D.host.g i : ℕ) : (D.s.atP p).Fp) * ((w : (D.s.atP p).Fp) * ((D.host.g j : ℕ) : (D.s.atP p).Fp)) := by rw [hw, mul_one]
      _ = _ := by ring
  intro Λ v hv
  unfold Loc.HermSp.smulLat at hv
  refine (Submodule.span_le.2 ?_) hv
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hsc, mul_smul]
    have e : ((gS D : ℕ) : (D.s.atP p).Ep) • baseChange₂ D p x = baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • x) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [e]
    exact (lattice₂ D Z.M p _).smul_mem (⟨_, hwO⟩ : (Z.M p).L.O)
      (Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx, rfl⟩)
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o y _ hy =>
    have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • (o • y) =
        o • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (sg.q : (D.s.atP p).Fp) • y) := by
      show _ • ((o : (D.s.atP p).Ep) • y) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hy

end GlobalTheory.LocCong
