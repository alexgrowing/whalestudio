import Formalism.SharpRestriction.LevelLetterCocycles.IsUnitOfMk

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section LevRatPf

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem exists_dvd_pow_of_not_isUnit_dvr [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0) (hpu : ¬ IsUnit p)
    {y : O} (hy : y ≠ 0) : ∃ (κ : ℕ) (z : O), p ^ κ = y * z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  obtain ⟨e, u', hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hpe, h, pow_zero, mul_one]; exact u'.isUnit) hpu
    · exact h
  refine ⟨m, ((u⁻¹ : Oˣ) : O) * (u' : O) ^ m * ϖ ^ (e * m - m), ?_⟩
  have hm : m ≤ e * m := Nat.le_mul_of_pos_left m he
  rw [hpe, hyu, mul_pow, ← pow_mul]
  have e1 : ϖ ^ (e * m) = ϖ ^ m * ϖ ^ (e * m - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [e1]
  have e2 : ((u : O) * ((u⁻¹ : Oˣ) : O)) = 1 := Units.mul_inv u
  linear_combination (-((u' : O) ^ m * ϖ ^ m * ϖ ^ (e * m - m))) * e2

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem levRatPf_ev (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (g : LetA O n) :
    ∃ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      ∀ ζ : Rs hB.F PD.p s, hB.ev ζ g = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  refine ⟨r, hdeg, fun ζ => ?_⟩
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have h1 := congrArg (hB.ev ζ) key
  rw [map_mul, hB.ev_letE, one_mul, map_add, map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
    hB.ev_letE, one_mul, ev_aeval hB] at h1
  exact h1

theorem levRat_of [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hR : ToolsR.RingP W)
    (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ)
    (hB : LevBasics W a s) : LevRat W a s hB.F hB.ev := by
  intro g _ d _ hd c hc
  obtain ⟨rg, hgdeg, hg⟩ := levRatPf_ev W hR hT hpu a s hB g
  obtain ⟨rd, hddeg, hdv⟩ := levRatPf_ev W hR hT hpu a s hB d
  have hN : ∀ r : Polynomial O, r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) →
      (r.map (algebraMap O hB.F)).natDegree < (PD.p - 1) * PD.p ^ s := by
    intro r hr
    have hNpos : 0 < (PD.p - 1) * PD.p ^ s :=
      Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
    refine lt_of_le_of_lt Polynomial.natDegree_map_le ?_
    by_cases h0 : r = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hr
  set R : Polynomial hB.F := rg.map (algebraMap O hB.F) - Polynomial.C c * rd.map (algebraMap O hB.F) with hRdef
  have hR0 : R = 0 := by
    refine poly_eq_zero hB R ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt (hN rg hgdeg) ?_)
      exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (hN rd hddeg)
    · intro ζ
      rw [hRdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
        Polynomial.eval_map, ← Polynomial.aeval_def, ← Polynomial.aeval_def, ← hg ζ, ← hdv ζ, hc ζ, sub_self]
  have hne : Nonempty (Rs hB.F PD.p s) := by
    rw [← Fintype.card_pos_iff, card_Rs hB]
    exact Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨ζ₀⟩ := hne
  have hrd : rd ≠ 0 := by
    intro h
    apply hd ζ₀
    rw [hdv ζ₀, h, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, rd.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hrd (Polynomial.ext fun k => by simpa using h k)
  have hck : algebraMap O hB.F (rg.coeff k) = c * algebraMap O hB.F (rd.coeff k) := by
    have := congrArg (fun P : Polynomial hB.F => P.coeff k) hR0
    simp only [hRdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_zero] at this
    exact sub_eq_zero.1 this
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  obtain ⟨κ, z, hz⟩ := exists_dvd_pow_of_not_isUnit_dvr ((PD.p : ℕ) : O) hp0 hpu hk
  refine ⟨κ, z * rg.coeff k, ?_⟩
  rw [map_mul, hck, ← map_natCast (algebraMap O hB.F), ← map_pow, hz, map_mul]
  ring

end LevRatPf

end Formalism.MainNotions.UnusedSlot80.InvW
