import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.XdualBase

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cyc_open (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
    [hl : Fact l.Prime] : IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have e1 : ((cycMod F Ω l 1).ker : Set (G F Ω)) =
      (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) - 1) ⁻¹' Metric.closedBall 0 ((l : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, map_one, sub_eq_zero, SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [e1]
  refine (IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))).preimage ?_
  exact (Units.continuous_val.comp (continuous_cycZ F Ω l)).sub continuous_const

private theorem not_dvd_ker {H : Type} [Group H] (l : ℕ) [hl : Fact l.Prime] (φ : H →* (ZMod (l ^ 1))ˣ) :
    ¬ l ∣ φ.ker.index := by
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  intro h
  rw [Subgroup.index_ker] at h
  have h1 : l ∣ Nat.card (ZMod (l ^ 1))ˣ := h.trans (Subgroup.card_subgroup_dvd_card _)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out] at h1
  have h2 := hl.out.two_le
  have := Nat.le_of_dvd (by omega) h1
  omega

private theorem rbar_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (g : G ℚ Ω) :
    D.rbar g = 1 ↔ ∀ i, Units.map (residue c.O).toMonoidHom (D.ps i g) = 1 := by
  have hr : D.rbar g = Matrix.diagonal fun i => residue c.O (D.ps i g : c.O) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Raw.rbar, Raw.r0, diagRep]
    · simp [Raw.rbar, Raw.r0, diagRep, h]
  rw [hr, ← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  exact forall_congr' fun i => by rw [Units.ext_iff]; rfl

theorem UpperTheory.V.Ws.residualKernel_properties :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Kr.Normal ∧ IsOpen (T.Kr : Set (G T.F Ω)) ∧ ¬ l ∣ T.Kr.index ∧ T.Kr ≤ (cycMod T.F Ω l 1).ker ∧ (∀ g ∈ T.Kr, D.rbar (resQ T.F g) = 1) ∧ (∀ w g, D.rbar (resQ T.F g) = 1 → T.rbU w g = 1) ∧ (prodS D ≠ 0 ∧ l ∣ prodS D) ∧ (∀ g ∈ ineOff T.F Ω (prodS D), g ∈ (T.fr ∅).N ∧ D.rbar (resQ T.F g) = 1) ∧ ∀ r, XRk l 1 (kerQ D T.F) r → XRk l 1 T.Kr r := by
  intro Ω _ _ _ l hl c D hD T
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, fo, -, fu⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  obtain ⟨hN, hI, -⟩ := UpperTheory.V.X.spKer D
  obtain ⟨hE, -, -⟩ := galEmbTop ℚ T.F Ω
  obtain ⟨hDI, -, -, -⟩ := galEmbFam ℚ T.F Ω l
  have hfix : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hK : T.Kr = D.rbar.ker.comap (resQ T.F) ⊓ (cycMod T.F Ω l 1).ker := by
    ext g
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hfix g, h.1⟩, h.2⟩⟩
  refine ⟨?_, ?_, ?_, hK ▸ inf_le_right, fun g hg => hg.1.2, fun w g hg => ?_,
    ⟨Finset.prod_ne_zero_iff.2 fun p hp => (hD.S_prime p hp).ne_zero, Finset.dvd_prod_of_mem _ hD.l_mem⟩, ?_, fun r hr => ?_⟩
  · rw [hK]
    infer_instance
  · rw [hK]
    exact (fo.preimage hE.continuous).inter (cyc_open T.F Ω l)
  · rw [hK, ← Subgroup.relIndex_mul_index inf_le_left, Subgroup.inf_relIndex_left]
    intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h2 | h2
    · exact not_dvd_ker l _ (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
    · rw [Subgroup.index_comap] at h2
      exact hI (h2.trans (Subgroup.relIndex_dvd_index_of_normal _ _))
  · have h := fun i => (rbar_iff D _).1 hg (lab T.pr i)
    show Units.map (residue c.O).toMonoidHom
      ((D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 1) (resQ T.F g))⁻¹) ^ w.1 *
        (D.ps (lab T.pr 0) (resQ T.F g) * (D.ps (lab T.pr 2) (resQ T.F g))⁻¹) ^ w.2) = 1
    simp only [map_mul, map_zpow, map_inv, h, inv_one, mul_one, one_zpow]
  · rintro g ⟨A, hA, hg⟩
    have hS : Raw.Away D.S A := fun p hp hv => hA (by
      obtain ⟨m, hm⟩ : p ∣ prodS D := Finset.dvd_prod_of_mem _ hp
      rw [hm, Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (natCast_mem A m))) hv)
    have hg' : resQ T.F g ∈ Ine (F := ℚ) A := by
      rw [← (hDI A).2] at hg
      exact hg
    have h1 : D.rbar (resQ T.F g) = 1 := (rbar_iff D _).2 fun i => by
      rw [MonoidHom.mem_ker.1 (fu i A hS hg'), map_one]
    refine ⟨⟨A, fun p hp => ?_, hg, h1⟩, h1⟩
    have : p = l := by simpa using hp
    exact hS p (this ▸ hD.l_mem)
  · have hle : kerQ D T.F ≤ galOf ℚ T.F Ω := fun g hg x =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg.1.1 x.1 x.2
    obtain ⟨⟨ε, -, hε, -⟩, -⟩ := UpperTheory.V.Kum.xdualBase ℚ Ω T.F 1 (kerQ D T.F) (ZMod l) (ZMod l) hle
    have e := (ε.ofSubmodules _ _ hε).toEquiv
    exact CardLe.of_injective hr e.symm e.symm.injective
