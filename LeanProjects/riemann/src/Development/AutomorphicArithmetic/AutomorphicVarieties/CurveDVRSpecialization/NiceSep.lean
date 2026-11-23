import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StrongIrrOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CommonFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCosetE
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.OneUnitTF
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TwoDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

private theorem exists_element_separating_powers {G K : Type} [Group G] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l] {n : ℕ}
    (ψ : Fin n → G →* (PowerSeries K)ˣ) (N V : Subgroup G) (hV : V.index ≠ 0)
    (hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (ψ a g : PowerSeries K) =
      PowerSeries.constantCoeff (ψ b g : PowerSeries K))
    (hsep : ∀ a b, a ≠ b → ∃ g ∈ N, ψ a g ≠ ψ b g) :
    ∃ g ∈ N, g ∈ V ∧ ∀ a b, a ≠ b → ∀ m : ℕ, 0 < m → ψ a g ^ m ≠ ψ b g ^ m := by
  haveI : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C_injective (R := K)) l
  have tf : ∀ g ∈ N, ∀ a b (m : ℕ), 0 < m → (ψ a g / ψ b g) ^ m = 1 → ψ a g / ψ b g = 1 := by
    intro g hg a b m hm h
    apply Units.ext
    apply UpperTheory.V.Pr.T.oneUnitTF l _ m hm.ne'
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff ((ψ b g)⁻¹ : (PowerSeries K)ˣ).val *
          PowerSeries.constantCoeff ((ψ b g : (PowerSeries K)ˣ) : PowerSeries K) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hc : PowerSeries.constantCoeff (((ψ a g / ψ b g : (PowerSeries K)ˣ) : PowerSeries K) - 1) = 0 := by
        rw [map_sub, div_eq_mul_inv, Units.val_mul, map_mul, hred g hg a b, mul_comm, hinv, map_one, sub_self]
      rw [hc]
      exact not_isUnit_zero
    · rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  let χ : {p : Fin n × Fin n // p.1 ≠ p.2} → ↥(N ⊓ V) →* (PowerSeries K)ˣ :=
    fun p => (ψ p.1.1 / ψ p.1.2).comp (N ⊓ V).subtype
  obtain ⟨h, hh⟩ := UpperTheory.V.Pr.commonFree ↥(N ⊓ V) (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2} χ 1 one_pos
    (by
      intro p h m hm hpow
      rw [pow_one]
      exact tf h (Subgroup.mem_inf.mp h.2).1 _ _ m hm hpow)
    (by
      intro p
      obtain ⟨g, hgN, hne⟩ := hsep _ _ p.2
      obtain ⟨k, hk, -, hkV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hV g
      refine ⟨⟨g ^ k, Subgroup.mem_inf.mpr ⟨N.pow_mem hgN k, hkV⟩⟩, ?_⟩
      rw [pow_one]
      intro h1
      apply hne
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) ^ k = 1 := by
        simpa [χ, div_pow, map_pow] using h1
      exact div_eq_one.mp (tf g hgN _ _ k hk h2))
  refine ⟨h, (Subgroup.mem_inf.mp h.2).1, (Subgroup.mem_inf.mp h.2).2, ?_⟩
  intro a b hab m hm heq
  apply hh ⟨(a, b), hab⟩ m hm
  simp [χ, div_pow, heq]

theorem UpperTheory.V.Pr.niceSep :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → ∀ v, ∃ g : T.G.Gv v, T.G.φ v g ∈ U ⊓ T.G.G' ∧ UpperTheory.V.Pr.FreeRatios fun i => y.ψ v i g |> Units.map (algebraMap y.A y.Fr).toMonoidHom := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hmat hψ U hU v
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char
  haveI : CharP y.K l :=
    charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) y.K).injective l
  let N : Subgroup (T.G.Gv v) := (F.Nv (T.K.e v)).comap (T.K.lam v).toMonoidHom
  let V : Subgroup (T.G.Gv v) := U.comap (T.G.φ v)
  have hV : V.index ≠ 0 := by
    rw [Subgroup.index_ne_zero_iff_finite]
    exact Subgroup.quotient_finite_of_isOpen V (hU.preimage (T.G.φ_cont v))
  have hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (y.ψ v a g : PowerSeries y.K) =
      PowerSeries.constantCoeff (y.ψ v b g : PowerSeries y.K) := by
    intro g hg a b
    have key : ∀ i, PowerSeries.constantCoeff (y.ψ v i g : PowerSeries y.K) =
        algebraMap (IsLocalRing.ResidueField O) y.K (T.r.psib v i g : IsLocalRing.ResidueField O) :=
      fun i => congrArg Units.val (DFunLike.congr_fun (y.ψ_red v i) g)
    have hΨ : F.Ψ ((F.loc0 (T.K.e v) (T.K.lam v g) : F.del.ker) : F.Γ) = 1 :=
      T.ok.Ψ_N (T.K.e v) (T.K.lam v g) hg
    rw [key a, key b, T.K.psib, T.K.psib, T.K.chib, T.K.chib, ← T.K.lam_loc, hΨ, one_zpow, one_zpow]
  have hsep : ∀ a b, a ≠ b → ∃ g ∈ N, y.ψ v a g ≠ y.ψ v b g := by
    intro a b hab
    have hc := hnice.sep (T.K.e v) a b hab
    simp only [UpperTheory.V.Fr.NRep.Coin, not_forall] at hc
    obtain ⟨g', hg', hne⟩ := hc
    refine ⟨(T.K.lam v).symm g', ?_, ?_⟩
    · show (T.K.lam v) ((T.K.lam v).symm g') ∈ F.Nv (T.K.e v)
      simpa using hg'
    · intro heq
      apply hne
      rw [hψ] at heq
      simp only [UpperTheory.V.Pr.TwLink.twψ, MonoidHom.mul_apply, MonoidHom.comp_apply] at heq
      have h2 := congrArg Units.val (mul_right_cancel heq)
      simp [UpperTheory.V.Fr.NRep.map] at h2
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      convert h2 using 4
      all_goals exact ((T.K.lam v).apply_symm_apply g').symm
  obtain ⟨g, hgN, hgV, hfree⟩ := exists_element_separating_powers l (y.ψ v) N V hV hred hsep
  refine ⟨g, ⟨hgV, ?_⟩, ?_⟩
  · show T.G.ε ((T.G.φ v g : T.G.η.ker) : T.G.Γ) = 1
    rw [← T.K.π_eps, ← T.K.lam_loc]
    exact (Subgroup.mem_inf.mp hgN).2
  · intro a b hab m hm heq
    apply hfree a b hab m hm
    apply Units.ext
    apply IsFractionRing.injective y.A y.Fr
    have h2 := congrArg Units.val heq
    simpa [Units.val_pow_eq_pow_val, map_pow] using h2
