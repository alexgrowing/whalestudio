import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsPrimitiveRootPadicInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.RealDimOne

open GlobalTheory.TorsionGenerators GlobalTheory.ZH.DimZero NumberField

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u n

theorem exists_level_of_points (hL : Laws) {R K : Type} [CommRing R] [Field K] (P₀ : PolAV (Sp R))
    [IsCommMonObj P₀.A] (j : R →+* K) {M : ℕ} (hM : (M : K) ≠ 0) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ M)
    (b : Fin (2 * P₀.g) → (Over.mk (spMap j) ⟶ P₀.A)) (hb : ∀ i, b i ^ M = 1)
    (hw : ∀ i l, WeilIs P₀.A P₀.L M (b i) (b l) (unitOn (ζ ^ stdSymp P₀.g i l))) :
    ∃ (P : PolAV (Sp K)) (φ : P.A.left ⟶ P₀.A.left), IsPolFibre j P₀ P φ ∧
      Nonempty (Out.Level P M (unitOn ζ)) := by
  obtain ⟨P, φ, β, h, -, H⟩ := exists_fibre hL P₀ j
  refine ⟨P, φ, h, ?_⟩
  have hg := h.1
  generalize P₀.g = g at b hb hw hg
  subst hg
  have hx : ∀ i, β.symm (b i) ^ M = 1 := fun i => by rw [← map_pow, hb, map_one]
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ P M (unitOn ζ)
    (isPrimitiveRoot_unitOn hζ) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (isPrimitiveRoot_unitOn hζ).map_of_injective (Units.map_injective
        fun a b hab => e.symm.injective ((s.appTop.hom.comp e.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp e.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀) (fun i => β.symm (b i)) hx (fun i l => by
      obtain ⟨c, hc, -⟩ := (hL.weil _ P M _).1 _ _ (hx i) (hx l)
      have H' := H M _ _ c hc
      rw [β.apply_symm_apply, β.apply_symm_apply] at H'
      rw [← unitOn_zpow, ← CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H' (hw i l)]
      exact hc)
  exact ⟨lev⟩

theorem exists_level_numberField (hL : Laws) {K₀ : Type} [Field K₀] [NumberField K₀] (P₀ : PolAV (Sp K₀)) {M : ℕ}
    (hM : M ≠ 0) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (j : K₀ →+* K) (P : PolAV (Sp K))
      (φ : P.A.left ⟶ P₀.A.left) (ζ : Kˣ), IsPrimitiveRoot ζ M ∧ IsPolFibre j P₀ P φ ∧
      Nonempty (Out.Level P M (unitOn ζ)) := by
  have := P₀.isAb.comm
  have := P₀.isAb.smooth
  let Q := AlgebraicClosure K₀
  let t : K₀ →+* Q := algebraMap K₀ Q
  have : NeZero M := ⟨hM⟩
  obtain ⟨z₀, hz₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Q M
  have hz := hz₀.isUnit_unit hM
  generalize (hz₀.isUnit hM).unit = z at hz
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P₀ t
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL Q P' h.1.symm M (Nat.cast_ne_zero.2 hM) _
    (isPrimitiveRoot_unitOn hz)
  choose s hs hb using fun i => exists_finite_coordinates P₀.A.hom t (β (x i)).left (Over.w _)
  let s' : Set Q := insert (z : Q) (⋃ i, s i)
  have : Finite s' := ((Set.finite_iUnion hs).insert _).to_subtype
  let K := IntermediateField.adjoin K₀ s'
  have : FiniteDimensional K₀ K := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have : NumberField K := NumberField.of_module_finite K₀ K
  let io : K →+* Q := algebraMap K Q
  let j : K₀ →+* K := algebraMap K₀ K
  have hj : io.comp j = t := rfl
  choose b hb' using fun i => hb i K io io.injective (fun c => ⟨j c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K₀ s' (Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨i, hy⟩))⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P₀.A.hom = spMap j := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (β (x i))
  let y : Fin (2 * P₀.g) → (Over.mk (spMap j) ⟶ P₀.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = β (x i) := fun i => Over.OverMorphism.ext (hb' i)
  have hyM : ∀ i, y i ^ M = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy, ← map_pow]
    exact (congrArg β (hx i)).trans (map_one β)
  let ζ : Kˣ := Units.mk0 ⟨z, IntermediateField.subset_adjoin K₀ s' (Set.mem_insert _ _)⟩
    fun e => z.ne_zero (congrArg Subtype.val e)
  have hζ : Units.map io.toMonoidHom ζ = z := Units.ext rfl
  have hp : IsPrimitiveRoot ζ M := IsPrimitiveRoot.of_map_of_injective (hζ ▸ hz) (unitsMap_injective io)
  obtain ⟨P, φ, h₁, h₂⟩ := exists_level_of_points hL P₀ j (Nat.cast_ne_zero.2 hM) hp y hyM fun i l => by
    obtain ⟨u, hu⟩ := exists_weilIs hL P₀ j (hyM i) (hyM l)
    have H₁ := weilIs_extPt hL P₀ hj hu
    rw [hy, hy] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H₁ (H _ _ _ _ (hw i l))
    rw [← unitOn_zpow, ← hζ, ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  exact ⟨K, _, this, j, P, φ, ζ, hp, h₁, h₂⟩

theorem exists_real_dim_one : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω), S.g = 1 ∧ S.Big ∧ Nonempty S.Real := by
  intro hL hL2
  obtain ⟨K₀, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsCyclotomicExtension {3} ℚ K :=
    ⟨CyclotomicField 3 ℚ, inferInstance, inferInstance, by
      convert CyclotomicField.isCyclotomicExtension 3 ℚ <;> first | rfl | exact Subsingleton.elim _ _⟩
  have hω := (IsCyclotomicExtension.zeta_spec 3 ℚ K₀).geom_sum_eq_zero (by norm_num)
  obtain ⟨P₀, hg, hS⟩ := CubeRootAut.exists_hypS hL K₀ (IsCyclotomicExtension.zeta 3 ℚ K₀) (by
    rw [← hω]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = (3 ^ 5 * (3 ^ 2) ^ 2) ^ 2 := ⟨_, rfl⟩
  have hM₀ : M ≠ 0 := by rw [hM]; positivity
  obtain ⟨K, _, _, j, P, φ, ζ, hζ, h, ⟨lev⟩⟩ := exists_level_numberField hL P₀ hM₀
  have := arithBase_intAway K
  have hS' : HypS P.A P.L :=
    SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P₀.isLB P.isLB h.2.1 h.2.2.symm hS
  have hζ' : IsPrimitiveRoot (ζ : K) M := IsPrimitiveRoot.coe_units_iff.2 hζ
  have : NeZero M := ⟨hM₀⟩
  let ze : (intAway K)ˣ := Units.map (algebraMap (𝓞 K) (intAway K)).toMonoidHom
    (hζ'.toInteger_isPrimitiveRoot.isUnit hM₀).unit
  have hze : ζ = Units.map (algebraMap (intAway K) K).toMonoidHom ze := Units.ext rfl
  have h3 : IsUnit ((3 : ℕ) : intAway K) := by simpa using isUnit_three_intAway K
  have hu : IsUnit (M : intAway K) := by
    rw [hM]
    simp only [Nat.cast_pow, Nat.cast_mul]
    exact ((h3.pow _).mul ((h3.pow _).pow _)).pow _
  have frac : ∀ x : K, ∃ a ∈ (⊥ : Subalgebra (intAway K) K), ∃ b ∈ (⊥ : Subalgebra (intAway K) K), x = a / b :=
    fun x => by
      obtain ⟨a, b, -, h⟩ := IsFractionRing.div_surjective (A := intAway K) x
      exact ⟨_, Subalgebra.algebraMap_mem _ a, _, Subalgebra.algebraMap_mem _ b, h.symm⟩
  obtain ⟨R, P', -, lev', hR, fg, hg', hS'', -⟩ :=
    GenSpread.polAV_spreads_out (intAway K) K ⊥ Subalgebra.fg_bot frac P M ze hu hS' (hze ▸ lev) hL
  obtain ⟨S, ρ, -, -, -, hN, hr, hSg, -⟩ := ThetaReal.exists_thetaSys_real hL hL2 (intAway K) K R fg (fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := frac x
      exact ⟨a, hR ha, b, hR hb, e⟩) P' 3 2 5 ze Nat.prime_three (by decide) le_rfl (by norm_num) h3 hS'' (hM ▸ lev')
  have g1 : S.g = 1 := hSg.trans (hg'.trans (h.1.trans hg))
  refine ⟨_, K, _, _, _, arithBase_intAway K, S, g1, ?_, ⟨ρ⟩⟩
  have a₁ : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) one_le_two (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have a₂ : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by norm_num)
  have a₃ : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) := by positivity
  have a₄ : (2 : ℝ) ^ ((1 : ℝ) / 2 - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  unfold ThetaSys.Big
  rw [g1, hN, hr]
  simp only [Nat.cast_one, Nat.factorial_one, pow_one]
  refine ⟨?_, ?_, by norm_num⟩
  · push_cast
    linarith
  · push_cast
    linarith

end GlobalTheory.ZH.RealDimOne
