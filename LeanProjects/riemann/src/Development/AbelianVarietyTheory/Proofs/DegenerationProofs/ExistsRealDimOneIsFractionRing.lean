import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
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

namespace GlobalTheory.RealInhabitant

open TorsionGenerators NumberField

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (a : ℤ) : unitOn (u ^ a) = unitOn u ^ a :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u a

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem map_unitOn {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (Geo.Tor.spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

theorem isPrimitiveRoot_map {B F : Type} [CommRing B] [IsDomain B] [Field F] (σ : B →+* F) {M : ℕ} (hM : (M : F) ≠ 0)
    {z : Bˣ} (hz : IsPrimitiveRoot z M) : IsPrimitiveRoot (Units.map σ.toMonoidHom z) M := by
  have : NeZero (M : F) := ⟨hM⟩
  have h₀ : 0 < M := Nat.pos_of_ne_zero fun e => hM (by rw [e, Nat.cast_zero])
  have h := ((IsPrimitiveRoot.coe_units_iff.2 hz).isRoot_cyclotomic h₀).map (f := σ)
  rw [Polynomial.map_cyclotomic] at h
  exact IsPrimitiveRoot.coe_units_iff.1 (Polynomial.isRoot_cyclotomic_iff.1 h)

theorem exists_finite_level (hL : Laws) {R₀ Q : Type} [CommRing R₀] [Field Q] [IsAlgClosed Q] (t : R₀ →+* Q)
    (P₀ : PolAV (Sp R₀)) {M : ℕ} (hM : (M : Q) ≠ 0) {ζ : Qˣ} (hζ : IsPrimitiveRoot ζ M) :
    ∃ s : Set Q, s.Finite ∧ ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (io : B →+* Q) (j : R₀ →+* B) (z : Bˣ),
      Function.Injective io → io.comp j = t → (∀ y ∈ s, y ∈ io.range) → Units.map io.toMonoidHom z = ζ →
      IsUnit (M : B) → ∀ (P : PolAV (Sp B)) (φ : P.A.left ⟶ P₀.A.left), IsPolFibre j P₀ P φ →
      Nonempty (Out.Level P M (unitOn z)) := by
  have := P₀.isAb.comm
  have := P₀.isAb.smooth
  have := P₀.isAb.proper
  obtain ⟨P', φ', β, h', -, hW⟩ := exists_fibre hL P₀ t
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL Q P' h'.1.symm M hM
    (unitOn ζ) (isPrimitiveRoot_unitOn hζ)
  choose s hs hb using fun i => exists_finite_coordinates P₀.A.hom t (β (x i)).left (Over.w _)
  refine ⟨⋃ i, s i, Set.finite_iUnion hs, fun B _ _ io j z hio hj hsB hzζ hMB P φ h => ?_⟩
  have := hio.isDomain io
  have : IsDominant (Geo.Tor.spMap io) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le)⟩
  choose b hb' using fun i => hb i B io hio (fun c => ⟨j c, congr($hj c)⟩)
    (fun y hy => hsB y (Set.mem_iUnion.2 ⟨i, hy⟩))
  have hs₀ : Geo.Tor.spMap io ≫ Geo.Tor.spMap j = Geo.Tor.spMap t := by rw [spMap_comp_spMap, hj]
  have hbw : ∀ i, b i ≫ P₀.A.hom = Geo.Tor.spMap j := fun i => ext_of_isDominant (Geo.Tor.spMap io) (by
    rw [← Category.assoc, hb', hs₀]
    exact Over.w (β (x i)))
  let u : Over.mk (Geo.Tor.spMap t) ⟶ Over.mk (Geo.Tor.spMap j) := Over.homMk (Geo.Tor.spMap io) hs₀
  let e : Fin (2 * P₀.g) → (Over.mk (Geo.Tor.spMap j) ⟶ P₀.A) := fun i => Over.homMk (b i) (hbw i)
  have he : ∀ i, u ≫ e i = β (x i) := fun i => Over.OverMorphism.ext (hb' i)
  have : IsReduced (Over.mk (Geo.Tor.spMap j)).left := inferInstanceAs (IsReduced (Sp B))
  have heM : ∀ i, e i ^ M = 1 := fun i => Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P₀.A.hom
    (by rw [Over.w, Over.w]) (Geo.Tor.spMap io) (by
      show (u ≫ e i ^ M).left = (u ≫ 1).left
      rw [comp_pow, he, comp_one, ← map_pow]
      exact congrArg (·.left) ((congrArg β (hx i)).trans (map_one β))))
  have hz : IsPrimitiveRoot z M :=
    IsPrimitiveRoot.of_map_of_injective (hzζ ▸ hζ) (Units.map_injective (f := io.toMonoidHom) hio)
  obtain ⟨κ, hκ⟩ := UnifPoint.exists_pointEquiv h.2.1
  have hg := h.1
  let c : Fin (2 * P.g) → Fin (2 * P₀.g) := Fin.cast (congrArg (2 * ·) hg)
  have hy : ∀ i, κ.symm (e i) ^ M = 1 := fun i => (map_pow κ.symm _ _).symm.trans (by rw [heM, map_one])
  obtain ⟨lev, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ P M (unitOn z) (isPrimitiveRoot_unitOn hz)
    (fun F _ s => by
      obtain ⟨σ, rfl⟩ := Spec.map_surjective s
      have hF : (M : F) ≠ 0 := by rw [← map_natCast σ.hom]; exact (hMB.map σ.hom).ne_zero
      exact ⟨hF, (map_unitOn σ.hom z).symm ▸ isPrimitiveRoot_unitOn (isPrimitiveRoot_map σ.hom hF hz)⟩)
    (fun i => κ.symm (e (c i))) (fun i => hy _) (fun i i' => by
      obtain ⟨v, hv, -⟩ := (hL.weil _ P M _).1 _ _ (hy (c i)) (hy (c i'))
      have H := (weilIs_grpPullback_of_comm _ _ P₀.A P.A _ φ P₀.L P.L P₀.isLB P.isLB h.2.1 (LBIso.symm h.2.2) _ M _ _
        (pushPt h.2.1.1.w (κ.symm (e (c i)))) (pushPt h.2.1.1.w (κ.symm (e (c i')))) _ rfl rfl).1 hv
      have k : ∀ i, (pushPt h.2.1.1.w (κ.symm (e i))).left = (e i).left := fun i =>
        (hκ _).symm.trans (congrArg (·.left) (κ.apply_symm_apply _))
      have H₁ := CommPairing.weilIs_pull hL.globalFns P₀.isAb P₀.isLB u
        (UnifPoint.weilIs_congr (Category.id_comp _) (k _) (k _) H)
      rw [he, he] at H₁
      have e₁ := CommutatorPairing.weilIs_unique hL.globalFns P₀.isAb P₀.isLB H₁ (hW _ _ _ _ (hw _ _))
      let v' := Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom v
      have ev : unitOn v' = v := Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of B)) v.val)
      have e₂ : unitOn (Units.map io.toMonoidHom v') = unitOn ζ ^ stdSymp P₀.g (c i) (c i') := by
        rw [← map_unitOn, ev]; exact e₁
      rw [← unitOn_zpow, ← hzζ, ← map_zpow] at e₂
      have e₃ := Units.map_injective (f := io.toMonoidHom) hio (unitOn_injective e₂)
      have e₄ : stdSymp P₀.g (c i) (c i') = stdSymp P.g i i' := by simp only [stdSymp, c, Fin.val_cast, hg]
      rw [← unitOn_zpow, ← e₄, ← e₃, ev]
      exact hv)
  exact ⟨lev⟩

theorem powers_le (K : Type) [Field K] [NumberField K] : Submonoid.powers (3 : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast (by decide : (3 : ℕ) ≠ 0))

abbrev IntThird (K : Type) [Field K] [NumberField K] : Type :=
  Localization.subalgebra.ofField K (Submonoid.powers (3 : 𝓞 K)) (powers_le K)

theorem arithBase (K : Type) [Field K] [NumberField K] : ArithBase (IntThird K) K where
  ded := IsLocalization.isDedekindDomain (𝓞 K) (powers_le K) _
  ft := by
    have : Algebra.FiniteType (𝓞 K) (IntThird K) :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (3 : 𝓞 K)) _
    exact Algebra.FiniteType.trans (S := 𝓞 K) inferInstance inferInstance
  char := inferInstance
  inj := Subtype.val_injective

theorem isUnit_three (K : Type) [Field K] [NumberField K] : IsUnit ((3 : ℕ) : IntThird K) := by
  simpa only [map_ofNat, Nat.cast_ofNat] using IsLocalization.Away.algebraMap_isUnit (S := IntThird K) (3 : 𝓞 K)

theorem isUnit_three_subalgebra {K : Type} [Field K] [NumberField K] (R : Subalgebra (IntThird K) K) :
    IsUnit (3 : R) := by
  simpa only [map_ofNat, Nat.cast_ofNat] using (isUnit_three K).map (algebraMap (IntThird K) R)

theorem exists_level_hypS (hL : Laws) (m : ℕ) : ∃ (K : Type) (_ : Field K) (_ : NumberField K)
    (R : Subalgebra (IntThird K) K) (ze : (IntThird K)ˣ) (P : PolAV (Sp R)), R.FG ∧ P.g = 1 ∧ HypS P.A P.L ∧
    Nonempty (Out.Level P (3 ^ (m + 1)) (unitOn (Units.map (algebraMap (IntThird K) R).toMonoidHom ze))) := by
  let Q := AlgebraicClosure ℚ
  let R₀ := Localization.Away (3 : ℤ)
  have h₀ : IsUnit (3 : R₀) := by
    simpa only [map_ofNat] using IsLocalization.Away.algebraMap_isUnit (S := R₀) (3 : ℤ)
  have := CMCurve.isElliptic_eisensteinCurve h₀
  have lf : ∀ (B : Type) [CommRing B], IsUnit (3 : B) → Nonempty (R₀ →+* B) := fun B _ h =>
    ⟨IsLocalization.Away.lift (3 : ℤ) (g := Int.castRingHom B) (by simpa using h)⟩
  obtain ⟨t⟩ := lf Q (Ne.isUnit three_ne_zero)
  have hM : 0 < 3 ^ (m + 1) := by positivity
  have : NeZero (3 ^ (m + 1)) := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Q (3 ^ (m + 1))
  obtain ⟨s, hs, H⟩ := exists_finite_level hL t (WeierstrassCurve.ellPolAV (CMCurve.eisensteinCurve R₀))
    (Nat.cast_ne_zero.2 hM.ne') (hζ.isUnit_unit hM.ne')
  have : Finite (insert ζ s : Set Q) := (hs.insert _).to_subtype
  have : Algebra.IsAlgebraic ℚ Q := AlgebraicClosure.isAlgebraic ℚ
  let K := IntermediateField.adjoin ℚ (insert ζ s)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have : NumberField K := {}
  let z : K := ⟨ζ, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)⟩
  have hz : IsPrimitiveRoot z (3 ^ (m + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K Q) hζ (algebraMap K Q).injective
  let z' : 𝓞 K := ⟨z, hz.isIntegral hM⟩
  have hz' : IsUnit z' := IsUnit.of_pow_eq_one (Subtype.ext hz.pow_eq_one) hM.ne'
  let ze : (IntThird K)ˣ := (hz'.map (algebraMap (𝓞 K) (IntThird K))).unit
  let R : Subalgebra (IntThird K) K := Algebra.adjoin _ (Subtype.val ⁻¹' s)
  have hR : R.FG := Subalgebra.fg_def.2 ⟨_, hs.preimage Subtype.val_injective.injOn, rfl⟩
  have := (arithBase K).ded
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  have h3 : IsUnit (3 : R) := isUnit_three_subalgebra R
  have := CMCurve.isElliptic_eisensteinCurve h3
  obtain ⟨j⟩ := lf R h3
  let io : R →+* Q := (algebraMap K Q).comp R.toSubring.subtype
  have hio : Function.Injective io := Subtype.val_injective.comp Subtype.val_injective
  let zR : R := ⟨z, R.algebraMap_mem ze⟩
  have hω : IsPrimitiveRoot (zR ^ 3 ^ m) 3 :=
    (IsPrimitiveRoot.of_map_of_injective (f := io) hζ hio).pow hM (pow_succ 3 m)
  have hω' : (zR ^ 3 ^ m) ^ 2 + zR ^ 3 ^ m + 1 = 0 := by
    have := hω.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    linear_combination this
  refine ⟨K, inferInstance, inferInstance, R, ze, WeierstrassCurve.ellPolAV (CMCurve.eisensteinCurve R), hR, rfl,
    CubeRootAut.hypS_eisensteinCurve hL.cube hω', H R io j _ hio
      (IsLocalization.ringHom_ext (Submonoid.powers (3 : ℤ)) (RingHom.ext_int _ _)) (fun y hy => ?_) (Units.ext rfl)
      (by rw [Nat.cast_pow]; exact h3.pow _) _ _ (WeierstrassCurve.ellPolAV_baseChange _ j ?_)⟩
  · exact ⟨⟨⟨y, IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hy)⟩, Algebra.subset_adjoin hy⟩, rfl⟩
  · ext <;> simp [CMCurve.eisensteinCurve]

theorem exists_real_dim_one_isFractionRing : Laws → Laws2 → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (_ : S.Real), S.g = 1 ∧ S.Big ∧ IsFractionRing o Ω := by
  intro hL hL₂
  obtain ⟨K, _, _, R, ze, P, hR, hg, hS, ⟨lev⟩⟩ := exists_level_hypS hL 17
  have := arithBase K
  have hfr : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    exact ⟨_, R.algebraMap_mem (algebraMap (𝓞 K) _ a), _, R.algebraMap_mem (algebraMap (𝓞 K) _ b), rfl⟩
  have e : 3 ^ (17 + 1) = (3 ^ 5 * (3 ^ 2) ^ 2) ^ 2 := by norm_num
  obtain ⟨S, ρ, -, -, -, hN, hr, hSg, -⟩ := ThetaReal.exists_thetaSys_real hL hL₂ (IntThird K) K R hR hfr P 3 2 5 ze Nat.prime_three
    (by decide) le_rfl (by norm_num) (isUnit_three K) hS (e ▸ lev)
  have h1 : S.g = 1 := hSg.trans hg
  refine ⟨IntThird K, K, inferInstance, inferInstance, inferInstance, this, S, ρ, h1, ?_, inferInstance⟩
  unfold ThetaSys.Big
  rw [h1, hN, hr]
  have a : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have b : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2 - 1) ≤ 2 ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have c : (2 : ℝ) ^ (-(1 / 4) : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [Real.rpow_one] at a
  refine ⟨?_, ?_, by norm_num⟩
  · norm_num at a ⊢
    linarith
  · have d := b.trans_lt c
    generalize (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2 - 1) = u at d
    norm_num
    linarith

end GlobalTheory.RealInhabitant

end
