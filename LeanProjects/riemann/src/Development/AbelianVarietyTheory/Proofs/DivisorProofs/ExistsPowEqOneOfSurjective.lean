import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDim
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifEnd

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel in

theorem exists_pow_eq_one_of_surjective (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ B.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hgB hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_factor_pow (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A)
    [IsSeparated A'.hom] [LocallyOfFiniteType A'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A ⟶ A') [IsMonHom φ]
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → y ≫ φ = 1) :
    ∃ α : A ⟶ A', IsMonHom α ∧ (𝟙 A ^ N) ≫ α = φ := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨hmon, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have key : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ (𝟙 A ^ N) = 1 → x ≫ φ = 1 := by
    intro T x hx
    let K := pullback (𝟙 A ^ N) η[A]
    let inc : K ⟶ A := pullback.fst ((𝟙 A ^ N)) η[A]
    have hinc : inc ≫ (𝟙 A ^ N) = 1 := by
      rw [pullback.condition, toUnit_unique (pullback.snd ((𝟙 A ^ N)) η[A]) (toUnit K)]; rfl
    have hp := (IsPullback.of_hasPullback ((𝟙 A ^ N)) η[A]).map (Over.forget (Sp ℂ))
    have he : Etale (pullback.snd ((𝟙 A ^ N)) η[A]).left :=
      MorphismProperty.of_isPullback (P := @Etale) hp het
    have hw : (pullback.snd ((𝟙 A ^ N)) η[A]).left = K.hom := by
      simpa using Over.w (pullback.snd ((𝟙 A ^ N)) η[A])
    rw [hw] at he
    have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
    have hk : inc ≫ φ = 1 := by
      refine Over.OverMorphism.ext ?_
      have : LocallyOfFiniteType ((inc ≫ φ).left ≫ A'.hom) := by rw [Over.w]; infer_instance
      refine ext_of_apply_eq A'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
        ((Over.w _).trans (Over.w _).symm)
      let p : Over.mk (𝟙 (Sp ℂ)) ⟶ K :=
        Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
      have hpN : (p ≫ inc) ^ N = 1 := by
        have : (p ≫ inc) ^ N = (p ≫ inc) ≫ (𝟙 A ^ N) := by rw [MonObj.comp_pow, Category.comp_id]
        rw [this, Category.assoc, hinc, MonObj.comp_one]
      have e : p ≫ inc ≫ φ = p ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        exact h _ hpN
      have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
      have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply K.hom z hz _
      simp only [Over.comp_left] at e'
      rw [← hz']
      exact e'
    have hx' : x ≫ (𝟙 A ^ N) = toUnit T ≫ η[A] := hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ φ = 1
    rw [hk, MonObj.comp_one]
  obtain ⟨⟨α, hα, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A A' ((𝟙 A ^ N)) φ hmon
    inferInstance inferInstance hsurj inferInstance key
  exact ⟨α, hα, hc⟩

theorem exists_isMonHom_of_map_lattice :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u.Λ) → ∃ α : A ⟶ A, IsMonHom α ∧ ∀ w, u.ex (M w) = u.ex w ≫ α := by
  intro A _ g hA hgA L u M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', -, hi', hr', hir'⟩ :=
    EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance

  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i

  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0

  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q Q.g v v (J ∘ₗ M ∘ₗ R)
    rfl rfl (fun l hl => hJΛ _ (hM _ (hRΛ _ hl)))
  haveI := hβ
  have hφ : ∀ z, u.ex z ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) = u.ex ((m * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR, hRJ, hRJ, map_nsmul, smul_smul]
  have := hA.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A hA (m * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    ((i ≫ i') ≫ β ≫ (r' ≫ r)) fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m * m ≠ 0 by positivity)
  have hw : (m * m) • (((m * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u.ex (M w) = u.ex ((m * m) • M (((m * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) := (hφ _).symm
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifEnd
