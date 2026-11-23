import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GSetup

theorem finite_stalkMap_field {K Ω : Type} [Field K] [Field Ω] (f : K →+* Ω) (hf : f.Finite) (x : Sp Ω) :
    ((spMap f).stalkMap x).hom.Finite := by
  haveI := x.isPrime
  refine (RingHom.finite_respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) x)).2 ?_
  refine RingHom.Finite.of_comp_finite (f := algebraMap K _) ?_
  have e : (Localization.localRingHom (PrimeSpectrum.comap f x).asIdeal x.asIdeal f rfl).comp (algebraMap K _) =
      (algebraMap Ω (Localization.AtPrime x.asIdeal)).comp f :=
    RingHom.ext fun a => Localization.localRingHom_to_map _ _ _ rfl a
  refine e ▸ RingHom.Finite.comp (RingHom.Finite.of_surjective _ ?_) hf
  exact (IsLocalization.atUnits Ω x.asIdeal.primeCompl (S := Localization.AtPrime x.asIdeal) fun a ha =>
    (IsUnit.mk0 a fun h => ha (h ▸ zero_mem _) : IsUnit a)).surjective

theorem exists_base_root (o F Ω : Type) [CommRing o] [IsDedekindDomain o] [Field F] [CharZero F] [Algebra o F]
    [IsFractionRing o F] [Field Ω] (β : F →+* Ω) (ζ : Ωˣ) (m : ℕ) (hm : 1 ≤ m) (hζ : ζ ^ m = 1) :
    ∃ (o₁ : Type) (_ : CommRing o₁) (_ : Algebra o₁ Ω) (κ : o →+* o₁) (ze : o₁ˣ), IsDedekindDomain o₁ ∧ κ.Finite ∧
      Function.Injective (algebraMap o₁ Ω) ∧ (algebraMap o₁ Ω).comp κ = β.comp (algebraMap o F) ∧
      Units.map (algebraMap o₁ Ω).toMonoidHom ze = ζ := by
  letI := β.toAlgebra
  have hz : (ζ : Ω) ^ m = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  have hint : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] [Algebra A L] (z : L), z ^ m = 1 → IsIntegral A z :=
    fun A _ L _ _ z h => IsIntegral.of_pow (by omega : 0 < m) (h ▸ isIntegral_one)
  let L : IntermediateField F Ω := IntermediateField.adjoin F {(ζ : Ω)}
  haveI : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional (hint F Ω _ hz)
  letI : Algebra o L := ((algebraMap F L).comp (algebraMap o F)).toAlgebra
  haveI : IsScalarTower o F L := IsScalarTower.of_algebraMap_eq' rfl
  let zL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self F _⟩
  have hzL : zL ^ m = 1 := Subtype.ext (by simpa using hz)
  let o₁ := integralClosure o L
  let z : o₁ := ⟨zL, hint o L _ hzL⟩
  have hz₁ : z ^ m = 1 := Subtype.ext (by simpa using hzL)
  letI : Algebra o₁ Ω := ((algebraMap L Ω).comp (algebraMap o₁ L)).toAlgebra
  refine ⟨o₁, inferInstance, inferInstance, algebraMap o o₁, Units.ofPowEqOne z m hz₁ (by omega),
    integralClosure.isDedekindDomain o F L, RingHom.finite_algebraMap.2 (IsIntegralClosure.finite o F L o₁),
    (algebraMap L Ω).injective.comp Subtype.val_injective, rfl, Units.ext rfl⟩

theorem exists_level_finite (K : Type) [Field K] [CharZero K] (A : PolAV (Sp K)) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (Ω : Type) (_ : Field Ω) (f : K →+* Ω) (A₁ : PolAV (Sp Ω)) (ψ : A₁.A.left ⟶ A.A.left) (ze : Ωˣ),
      f.Finite ∧ IsPolFibre f A A₁ ψ ∧ ze ^ m = 1 ∧ Nonempty (Out.Level A₁ m (unitOn ze)) := by
  obtain ⟨K', _, _, hfin, H⟩ := LevelAfterExt.exists_ext_level K A m hm
  haveI : FiniteDimensional K K' := hfin
  obtain ⟨Ω, _, _, _, _, j, ζ, hζ⟩ := MumLevel.exists_galois_root K K' m hm
  let f : K →+* Ω := algebraMap K Ω
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  obtain ⟨A₁, ψ, hA⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 f A
  let ze : Ωˣ := (hζ.isUnit (by omega)).unit
  have hze : IsPrimitiveRoot (ze : Ω) m := hζ
  obtain ⟨lev, -, h₂, h₃⟩ := H Ω j.toRingHom f j.comp_algebraMap A₁ ψ hA A₁.g rfl ze hze
  have hL := GlobalTheory.lawsAndExpansions.1.1
  have := A₁.isAb.comm
  have hM : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let ek := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  obtain ⟨L, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ A₁ m (unitOn ze)
    (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)).map_of_injective
        (Units.map_injective fun a b hab => ek.symm.injective ((s.appTop.hom.comp ek.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp ek.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀)
    (fun k => lev (Pi.single (MumLevel.half A₁.g k) 1)) (fun k => h₂ _) (fun k l => by
      rw [MumLevel.stdSymp_eq, ← ZH.RealDimOne.unitOn_zpow]
      exact h₃ _ _)
  exact ⟨Ω, inferInstance, f, A₁, ψ, ze, RingHom.finite_algebraMap.2 inferInstance, hA,
    (IsPrimitiveRoot.coe_units_iff.1 hze).pow_eq_one, ⟨L⟩⟩

theorem exists_chart {F : Type} [Field F] {X : Scheme.{0}} (s : X ⟶ Sp F) [LocallyOfFiniteType s] (x : X) :
    ∃ (A : Type) (_ : CommRing A) (φ : F →+* A) (j : Sp A ⟶ X) (P : Ideal A) (_ : P.IsPrime), φ.FiniteType ∧
      j ≫ s = spMap φ ∧ IsOpenImmersion j ∧ j ⟨P, inferInstance⟩ = x := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  exact ⟨Γ(X, U), inferInstance, a.hom, hU.fromSpec, (hU.primeIdealOf ⟨x, hx⟩).asIdeal, inferInstance, hft, ha.symm,
    inferInstance, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩

theorem exists_int_mul_mem {o F : Type} [CommRing o] [IsDomain o] [IsIntegrallyClosed o] [Field F] [NumberField F]
    [Algebra o F] [IsFractionRing o F] (y : F) : ∃ m : ℤ, m ≠ 0 ∧ ∃ a : o, algebraMap o F a = m * y := by
  obtain ⟨m, hm, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
    (Algebra.IsAlgebraic.isAlgebraic y)).exists_integral_multiple
  have h : IsIntegral o (algebraMap ℤ F m * y) := by
    obtain ⟨p, hp, h0⟩ := hy
    refine ⟨p.map (Int.castRingHom o), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap o F).comp (Int.castRingHom o)) (algebraMap ℤ F),
      ← Algebra.smul_def]
    exact h0
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨m, hm, a, by rw [ha, eq_intCast]⟩

theorem exists_fg_ratHull {o F o₁ Ω A : Type} [CommRing o] [Field F] [CommRing o₁] [Field Ω] [CharZero Ω] [Algebra o₁ Ω] [CommRing A]
    (b : o →+* F) (hb : ∀ y : F, ∃ m : ℤ, m ≠ 0 ∧ ∃ a, b a = m * y) (κ : o →+* o₁) (β : F →+* Ω)
    (hκ : (algebraMap o₁ Ω).comp κ = β.comp b) (hβ : β.EssFiniteType) (φ : F →+* A) (hφ : φ.FiniteType) (e : A →+* Ω)
    (he : e.comp φ = β) :
    ∃ R₀ : Subalgebra o₁ Ω, R₀.FG ∧ (∀ z : Ω, ∃ a ∈ R₀, ∃ c ∈ R₀, z = a / c) ∧ ∀ a, e a ∈ ratHull R₀ := by
  classical
  letI := β.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff F Ω).1 hβ
  obtain ⟨t, ht⟩ := hφ
  let R₀ : Subalgebra o₁ Ω := Algebra.adjoin o₁ ((σ : Set Ω) ∪ e '' (t : Set A))
  have hF : ∀ y : F, β y ∈ ratHull R₀ := fun y => by
    obtain ⟨m, hm, a, ha⟩ := hb y
    refine mem_ratHull.2 ⟨m, hm, ?_⟩
    have : algebraMap o₁ Ω (κ a) = m * β y := by
      rw [← RingHom.comp_apply, hκ, RingHom.comp_apply, ha, map_mul, map_intCast]
    exact this ▸ R₀.algebraMap_mem _
  have hσ' : ∀ z ∈ Algebra.adjoin F (σ : Set Ω), z ∈ ratHull R₀ := fun z hz => by
    induction hz using Algebra.adjoin_induction with
    | mem x hx => exact le_ratHull _ (Algebra.subset_adjoin (Or.inl hx))
    | algebraMap y => exact hF y
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  refine ⟨R₀, Subalgebra.fg_def.2 ⟨_, (σ.finite_toSet.union (t.finite_toSet.image _)), rfl⟩, fun z => ?_, fun a => ?_⟩
  · obtain ⟨w, hw, hu, hzw⟩ := hσ z
    obtain ⟨m₁, hm₁, h₁⟩ := mem_ratHull.1 (hσ' _ hzw)
    obtain ⟨m₂, hm₂, h₂⟩ := mem_ratHull.1 (hσ' _ hw)
    refine ⟨_, mul_mem (intCast_mem R₀ m₂) h₁, _, mul_mem (intCast_mem R₀ m₁) h₂, ?_⟩
    have hw0 : w ≠ 0 := hu.ne_zero
    have h1 : (m₁ : Ω) ≠ 0 := Int.cast_ne_zero.2 hm₁
    have h2 : (m₂ : Ω) ≠ 0 := Int.cast_ne_zero.2 hm₂
    field_simp
  · have ha : a ∈ Algebra.adjoin F (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact le_ratHull _ (Algebra.subset_adjoin (Or.inr ⟨x, hx, rfl⟩))
    | algebraMap y => exact (show e (algebraMap F A y) = β y from congrArg (· y) he) ▸ hF y
    | add x y _ _ hx hy => exact (map_add e x y).symm ▸ add_mem hx hy
    | mul x y _ _ hx hy => exact (map_mul e x y).symm ▸ mul_mem hx hy

theorem map_unitOn' {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    (spMap β).appTop.hom (unitOn c : Γ(Sp A, ⊤)) = (unitOn (Units.map β.toMonoidHom c) : Γ(Sp B, ⊤)) :=
  (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

theorem exists_thetaSys_uOver (Xo : Moduli D l) (c : Coeff l) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    [hb : ArithBase o Ω] (R₀ : Subalgebra o Ω) (hR₀ : R₀.FG) (hfr : ∀ z : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, z = a / b)
    (u₀ : Sp (ratHull R₀) ⟶ Xo.XF c) (A₁ : PolAV (Sp Ω))
    (hU : UOver Xo c A₁ (RingHom.id Ω) (spMap (ratHull R₀).val.toRingHom ≫ u₀)) (hS : HypS A₁.A A₁.L)
    (n k j : ℕ) (hn : n.Prime) (ho : Odd n) (hk : 2 ≤ k) (hj : 1 ≤ j) (hun : IsUnit (n : o)) (ze : oˣ)
    (lev : Out.Level A₁ ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) :
    ∃ (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧
      S.g = A₁.g ∧ UOver Xo c ρ.P (toRat S.R) u ∧
      spMap (ratHull S.R).val.toRingHom ≫ u = spMap (ratHull R₀).val.toRingHom ≫ u₀ := by
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI := hb.ded
  haveI := hb.char
  have hM : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : o) := by
    push_cast
    exact ((hun.pow _).mul ((hun.pow _).pow _)).pow _
  have frOf : ∀ R : Subalgebra o Ω, R₀ ≤ R → ∀ z : Ω, ∃ a ∈ R, ∃ b ∈ R, z = a / b := fun R h z =>
    let ⟨a, ha, b, hb, e⟩ := hfr z
    ⟨a, h ha, b, h hb, e⟩

  obtain ⟨R, P', φ, lev', hle, hR, hg', hS', hφ, hφL, -⟩ :=
    GenSpread.polAV_spreads_out o Ω R₀ hR₀ hfr A₁ _ ze hM hS lev hL
  let uR : Sp (ratHull R) ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u₀
  have ptR : spMap (ratHull R).val.toRingHom ≫ uR = spMap (ratHull R₀).val.toRingHom ≫ u₀ := by
    rw [← Category.assoc, ← Spec.map_comp]; rfl
  have h₁ : UOver Xo c P' R.val.toRingHom (spMap (ratHull R).val.toRingHom ≫ uR) := by
    rw [ptR]
    simpa using (uOver_baseChange_iff hφ hφL (RingHom.id Ω)).1 hU

  obtain ⟨R', hle', hR', h₂⟩ := UOver.exists_spread hR (frOf R hle) h₁
  let u' : Sp (ratHull R') ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono hle')).toRingHom ≫ uR
  have pt' : spMap (ratHull R').val.toRingHom ≫ u' = spMap (ratHull R₀).val.toRingHom ≫ u₀ := by
    rw [← ptR, ← Category.assoc, ← Spec.map_comp]; rfl

  haveI : IsNoetherianRing o := inferInstance
  haveI := (Subalgebra.fg_iff_finiteType R).1 hR
  haveI := (Subalgebra.fg_iff_finiteType R').1 hR'
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o R
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing o R'
  obtain ⟨P'', φ', hP''⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1
    (Subalgebra.inclusion hle').toRingHom P'
  have hL'' : LBIso P''.L (P'.L.pull φ') := LBIso.symm hP''.2.2
  have hS'' : HypS P''.A P''.L := by
    have := P'.isAb.comm
    have := P''.isAb.comm
    exact SymBaseChange.hypS_baseChange _ _ _ _ _ φ' _ _ P'.isLB P''.isLB hP''.2.1 hL'' hS'
  obtain ⟨lev'', -⟩ := exists_level_baseChange hL _ _ _ P' P'' φ' hP''.2.1 hL'' hP''.1 _ _
    (unitOn (Units.map (algebraMap o R').toMonoidHom ze))
    (by rw [map_unitOn']; rfl)
    ((SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).2 (by
      have := (SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev'.prim
      exact (IsPrimitiveRoot.coe_units_iff.1 ((IsPrimitiveRoot.coe_units_iff.2 this).map_of_injective
        (f := Subalgebra.inclusion hle') (Subalgebra.inclusion_injective hle')))))
    lev'
  have h₃ : UOver Xo c P'' (toRat R') u' := (uOver_baseChange_iff hP''.2.1 hL'' (toRat R')).2 h₂

  obtain ⟨S, ρ, h, χ, -, hN, hr, hg, hχ, hχL, -⟩ :=
    ThetaReal.exists_thetaSys_real hL hL₂ o Ω R' hR' (frOf R' (hle.trans hle')) P'' n k j ze hn ho hk hj hun hS''
      lev''
  let uS : Sp (ratHull S.R) ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u'
  refine ⟨S, ρ, uS, hN, hr, hg.trans (hP''.1.trans (hg'.trans rfl)), ?_, ?_⟩
  · exact (uOver_baseChange_iff hχ hχL (toRat S.R)).2 (h₃.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom)
  · rw [← pt', ← Category.assoc, ← Spec.map_comp]; rfl

theorem exists_big_level (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem hypS_univ (Xo : Moduli D l) : HypS Xo.univ.t.G Xo.univ.t.PP.L :=
  ⟨Xo.univ.t.act.act H.w0, Xo.univ.t.act.act (H.bar H.w0), Xo.univ.t.act.hom _, Xo.univ.t.act.hom _,
    by rw [← Xo.univ.t.act.add, HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, Xo.univ.t.act.one], Xo.univ.t.prim, Xo.univ.t.adj _⟩

theorem exists_fibre (Xo : Moduli D l) (c : Coeff l) {K : Type} [CommRing K] (y : Sp K ⟶ Xo.XF c) :
    ∃ P : PolAV (Sp K), HypS P.A P.L ∧ UOver Xo c P (RingHom.id K) y := by
  obtain ⟨P, g, hG, hL⟩ := exists_pol_baseChange (Obj.toPolAV Xo.univ) (y ≫ pullback.fst _ _)
  have := P.isAb.comm
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.A))
  refine ⟨P, SymBaseChange.hypS_baseChange _ _ Xo.univ.t.G P.A _ g _ _ Xo.univ.t.PP.isLB P.isLB hG hL (hypS_univ Xo),
    P.A, inferInstance, 𝟙 _, g, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id _).symm rfl, hG, ?_⟩
  exact LBIso.trans (pull_isLB P.isLB _) P.isLB (pull_isLB Xo.univ.t.PP.isLB _)
    (LBIso.chartPull (chartPullId _) (chartPullUnpull P.L _ rfl) (PolBaseChange.lbIso_refl (pull_isLB P.isLB _))) hL

theorem exists_uSetup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ η ∈ genericPoints (Xo.XF c), ∀ B : ℕ, ∃ X₁ : USetup C, B ≤ X₁.S.N ∧ ∀ w, X₁.uΩ w = η := by
  intro E _ _ _ H Dw hpq l Xo c C η hη B
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  obtain ⟨A, _, φ, j, P, _, hφ, hjs, hjo, hjx⟩ :=
    exists_chart (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) η
  let ev : A →+* P.ResidueField := algebraMap A P.ResidueField
  let y : Sp P.ResidueField ⟶ Xo.XF c := spMap ev ≫ j
  have hy : ∀ w, y w = η := fun w => by
    have hp : spMap ev w = ⟨P, inferInstance⟩ := by
      refine PrimeSpectrum.ext ?_
      show Ideal.comap ev w.asIdeal = P
      rw [Subsingleton.elim w (⊥ : PrimeSpectrum P.ResidueField)]
      exact Ideal.ker_algebraMap_residueField _
    show j (spMap ev w) = η
    rw [hp, hjx]
  haveI : CharZero P.ResidueField := (ev.comp φ).charZero_iff (ev.comp φ).injective |>.1 inferInstance
  obtain ⟨A₀, hS₀, hU₀⟩ := exists_fibre Xo c y
  have ho : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_level A₀.g H.d H.d_prime.two_le B
  obtain ⟨Ω, _, f, A₁, ψ, ze, hf, hA₁, hze, ⟨lev⟩⟩ :=
    exists_level_finite P.ResidueField A₀ ((H.d ^ j₁ * (H.d ^ k) ^ 2) ^ 2) (Nat.one_le_iff_ne_zero.2 (by
      have := H.d_prime.pos; positivity))
  haveI : CharZero Ω := f.charZero_iff f.injective |>.1 inferInstance
  have hU₁ : UOver Xo c A₁ (RingHom.id Ω) (spMap f ≫ y) := by
    refine (uOver_baseChange_iff hA₁.2.1 (LBIso.symm hA₁.2.2) (RingHom.id Ω)).2 ?_
    rw [RingHom.id_comp]
    simpa only [RingHom.comp_id] using hU₀.comp f
  have hS₁ : HypS A₁.A A₁.L := by
    have := A₀.isAb.comm
    have := A₁.isAb.comm
    exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A₀.isLB A₁.isLB hA₁.2.1 (LBIso.symm hA₁.2.2) hS₀
  letI : Algebra C.o c.F := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  let β : c.F →+* Ω := f.comp (ev.comp φ)
  obtain ⟨o₁, _, _, κ, ze₁, hded, hκ, hinj, hcomp, hze₁⟩ :=
    exists_base_root C.o c.F Ω β ze _ (Nat.one_le_iff_ne_zero.2 (by have := H.d_prime.pos; positivity)) hze
  have hft : Algebra.FiniteType ℤ o₁ := by
    letI := κ.toAlgebra
    haveI := C.ft
    haveI : Algebra.FiniteType C.o o₁ := hκ.finiteType
    exact Algebra.FiniteType.trans C.ft this
  haveI : ArithBase o₁ Ω := ⟨hded, hft, inferInstance, hinj⟩
  have hun : IsUnit (H.d : o₁) := by simpa using C.unit_d.map κ
  rw [← hze₁] at lev
  have hβ : β.EssFiniteType :=
    RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp hφ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := A) (S := P.ResidueField)).2 inferInstance)) hf.finiteType.essFiniteType
  obtain ⟨R₀, hR₀, hfr, hR₀e⟩ := exists_fg_ratHull C.b (fun y => exists_int_mul_mem y) κ β hcomp hβ φ hφ (f.comp ev) rfl
  let u₀ : Sp (ratHull R₀) ⟶ Xo.XF c := spMap ((f.comp ev).codRestrict (ratHull R₀) hR₀e) ≫ j
  have hu₀ : spMap (ratHull R₀).val.toRingHom ≫ u₀ = spMap f ≫ y := by
    simp only [u₀, y, ← Category.assoc, ← Spec.map_comp]; rfl
  obtain ⟨S, ρ, u, hN, hr, hg, hUS, hpt⟩ :=
    exists_thetaSys_uOver Xo c R₀ hR₀ hfr u₀ A₁ (hu₀ ▸ hU₁) hS₁ H.d k j₁ H.d_prime ho hk hj₁ hun ze₁ lev
  have hbig : S.Big := big j₁ le_rfl o₁ Ω S (hg.trans hA₁.1) hN hr
  have hp : spMap (ratHull S.R).val.toRingHom ≫ u = spMap f ≫ spMap ev ≫ j := hpt.trans hu₀
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  haveI := C.isPreimmersion_i
  haveI : SurjectiveOnStalks (spMap ev) :=
    (SurjectiveOnStalks.Spec_iff (φ := CommRingCat.ofHom ev)).2 (Ideal.surjectiveOnStalks_residueField P)
  have hi : C.i ≫ C.z = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ spMap C.b := by
    simp only [UCompact.i, Category.assoc, pullback.condition]
    rw [← Category.assoc, C.iF_over]
  have hpz : (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z = spMap ((algebraMap o₁ Ω).comp κ) := by
    rw [show (spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i) ≫ C.z =
      (spMap (ratHull S.R).val.toRingHom ≫ u) ≫ (C.i ≫ C.z) by simp only [Category.assoc], hp, hi]
    simp only [Category.assoc]
    rw [← Category.assoc j, hjs, hcomp]
    simp only [← Spec.map_comp]
    rfl
  have hst : ((spMap (ratHull S.R).val.toRingHom ≫ u ≫ C.i).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
    rw [← Category.assoc, hp, Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (finite_stalkMap_field f hf _)
      (RingHom.Finite.of_surjective _ (Scheme.Hom.stalkMap_surjective _ _))
  obtain ⟨Mdl, π, hMn, hπ, hMp⟩ := GlobalTheory.Poinc.exists_ratModel_normalization C.o o₁ Ω κ hκ C.Z C.z inferInstance
    inferInstance inferInstance _ hpz hst
  have hgen : ∀ w, (spMap (ratHull S.R).val.toRingHom ≫ u) w = η := fun w => by
    rw [hp]
    exact hy _
  exact ⟨⟨o₁, Ω, S, ρ, hbig, u, hUS, fun w => (hgen w).symm ▸ hη, Mdl, GlobalTheory.IsNormalScheme.of_pred hMn, π, hπ, hMp⟩, hN ▸ hBk, hgen⟩

end GlobalTheory.UPoinc.GSetup
