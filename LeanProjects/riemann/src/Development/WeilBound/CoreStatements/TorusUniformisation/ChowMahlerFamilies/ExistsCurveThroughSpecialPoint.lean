import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsCurveOfFunctionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsPrimeDimOneAvoiding
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurveExistence

open IsLocalRing

theorem alg (O B S D : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] [CommRing S] [Algebra B S] [IsLocalization.AtPrime S m]
    [CommRing D] [IsDomain D] (π : S →+* D) (hπ : Function.Surjective π) (hd : ringKrullDim D = 1)
    (h0 : ∀ o ∈ maximalIdeal O, π (algebraMap B S (algebraMap O B o)) = 0) :
    ∃ (_ : Algebra (ResidueField O) (FractionRing D)),
      (∀ o, algebraMap (ResidueField O) (FractionRing D) (residue O o) =
        algebraMap D (FractionRing D) (π (algebraMap B S (algebraMap O B o)))) ∧
      (⊤ : IntermediateField (ResidueField O) (FractionRing D)).FG ∧
      Algebra.trdeg (ResidueField O) (FractionRing D) = 1 := by
  let χ : B →+* D := π.comp (algebraMap B S)
  let p : Ideal B := RingHom.ker χ
  haveI hp : p.IsPrime := RingHom.ker_isPrime χ
  have hpm : p ≤ m := fun b hb => by
    by_contra hbm
    have hu : IsUnit (algebraMap B S b) := IsLocalization.map_units S (⟨b, hbm⟩ : m.primeCompl)
    exact (hu.map π).ne_zero hb
  let B' := B ⧸ p
  let c : ResidueField O →+* B' := Ideal.Quotient.lift (maximalIdeal O)
    ((Ideal.Quotient.mk p).comp (algebraMap O B)) fun o ho => Ideal.Quotient.eq_zero_iff_mem.2 (h0 o ho)
  letI : Algebra (ResidueField O) B' := c.toAlgebra
  haveI : IsScalarTower O (ResidueField O) B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType O B' := inferInstanceAs (Algebra.FiniteType O (B ⧸ p))
  haveI : Algebra.FiniteType (ResidueField O) B' := Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  letI : Algebra B' D := (RingHom.kerLift χ).toAlgebra
  have hinj : Function.Injective (algebraMap B' D) := RingHom.kerLift_injective χ
  have hab : ∀ b : B, algebraMap B' D (Ideal.Quotient.mk p b) = π (algebraMap B S b) := fun _ => rfl
  let m' : Ideal B' := m.map (Ideal.Quotient.mk p)
  have hcm : m'.comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hpm]
  haveI hm' : m'.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hm).resolve_left fun h => by
      apply hm.ne_top
      rw [← hcm]
      change Ideal.comap _ (Ideal.map _ _) = _
      rw [h, Ideal.comap_top]
  have hmem : ∀ b : B, Ideal.Quotient.mk p b ∈ m' ↔ b ∈ m := fun b => by
    rw [← Ideal.mem_comap, hcm]
  haveI : IsLocalization.AtPrime D m' := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hb : b ∉ m := fun h => hy ((hmem b).2 h)
      exact (IsLocalization.map_units S (⟨b, hb⟩ : m.primeCompl)).map π
    · intro z
      obtain ⟨t, rfl⟩ := hπ z
      obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj m.primeCompl t
      refine ⟨⟨Ideal.Quotient.mk p a, ⟨Ideal.Quotient.mk p b, fun h => b.2 ((hmem b).1 h)⟩⟩, ?_⟩
      change π t * π (algebraMap B S b) = π (algebraMap B S a)
      rw [← map_mul, e]
    · intro a b e
      exact ⟨1, by rw [hinj e]⟩
  have hht : (m'.height : WithBot ℕ∞) = 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m' D, hd]
  have hB' : ringKrullDim B' = 1 := by
    rw [← GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (ResidueField O) m', hht,
      ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m').1 hm'), add_zero]
  obtain ⟨n, hn, htr⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (ResidueField O) (A := B')
  have hn1 : n = 1 := by
    rw [hB'] at hn
    exact_mod_cast hn.symm
  subst hn1
  letI : Algebra (ResidueField O) D := ((algebraMap B' D).comp c).toAlgebra
  haveI : IsScalarTower (ResidueField O) B' D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul B' D := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Algebra.IsAlgebraic B' D := IsLocalization.isAlgebraic D m'.primeCompl
  haveI : FaithfulSMul (ResidueField O) B' := (faithfulSMul_iff_algebraMap_injective _ _).2 c.injective
  have hD : Algebra.trdeg (ResidueField O) D = 1 := by
    rw [← trdeg_add_eq (ResidueField O) B' (A := D), trdeg_eq_zero (R := B') (A := D), add_zero, htr, Nat.cast_one]
  refine ⟨inferInstance, fun o => rfl, ?_, ?_⟩
  · rw [IntermediateField.fg_top_iff]
    haveI : Algebra.EssFiniteType B' D := Algebra.EssFiniteType.of_isLocalization D m'.primeCompl
    haveI : Algebra.EssFiniteType D (FractionRing D) :=
      Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors D)
    haveI := Algebra.EssFiniteType.comp (ResidueField O) B' D
    exact Algebra.EssFiniteType.comp (ResidueField O) D _
  · rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (ResidueField O) (A := D), hD]

theorem chart {X : Scheme.{0}} {O : Type} [CommRing O] [IsLocalRing O] (s : X ⟶ Spec (CommRingCat.of O))
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ β : O →+* X.presheaf.stalk x, X.fromSpecStalk x ≫ s = Spec.map (CommRingCat.ofHom β) ∧
      ∀ (D : Type) [CommRing D] [IsDomain D] (π : X.presheaf.stalk x →+* D), Function.Surjective π →
        ringKrullDim D = 1 → (∀ o ∈ maximalIdeal O, π (β o) = 0) →
        ∃ (_ : Algebra (ResidueField O) (FractionRing D)),
          (∀ o, algebraMap (ResidueField O) (FractionRing D) (residue O o) =
            algebraMap D (FractionRing D) (π (β o))) ∧
          (⊤ : IntermediateField (ResidueField O) (FractionRing D)).FG ∧
          Algebra.trdeg (ResidueField O) (FractionRing D) = 1 := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let ψ : CommRingCat.of O ⟶ Γ(X, U) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appLE ⊤ U le_top
  have hψ : hU.fromSpec ≫ s = Spec.map ψ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  have hft : ψ.hom.FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2)
  refine ⟨(ψ ≫ X.presheaf.germ U x hxU).hom, ?_, fun D _ _ π hπ hd h0 => ?_⟩
  · rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc, hψ, ← Spec.map_comp]
    rfl
  · letI : Algebra O Γ(X, U) := ψ.hom.toAlgebra
    haveI : Algebra.FiniteType O Γ(X, U) := hft
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    haveI := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    exact alg O Γ(X, U) (X.presheaf.stalk x) D (hU.primeIdealOf ⟨x, hxU⟩).asIdeal π hπ hd h0

theorem val_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    (x : Cpt ξ) {R : Type} [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk x.1 →+* R)
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x.1)) (σ : X.presheaf.stalk x.1) :
    ValAt ξ (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x.1) (genMap ξ x σ) (φ σ) ∧
      (IsUnit (φ σ) → unitAt ξ ⟨_, h⟩ (genMap ξ x σ)) := by
  set η : Spec (CommRingCat.of R) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x.1 with hη
  have hs : centre η ⤳ x.1 := by
    have : centre η ∈ Set.range (X.fromSpecStalk x.1) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have key := ProjectiveLinePlaces.stalk_square hs (𝟙 _) (Scheme.stalkClosedPointTo η) (CommRingCat.ofHom φ)
    ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk η).trans (by rw [Spec.map_id, Category.id_comp]; exact hη))
  have k2 : (Scheme.stalkClosedPointTo η).hom ((X.presheaf.stalkSpecializes hs).hom σ) = φ σ :=
    congrArg (fun g => g.hom σ) key
  have k3 := ProjectiveLinePlaces.genMap_specializes (ξ := ξ) hs h x.2 σ
  refine ⟨⟨h, _, k3, k2⟩, fun hu => (CptModel.unitAt_iff ξ _ _).2 ⟨_, ?_, k3⟩⟩
  have hl := Scheme.isLocalHom_stalkClosedPointTo η
  exact hl.map_nonunit _ (by rw [← k2] at hu; exact hu)

end PositivityTheory.Xgn.CurveExistence

open IsLocalRing PositivityTheory.Xgn.CurveExistence in
theorem PositivityTheory.Xgn.exists_curve_through_special_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ _ hs hξ y x g hy hyx hx hg hgy hgx
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨β, hβ, hfun⟩ := chart s x.1 hx
  obtain ⟨γ, rfl⟩ := hg
  have hξx : Spec.map (CommRingCat.ofHom (genMap ξ x)) ≫ X.fromSpecStalk x.1 = ξ := by
    exact (congrArg (· ≫ X.fromSpecStalk x.1)
      (Spec.map_comp (X.presheaf.stalkSpecializes x.2) (Scheme.stalkClosedPointTo ξ))).trans
      ((Category.assoc _ _ _).trans ((congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk x.2)).trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))
  have hcomp : ∀ {R : Type} [CommRing R] (φ : X.presheaf.stalk x.1 →+* R),
      (Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x.1) ≫ s = Spec.map (CommRingCat.ofHom (φ.comp β)) := by
    intro R _ φ
    rw [Category.assoc, hβ, ← Spec.map_comp]
    rfl
  have hβo : ∀ o, genMap ξ x (β o) = algebraMap O Ω o := fun o => by
    have e := hcomp (genMap ξ x)
    rw [hξx, hs] at e
    exact (congrArg (fun f => f.hom o) (Spec.map_injective e)).symm
  let ρ : X.presheaf.stalk x.1 →+* X.presheaf.stalk y.1 := (X.presheaf.stalkSpecializes hyx).hom
  let q : Ideal (X.presheaf.stalk x.1) := (maximalIdeal _).comap ρ
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hqm : ∀ σ, σ ∉ q ↔ unitAt ξ y (genMap ξ x σ) := fun σ => by
    have e0 : genMap ξ y (ρ σ) = genMap ξ x σ := ProjectiveLinePlaces.genMap_specializes hyx y.2 x.2 σ
    rw [← e0, CptModel.unitAt_iff]
    change ¬ (ρ σ ∈ maximalIdeal _) ↔ _
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨t, ht, e⟩ => hξ.inj y e ▸ ht⟩
  have hγq : γ ∉ q := (hqm γ).2 hgy
  have hγu : ¬ IsUnit γ := fun h => hgx ((CptModel.unitAt_iff ξ x _).2 ⟨γ, h, rfl⟩)
  have hϖq : β ϖ ∈ q := by
    by_contra h
    exact hy (hβo ϖ ▸ (hqm _).1 h)
  haveI : IsLocalRing (X.presheaf.stalk x.1 ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hγ0 : Ideal.Quotient.mk q γ ≠ 0 := fun h => hγq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  obtain ⟨P, hP, hγP, hd⟩ := PositivityTheory.Xgn.exists_prime_dim_one_avoiding (X.presheaf.stalk x.1 ⧸ q) (Ideal.Quotient.mk q γ) hγ0
    fun hF => by
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel hγ0
      exact hγu (IsLocalHom.map_nonunit γ (IsUnit.of_mul_eq_one b hb))
  let D := (X.presheaf.stalk x.1 ⧸ q) ⧸ P
  let π : X.presheaf.stalk x.1 →+* D := (Ideal.Quotient.mk P).comp (Ideal.Quotient.mk q)
  have hπq : ∀ σ ∈ q, π σ = 0 := fun σ h => by
    change Ideal.Quotient.mk P (Ideal.Quotient.mk q σ) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  obtain ⟨alg, halg, hfg, htr⟩ := hfun D π (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective) hd
    fun o ho => by
      rw [hϖ.maximalIdeal_eq] at ho
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      rw [map_mul, map_mul, hπq _ hϖq, mul_zero]
  let φ : X.presheaf.stalk x.1 →+* FractionRing D := (algebraMap D (FractionRing D)).comp π
  have hφγ : φ γ ≠ 0 := fun h => hγP (Ideal.Quotient.eq_zero_iff_mem.1
    ((map_eq_zero_iff _ (IsFractionRing.injective D (FractionRing D))).1 h))
  have hφq : ∀ σ ∈ q, φ σ = 0 := fun σ h => by
    change algebraMap D _ (π σ) = 0
    rw [hπq σ h, map_zero]
  let η : Spec (CommRingCat.of (FractionRing D)) ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x.1
  have hyη : y.1 ⤳ centre η := by
    have e1 : y.1 = X.fromSpecStalk x.1 (⟨q, hq⟩ : PrimeSpectrum _) := by
      have := congrArg (fun f => f (closedPoint (X.presheaf.stalk y.1)))
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hyx)
      exact (Scheme.fromSpecStalk_closedPoint.symm.trans this.symm :)
    have e2 : (⟨q, hq⟩ : PrimeSpectrum _) ⤳ PrimeSpectrum.comap φ (closedPoint _) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 fun σ h => by
        change φ σ ∈ maximalIdeal _
        rw [hφq σ h]
        exact zero_mem _
    rw [e1]
    exact e2.map (X.fromSpecStalk x.1).continuous
  have hη : genPt ξ ⤳ centre η := y.2.trans hyη
  obtain ⟨C, hw, htriv, -, hall⟩ := exists_curve_of_function_field _ _ hfg htr
  have hk : ∀ i (a : ResidueField O), algebraMap _ (FractionRing D) a ∈ (C.v i).valuationSubring := fun i a => by
    change C.v i _ ≤ 1
    by_cases h : a = 0
    · simp [h]
    · exact (htriv i a h).le
  let b : ∀ i, O →+* (C.v i).valuationSubring := fun i =>
    (φ.comp β).codRestrict _ fun o => (halg o) ▸ hk i (residue O o)
  have hz := fun i => existsUnique_valuationRing_lift O (C.v i).valuationSubring (FractionRing D) (b i) X s η
    (hcomp φ)
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ
  obtain ⟨i, rfl, -⟩ := hall W (by
      rintro rfl
      refine hγu (hloc.map_nonunit γ (IsUnit.of_mul_eq_one ⟨(φ γ)⁻¹, trivial⟩ (Subtype.ext ?_)))
      exact mul_inv_cancel₀ hφγ)
    fun a => by
      obtain ⟨o, rfl⟩ := residue_surjective a
      rw [halg]
      exact hW (β o)
  let φ' : X.presheaf.stalk x.1 →+* (C.v i).valuationSubring := φ.codRestrict _ hW
  haveI : IsLocalHom φ' := hloc
  have hzi : Spec.map (CommRingCat.ofHom φ') ≫ X.fromSpecStalk x.1 = (hz i).choose :=
    (hz i).choose_spec.2 _ ⟨by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl, hcomp φ'⟩
  have h0 : ValAt ξ η (algebraMap O Ω ϖ) 0 := by
    have := (val_stalk hξ x φ hη (β ϖ)).1
    rwa [hβo, hφq _ hϖq] at this
  refine ⟨{ k := ResidueField O, κ := FractionRing D, fg := hfg, trdeg := htr, C := C, w_pos := hw, triv := htriv,
            all := hall, η := η, η_spec := hη, η_zero := h0, z := fun j => (hz j).choose,
            z_gen := fun j => (hz j).choose_spec.1.1 }, i, hyη,
    (val_stalk hξ x φ hη γ).2 (IsUnit.mk0 _ hφγ), ?_⟩
  change centre (hz i).choose = x.1
  rw [← hzi]
  change X.fromSpecStalk x.1 (PrimeSpectrum.comap φ' (closedPoint _)) = x.1
  rw [comap_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint
