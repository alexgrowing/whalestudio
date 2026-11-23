import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SpanEqTopOfForallMaximal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLoc

section Chart

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem univChart_of_standardSmooth (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) (ε : S →ₐ[R] R) (hε : spMap ε ≫ j = 1)
    (hj : ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) →
      ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ φ : S →ₐ[R] A, y = spMap φ ≫ j)
    (hinj : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : S →ₐ[R] A),
      spMap φ ≫ j = spMap φ' ≫ j → φ = φ') :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G, IsUnivChart G n x := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  letI : Algebra (MvPolynomial (Fin n) R) S := g.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) S := hg
  have hπ : ∀ m : ℕ, ∃ π : S →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε ∧
      ∀ i, π (sX R i) = algebraMap R _ (ε (sX R i)) + zR m i := fun m =>
    etale_exists (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun i => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨fun m => spMap (π m) ≫ j, fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, spMap_comp]
    congr 2
    refine etale_ext (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro i
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · have e : (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε := by
      refine etale_ext (n := n) ε (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
        exact hπaug m
      · ext s
        simp
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
        rfl
    rw [← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hε, comp_one']
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    obtain ⟨φ, rfl⟩ := hj A aug hJn y hy
    have hφ : aug.comp φ = ε := hinj _ _ _ (by rw [← spMap_comp, Category.assoc, hy, hε])
    have hmem : ∀ i : Fin n, φ (sX (S := S) R i) - algebraMap R A (ε (sX (S := S) R i)) ∈
        RingHom.ker aug := by
      intro i
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun i : Fin n => φ (sX (S := S) R i) - algebraMap R A (ε (sX (S := S) R i))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun i => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem i
    have hψπ : ψ.comp (π m) = φ := by
      refine etale_ext (n := n) ε aug hJn _ _ ?_ hφ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, ?_⟩, ?_⟩
    · rw [← Category.assoc, spMap_comp, hψπ]
    · rintro ψ₂ ⟨_, h2⟩
      rw [← Category.assoc, spMap_comp] at h2
      have h4 := (hinj _ _ _ h2).symm
      apply jet_ext
      intro i
      rw [jetLift_zR]
      have := AlgHom.congr_fun h4 (sX R i)
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
      rw [← this, add_sub_cancel_left]

theorem univChart_baseChange (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) [IsOpenImmersion j.left] (R' : Type) [CommRing R'] [Algebra R R']
    (ε : S →ₐ[R] R') (hε : spMap ε ≫ j = 1) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x := by
  let inc : S →ₐ[R] R' ⊗[R] S := Algebra.TensorProduct.includeRight
  let j' : sp (R₀ := R') (R' ⊗[R] S) ⟶ (Over.pullback (fB R R')).obj G := pullR G (spMap inc ≫ j)
  have hpush : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : R' ⊗[R] S →ₐ[R'] A), pushR G (spMap φ ≫ j') = spMap ((φ.restrictScalars R).comp inc) ≫ j := by
    intro A _ _ _ _ φ
    rw [pushR_spMap, pushR_pullR, ← Category.assoc, spMap_comp]
  have hlift : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : S →ₐ[R] A), ∃ φ' : R' ⊗[R] S →ₐ[R'] A, (φ'.restrictScalars R).comp inc = φ := by
    intro A _ _ _ _ φ
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId R' A) φ fun _ _ => Commute.all _ _, ?_⟩
    ext s
    simp [inc]
  obtain ⟨ε', hε'⟩ := hlift R' ε
  refine univChart_of_standardSmooth _ n (R' ⊗[R] S) j' ε' ?_ ?_ ?_
  · apply pushR_inj G
    rw [hpush, hε', hε, pushR_one]
  · intro A _ _ aug hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = spMap ε ≫ j := by
      rw [← pushR_spMap, hy, pushR_one, hε]
    obtain ⟨φ, h1, -⟩ := SqZero.exists_chart_pt_of_nil j (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ hJ a ha) _ _ hz
    obtain ⟨φ', h2⟩ := hlift A φ
    refine ⟨φ', pushR_inj G ?_⟩
    rw [hpush, h2, h1]
  · intro A _ _ φ φ' h
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 := congrArg (pushR G) h
    rw [hpush, hpush] at h1
    have h2 := SqZero.chart_inj j h1
    exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) h2

theorem exists_standardSmooth_chart (X : Over (Spec (CommRingCat.of R))) (n : ℕ)
    (h : SmoothOfRelativeDimension n X.hom) (x : X.left) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ X),
      Algebra.IsStandardSmoothOfRelativeDimension n R S ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  obtain ⟨B, j₀, hj₀, ⟨q, hq⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := x) (U := ⊤) trivial
  letI : Algebra R B := (Spec.preimage (j₀ ≫ X.hom)).hom.toAlgebra
  let j : sp (R₀ := R) B ⟶ X := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ X.hom)).symm
  have h1 : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    have e : j₀ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w j
    rw [← e, ← zero_add n]
    infer_instance
  obtain ⟨s, hs, H⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := CommRingCat.ofHom (algebraMap R B))).1 h1
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ (q : PrimeSpectrum B).asIdeal := by
    by_contra! hc
    exact (q : PrimeSpectrum B).2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hq' : (q : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    exact htq
  obtain ⟨q', hq'⟩ := hq'
  have Ht := H t hts
  rw [CommRingCat.hom_ofHom, ← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at Ht
  refine ⟨Localization.Away t, inferInstance, inferInstance, spMap (SqZero.awayHom R t) ≫ j, Ht, ?_,
    q', ?_⟩
  · change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))) ≫ j₀)
    infer_instance
  · rw [← hq, ← hq']
    rfl

theorem exists_univChart_away (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (h : SmoothOfRelativeDimension n G.hom) (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, ∃ x : ∀ m : ℕ, sp (R₀ := Localization.Away r)
      (JetR (Localization.Away r) (Fin n) m) ⟶ (Over.pullback (fB R (Localization.Away r))).obj G,
      IsUnivChart _ n x := by
  let e : Spec (CommRingCat.of R) ⟶ G.left := η[G].left
  obtain ⟨S, _, _, j, hS, hj, hmem⟩ := exists_standardSmooth_chart G n h (e p)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (e ⁻¹ᵁ j.left.opensRange).1) hmem (e ⁻¹ᵁ j.left.opensRange).2
  refine ⟨r, hr, ?_⟩
  obtain ⟨ε, hε⟩ := SqZero.exists_chart_pt j (1 : sp (R₀ := R) (Localization.Away r) ⟶ G) (by
    rintro _ ⟨t, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this)
  exact univChart_baseChange G n S j _ ε hε.symm

end Chart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lie_locally_free :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
      SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
        ∃ v : Fin n → (epsR (Localization.Away r) ⟶
          (Over.pullback (spMap (algebraMap R (Localization.Away r)))).obj G), IsLieBasis v := by
  intro R _ G _ _ n h p
  obtain ⟨r, hr, x, hx⟩ := exists_univChart_away G n h p
  exact ⟨r, hr, _, Chart.basis_of_chart hx⟩

end GlobalTheory.LieLoc
