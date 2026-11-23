import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AdaptedParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem formallySmooth_of_etaleChart {X₁ : Scheme.{u}} {k₁ : Type u} [Field k₁]
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {U₁ : X₁.Opens} {m₁ : ℕ}
    [Algebra k₁ Γ(X₁, U₁)]
    (hk : algebraMap k₁ Γ(X₁, U₁) = sectionsAlgebraMap k₁ p₁ U₁)
    (hU : IsAffineOpen U₁) (c : EtaleChart p₁ U₁ m₁) :
    Algebra.FormallySmooth k₁ Γ(X₁, U₁) := by
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) := c.algebra
  have instT : IsScalarTower k₁ (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [hk, MvPolynomial.algebraMap_eq]
      exact (c.coordRingHom_C a).symm
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁) :=
    c.algebra_formallyEtale hU
  exact Algebra.FormallySmooth.comp k₁ (MvPolynomial (ULift.{u} (Fin m₁)) k₁) Γ(X₁, U₁)

private theorem notMem_support_of_restrictIdeal_eq_top_of_mem {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {U : Y.Opens} (h : restrictIdeal I U = ⊤) {y : Y} (hyU : y ∈ U) : y ∉ I.support := by
  intro hy
  have h1 : (⟨y, hyU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hy
  rw [← restrictIdeal_eq_comap_ι, h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨y, hyU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2

private theorem exists_isUnit_mul_of_span_singleton_eq {R : Type*} [CommRing R] {y z : R}
    (hy : y ∈ nonZeroDivisors R) (hsp : Ideal.span {z} = Ideal.span {y}) :
    ∃ u : R, IsUnit u ∧ z = u * y := by
  have hz : z ∈ Ideal.span {y} := by
    rw [← hsp]
    exact Ideal.mem_span_singleton_self z
  have hy' : y ∈ Ideal.span {z} := by
    rw [hsp]
    exact Ideal.mem_span_singleton_self y
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy'
  have hsub : (b * u - 1) * y = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hu, hb, sub_self]
  have hcancel : ∀ w : R, w * y = 0 → w = 0 := (mem_nonZeroDivisors_iff.mp hy).2
  have h1 : b * u - 1 = 0 := hcancel _ hsub
  have h2 : b * u = 1 := by
    rw [sub_eq_zero] at h1
    exact h1
  have h3 : u * b = 1 := by
    rw [mul_comm]
    exact h2
  exact ⟨u, ⟨⟨u, b, h3, h2⟩, rfl⟩, hu.symm⟩

private theorem repr_sum_smul_apply {ι₀ : Type*} [Fintype ι₀]
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι₀ R M) (cc : ι₀ → R) (i : ι₀) :
    b.repr (∑ j : ι₀, cc j • b j) i = cc i := by
  rw [Module.Basis.repr_sum_self]

private theorem basisKaehler_repr_kaehlerMap (k₀ : Type*) [CommRing k₀] (ι₀ : Type*) [Fintype ι₀]
    [DecidableEq ι₀] (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
    [Algebra k₀ S] [Algebra k₀ S'] [Algebra (MvPolynomial ι₀ k₀) S]
    [Algebra (MvPolynomial ι₀ k₀) S'] [Algebra S S']
    [IsScalarTower k₀ (MvPolynomial ι₀ k₀) S] [IsScalarTower k₀ (MvPolynomial ι₀ k₀) S']
    [IsScalarTower k₀ S S'] [IsScalarTower (MvPolynomial ι₀ k₀) S S']
    [Algebra.FormallyEtale (MvPolynomial ι₀ k₀) S]
    [Algebra.FormallyEtale (MvPolynomial ι₀ k₀) S']
    (ω : KaehlerDifferential k₀ S) (i : ι₀) :
    (EtaleCoordinates.basisKaehler k₀ ι₀ S').repr (KaehlerDifferential.map k₀ k₀ S S' ω) i
      = algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω i) := by
  have hb : ∀ j : ι₀,
      KaehlerDifferential.map k₀ k₀ S S' (EtaleCoordinates.basisKaehler k₀ ι₀ S j)
        = EtaleCoordinates.basisKaehler k₀ ι₀ S' j := by
    intro j
    simp only [EtaleCoordinates.basisKaehler_apply, KaehlerDifferential.map_D,
      EtaleCoordinates.algebraMap_coord]
  have hω : ω = ∑ j : ι₀, (EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j •
      EtaleCoordinates.basisKaehler k₀ ι₀ S j :=
    ((EtaleCoordinates.basisKaehler k₀ ι₀ S).sum_repr ω).symm
  have key : KaehlerDifferential.map k₀ k₀ S S' ω
      = ∑ j : ι₀, algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j) •
        EtaleCoordinates.basisKaehler k₀ ι₀ S' j := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j)
      (EtaleCoordinates.basisKaehler k₀ ι₀ S' j)
  rw [key]
  exact repr_sum_smul_apply (EtaleCoordinates.basisKaehler k₀ ι₀ S')
    (fun j => algebraMap S S' ((EtaleCoordinates.basisKaehler k₀ ι₀ S).repr ω j)) i

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  [AlgebraicGeometry.Smooth p] {V : X.Opens} {n : ℕ}

theorem exists_etaleChart_coord_eq_of_isUnit_jacobianDet (hV : IsAffineOpen V)
    (c : EtaleChart p V n) (w : ULift.{u} (Fin n) → Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) →
      ∃ c' : EtaleChart p V n, ∀ j : Fin n, c'.coord j = w (ULift.up j) := by
  intro hdet0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have instFS : Algebra.FormallySmooth k Γ(X, V) := formallySmooth_of_etaleChart hk hV c
  have hdet : IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) := hdet0
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, V),
        (∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p V a) ∧
        (∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) = w i) ∧
        @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) _ _
          f.toAlgebra := by
    refine ⟨(MvPolynomial.aeval (R := k) w).toRingHom, fun a => ?_, fun i => ?_, ?_⟩
    · show MvPolynomial.aeval w (MvPolynomial.C a) = sectionsAlgebraMap k p V a
      rw [MvPolynomial.aeval_C, hk]
    · show MvPolynomial.aeval w (MvPolynomial.X i) = w i
      rw [MvPolynomial.aeval_X]
    · exact EtaleCoordinates.formallyEtale_aeval_of_isUnit_det
        (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)) w hdet
  exact exists_etaleChart_coord_eq p hV w f hfC hfX
    (ringHom_etale_of_formallyEtale p hV f hfC hfEtale)

theorem exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem
    (hV : IsAffineOpen V) (c : EtaleChart p V n) {x : X} (hx : x ∈ V)
    (w : ULift.{u} (Fin n) → Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal →
      ∃ (V' : X.Opens) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        ∀ j : Fin n,
          c'.coord j = (X.presheaf.map (homOfLE hV'V).op).hom (w (ULift.up j)) := by
  intro hg0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  obtain ⟨g, hgd⟩ : ∃ g : Γ(X, V),
      g = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i) := ⟨_, rfl⟩
  have hg : g ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hgd]
    exact hg0
  have hle : X.basicOpen g ≤ V := X.basicOpen_le g
  have hVg : IsAffineOpen (X.basicOpen g) := hV.basicOpen g
  have hxg : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hV hx g hg
  let instk' : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  let instAlg : Algebra Γ(X, V) Γ(X, X.basicOpen g) :=
    (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have halg : ∀ z : Γ(X, V),
      algebraMap Γ(X, V) Γ(X, X.basicOpen g) z =
        (X.presheaf.map (homOfLE hle).op).hom z := fun _ => rfl
  have instScalarTower : IsScalarTower k Γ(X, V) Γ(X, X.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg]
      exact (FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply k p hle a).symm
  have instLoc : IsLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) :=
    hV.isLocalization_basicOpen g
  have hunit : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen g)
      ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
        fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i))) := by
    rw [← hgd]
    exact IsLocalization.map_units (M := Submonoid.powers g) Γ(X, X.basicOpen g)
      ⟨g, Submonoid.mem_powers g⟩
  obtain ⟨e, he⟩ := exists_basis_isUnit_det_of_isLocalization (k := k)
    (S' := Γ(X, X.basicOpen g)) (Submonoid.powers g) w hunit
  have instFS : Algebra.FormallySmooth k Γ(X, X.basicOpen g) :=
    formallySmooth_of_etaleChart (algebraMap_sectionsAlgebra k p (X.basicOpen g)) hVg
      (c.restrict hle)
  obtain ⟨f, hfC, hfX, hfEtale⟩ :
      ∃ f : MvPolynomial (ULift.{u} (Fin n)) k →+* Γ(X, X.basicOpen g),
        (∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a) ∧
        (∀ i : ULift.{u} (Fin n), f (MvPolynomial.X i) =
          algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) ∧
        @Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, X.basicOpen g) _ _
          f.toAlgebra := by
    refine ⟨(MvPolynomial.aeval (R := k)
      (fun i : ULift.{u} (Fin n) =>
        algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))).toRingHom,
      fun a => ?_, fun i => ?_, ?_⟩
    · show MvPolynomial.aeval
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))
        (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a
      rw [MvPolynomial.aeval_C, algebraMap_sectionsAlgebra k p (X.basicOpen g)]
    · show MvPolynomial.aeval
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i))
        (MvPolynomial.X i) = algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)
      rw [MvPolynomial.aeval_X]
    · exact EtaleCoordinates.formallyEtale_aeval_of_isUnit_det e
        (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) he
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p hVg
    (fun i : ULift.{u} (Fin n) => algebraMap Γ(X, V) Γ(X, X.basicOpen g) (w i)) f hfC hfX
    (ringHom_etale_of_formallyEtale p hVg f hfC hfEtale)
  exact ⟨X.basicOpen g, hVg, hle, hxg, c', fun j => (hc' j).trans (halg _)⟩

theorem exists_etaleChart_coord_add_smul (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) (t : k) :
    ∃ c' : EtaleChart p V n,
      c'.coord j₂ = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
        ∀ j : Fin n, j ≠ j₂ → c'.coord j = c.coord j := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have hcr : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) = c.coordRingHom :=
    c.algebraMap_eq_coordRingHom
  have hcoord : ∀ j : Fin n,
      EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) = c.coord j :=
    fun j => c.etaleCoordinates_coord j
  have h1 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₂) = 1 := by
    rw [← hcoord j₂]
    exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
  have h2 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₁) = 0 := by
    rw [← hcoord j₁]
    refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, V)
      (ULift.up j₂) (ULift.up j₁) ?_
    intro hcon
    exact hj (congrArg ULift.down hcon).symm
  have h3 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (sectionsAlgebraMap k p V t) = 0 := by
    rw [← hk]
    simp
  have hpd : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₂)
      (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁) = 1 := by
    simp [Derivation.leibniz, h1, h2, h3]
  obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, V),
      w (ULift.up j₂) = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
      (∀ j : Fin n, j ≠ j₂ → w (ULift.up j) = c.coord j) ∧
      (fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) =
        Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)))
          (ULift.up j₂)
          (KaehlerDifferential.D k Γ(X, V)
            (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁)) := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin n) => c.coord i.down) (ULift.up j₂)
      (c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁), ?_, fun j hjne => ?_, ?_⟩
    · rw [Function.update_apply]
      exact if_pos rfl
    · rw [Function.update_apply]
      exact if_neg (fun hcon : ULift.up j = ULift.up j₂ => hjne (congrArg ULift.down hcon))
    · funext i
      rw [Function.update_apply, Function.update_apply]
      by_cases hi : i = ULift.up j₂
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        exact (basisKaehler_apply_eq_D_coord c hk hcr i.down).symm
  have hdet : IsUnit ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) := by
    rw [hwupd, det_update_eq_repr, ← EtaleCoordinates.partialDeriv_apply, hpd]
    exact isUnit_one
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq_of_isUnit_jacobianDet hV c w hdet
  refine ⟨c', ?_, fun j hjne => ?_⟩
  · rw [hc' j₂, hwj]
  · rw [hc' j, hwne j hjne]

theorem exists_etaleChart_update_coord_of_partialDeriv_notMem
    (hV : IsAffineOpen V) (c : EtaleChart p V n) {x : X} (hx : x ∈ V) (j₁ : Fin n)
    (x' : Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₁) x' ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal →
      ∃ (V' : X.Opens) (_ : IsAffineOpen V') (hV'V : V' ≤ V) (_ : x ∈ V')
        (c' : EtaleChart p V' n),
        c'.coord j₁ = (X.presheaf.map (homOfLE hV'V).op).hom x' ∧
          ∀ j : Fin n, j ≠ j₁ →
            c'.coord j = (X.presheaf.map (homOfLE hV'V).op).hom (c.coord j) := by
  intro hpd0
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hpd : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j₁) x' ∉
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal := hpd0
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have hcr : algebraMap (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) = c.coordRingHom :=
    c.algebraMap_eq_coordRingHom
  obtain ⟨w, hwj, hwne, hwupd⟩ : ∃ w : ULift.{u} (Fin n) → Γ(X, V),
      w (ULift.up j₁) = x' ∧
      (∀ j : Fin n, j ≠ j₁ → w (ULift.up j) = c.coord j) ∧
      (fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) =
        Function.update (⇑(EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)))
          (ULift.up j₁) (KaehlerDifferential.D k Γ(X, V) x') := by
    refine ⟨Function.update (fun i : ULift.{u} (Fin n) => c.coord i.down) (ULift.up j₁) x',
      ?_, fun j hjne => ?_, ?_⟩
    · rw [Function.update_apply]
      exact if_pos rfl
    · rw [Function.update_apply]
      exact if_neg (fun hcon : ULift.up j = ULift.up j₁ => hjne (congrArg ULift.down hcon))
    · funext i
      rw [Function.update_apply, Function.update_apply]
      by_cases hi : i = ULift.up j₁
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi]
        exact (basisKaehler_apply_eq_D_coord c hk hcr i.down).symm
  have hdet : ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).det
      fun i : ULift.{u} (Fin n) => KaehlerDifferential.D k Γ(X, V) (w i)) ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [hwupd, det_update_eq_repr, ← EtaleCoordinates.partialDeriv_apply]
    exact hpd
  obtain ⟨V', hV'aff, hle, hxV', c', hc'⟩ :=
    exists_etaleChart_restrict_coord_eq_of_jacobianDet_notMem hV c hx w hdet
  refine ⟨V', hV'aff, hle, hxV', c', ?_, fun j hjne => ?_⟩
  · rw [hc' j₁, hwj]
  · rw [hc' j, hwne j hjne]

def chartPartialDeriv (hV : IsAffineOpen V) (c : EtaleChart p V n) (j : Fin n)
    (f : Γ(X, V)) : Γ(X, V) :=
  letI _instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  letI _instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  haveI _instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  haveI _instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) f

omit [AlgebraicGeometry.Smooth p] in
theorem chartPartialDeriv_eq (hV : IsAffineOpen V) (c : EtaleChart p V n) (j : Fin n)
    (f : Γ(X, V)) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    chartPartialDeriv hV c j f =
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) f :=
  rfl

private theorem derivation_sum_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ι → Derivation R A A) (a : A) :
    (∑ i ∈ s, D i) a = ∑ i ∈ s, D i a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      simp [ih]

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_chainRule {W : X.Opens} (hW : IsAffineOpen W) {n₁ n₂ : ℕ}
    (c₁ : EtaleChart p W n₁) (c₂ : EtaleChart p W n₂) (j : Fin n₂) (f : Γ(X, W)) :
    chartPartialDeriv hW c₂ j f =
      ∑ i : Fin n₁, chartPartialDeriv hW c₂ j (c₁.coord i) * chartPartialDeriv hW c₁ i f := by
  classical
  let instk : Algebra k Γ(X, W) := sectionsAlgebra k p W
  obtain ⟨D, hD⟩ : ∃ D : Derivation k Γ(X, W) Γ(X, W),
      ∀ z : Γ(X, W), D z = chartPartialDeriv hW c₂ j z := by
    let instc₂ : Algebra (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) := c₂.algebra
    have instT₂ : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) :=
      c₂.isScalarTower
    have instFE₂ : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n₂)) k) Γ(X, W) :=
      c₂.algebra_formallyEtale hW
    exact ⟨EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₂)) Γ(X, W) (ULift.up j),
      fun _ => rfl⟩
  let instc₁ : Algebra (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) := c₁.algebra
  have instT₁ : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) :=
    c₁.isScalarTower
  have instFE₁ : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n₁)) k) Γ(X, W) :=
    c₁.algebra_formallyEtale hW
  have hcoord : ∀ i : ULift.{u} (Fin n₁),
      EtaleCoordinates.coord k (ULift.{u} (Fin n₁)) Γ(X, W) i = c₁.coord i.down := by
    rintro ⟨i⟩
    exact c₁.etaleCoordinates_coord i
  have hpd : ∀ i : ULift.{u} (Fin n₁),
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) i f =
        chartPartialDeriv hW c₁ i.down f := by
    rintro ⟨i⟩
    rfl
  have hsum := EtaleCoordinates.eq_sum_smul_partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) D
  have happ : D f = ∑ i : ULift.{u} (Fin n₁),
      D (EtaleCoordinates.coord k (ULift.{u} (Fin n₁)) Γ(X, W) i) *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n₁)) Γ(X, W) i f := by
    conv_lhs => rw [hsum]
    rw [derivation_sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hbij : Function.Bijective (fun i : ULift.{u} (Fin n₁) => i.down) := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ hab
      exact congrArg ULift.up hab
    · intro b
      exact ⟨ULift.up b, rfl⟩
  rw [← hD f, happ]
  refine Fintype.sum_bijective (fun i : ULift.{u} (Fin n₁) => i.down) hbij _ _ ?_
  intro i
  rw [hcoord i, hpd i, hD]

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_coord_self (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j : Fin n) : chartPartialDeriv hV c j (c.coord j) = 1 := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hcoord : EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) = c.coord j :=
    c.etaleCoordinates_coord j
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (c.coord j) = 1
  rw [← hcoord]
  exact EtaleCoordinates.partialDeriv_coord_self k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_coord_of_ne (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j i : Fin n) (h : j ≠ i) : chartPartialDeriv hV c j (c.coord i) = 0 := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hcoord : EtaleCoordinates.coord k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up i) = c.coord i :=
    c.etaleCoordinates_coord i
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (c.coord i) = 0
  rw [← hcoord]
  refine EtaleCoordinates.partialDeriv_coord_of_ne k (ULift.{u} (Fin n)) Γ(X, V)
    (ULift.up j) (ULift.up i) ?_
  intro hcon
  exact h (congrArg ULift.down hcon)

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_coord (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j i : Fin n) :
    chartPartialDeriv hV c j (c.coord i) = if i = j then (1 : Γ(X, V)) else 0 := by
  by_cases h : i = j
  · rw [if_pos h, ← h]
    exact chartPartialDeriv_coord_self hV c i
  · rw [if_neg h]
    exact chartPartialDeriv_coord_of_ne hV c j i (fun hc => h hc.symm)

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_add_algebraMap_mul (hV : IsAffineOpen V) (c : EtaleChart p V n)
    (j : Fin n) (a b : Γ(X, V)) (t : k) :
    chartPartialDeriv hV c j (a + sectionsAlgebraMap k p V t * b) =
      chartPartialDeriv hV c j a + sectionsAlgebraMap k p V t * chartPartialDeriv hV c j b := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have hk : algebraMap k Γ(X, V) = sectionsAlgebraMap k p V := algebraMap_sectionsAlgebra k p V
  have h3 : EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)
      (sectionsAlgebraMap k p V t) = 0 := by
    rw [← hk]
    simp
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j)
      (a + sectionsAlgebraMap k p V t * b)
    = EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) a
      + sectionsAlgebraMap k p V t *
        EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) b
  simp [Derivation.leibniz, h3]

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_mul (hV : IsAffineOpen V) (c : EtaleChart p V n) (j : Fin n)
    (a b : Γ(X, V)) :
    chartPartialDeriv hV c j (a * b) =
      a * chartPartialDeriv hV c j b + b * chartPartialDeriv hV c j a := by
  let instk : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instc : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  have instT : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
  have instFormallyEtale : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  show EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) (a * b)
    = a * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) b
      + b * EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) a
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

omit [AlgebraicGeometry.Smooth p] in
private theorem chartPartialDeriv_chainRule_of_same_rank (hV : IsAffineOpen V)
    (c c' : EtaleChart p V n) (j : Fin n) (f : Γ(X, V)) :
    chartPartialDeriv hV c' j f =
      ∑ i : Fin n, chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f :=
  chartPartialDeriv_chainRule hV c c' j f

theorem exists_etaleChart_coord_add_smul_chartPartialDeriv (hV : IsAffineOpen V)
    (c : EtaleChart p V n) (j₁ j₂ : Fin n) (hj : j₁ ≠ j₂) (t : k) :
    ∃ c' : EtaleChart p V n,
      c'.coord j₂ = c.coord j₂ + sectionsAlgebraMap k p V t * c.coord j₁ ∧
      (∀ j : Fin n, j ≠ j₂ → c'.coord j = c.coord j) ∧
      (∀ f : Γ(X, V),
        chartPartialDeriv hV c' j₁ f =
          chartPartialDeriv hV c j₁ f -
            sectionsAlgebraMap k p V t * chartPartialDeriv hV c j₂ f) ∧
      (∀ (j : Fin n) (f : Γ(X, V)), j ≠ j₁ →
        chartPartialDeriv hV c' j f = chartPartialDeriv hV c j f) := by
  classical
  obtain ⟨c', h1, h2⟩ := exists_etaleChart_coord_add_smul hV c j₁ j₂ hj t
  have hc1 : c'.coord j₁ = c.coord j₁ := h2 j₁ hj
  have hB : ∀ j : Fin n, chartPartialDeriv hV c' j (c.coord j₂) =
      chartPartialDeriv hV c' j (c'.coord j₂) -
        sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j₁) := by
    intro j
    have happ : chartPartialDeriv hV c' j (c'.coord j₂) =
        chartPartialDeriv hV c' j (c.coord j₂) +
          sectionsAlgebraMap k p V t * chartPartialDeriv hV c' j (c.coord j₁) := by
      rw [h1]
      exact chartPartialDeriv_add_algebraMap_mul hV c' j (c.coord j₂) (c.coord j₁) t
    exact eq_sub_of_add_eq happ.symm
  have hgen : ∀ j i : Fin n, chartPartialDeriv hV c' j (c.coord i) =
      (if i = j then (1 : Γ(X, V)) else 0) -
        (if i = j₂ then (if j = j₁ then sectionsAlgebraMap k p V t else 0) else 0) := by
    intro j i
    by_cases hi : i = j₂
    · rw [hi, hB j, ← hc1, chartPartialDeriv_coord hV c' j j₂, chartPartialDeriv_coord hV c' j j₁]
      by_cases hjj : j = j₁
      · simp [hjj]
      · simp [hjj, Ne.symm hjj]
    · rw [← h2 i hi, chartPartialDeriv_coord hV c' j i, if_neg hi, sub_zero]
  refine ⟨c', h1, h2, ?_, ?_⟩
  · intro f
    rw [chartPartialDeriv_chainRule_of_same_rank hV c c' j₁ f]
    have hterm : ∀ i : Fin n,
        chartPartialDeriv hV c' j₁ (c.coord i) * chartPartialDeriv hV c i f =
          (if i = j₁ then chartPartialDeriv hV c j₁ f else 0) +
            (if i = j₂ then
              -(sectionsAlgebraMap k p V t * chartPartialDeriv hV c j₂ f) else 0) := by
      intro i
      rw [hgen j₁ i]
      by_cases hi1 : i = j₁
      · simp [hi1, hj]
      · by_cases hi2 : i = j₂
        · simp [hi2, Ne.symm hj]
        · simp [hi1, hi2]
    simp only [hterm]
    simp [Finset.sum_add_distrib, sub_eq_add_neg]
  · intro j f hjne
    rw [chartPartialDeriv_chainRule_of_same_rank hV c c' j f]
    have hterm : ∀ i : Fin n,
        chartPartialDeriv hV c' j (c.coord i) * chartPartialDeriv hV c i f =
          (if i = j then chartPartialDeriv hV c j f else 0) := by
      intro i
      rw [hgen j i, if_neg hjne, ite_self, sub_zero]
      by_cases hi : i = j
      · simp [hi]
      · simp [hi]
    simp only [hterm]
    simp

omit [AlgebraicGeometry.Smooth p] in
private theorem etaleChart_restrict_coordRingHom (c : EtaleChart p V n) {W : X.Opens}
    (hWV : W ≤ V) :
    (c.restrict hWV).coordRingHom =
      ((X.presheaf.map (homOfLE hWV).op).hom).comp c.coordRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, EtaleChart.coordRingHom_C, EtaleChart.coordRingHom_C,
      FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply]
  · obtain ⟨i⟩ := i
    rw [RingHom.comp_apply, EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X]
    exact FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hWV i

omit [AlgebraicGeometry.Smooth p] in
private theorem map_chartPartialDeriv_restrict (hV : IsAffineOpen V) (c : EtaleChart p V n)
    {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (j : Fin n) (f : Γ(X, V)) :
    (X.presheaf.map (homOfLE hWV).op).hom (chartPartialDeriv hV c j f)
      = chartPartialDeriv hW (c.restrict hWV) j
          ((X.presheaf.map (homOfLE hWV).op).hom f) := by
  let instkV : Algebra k Γ(X, V) := sectionsAlgebra k p V
  let instkW : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instcV : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
  let instcW : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).algebra
  let instVW : Algebra Γ(X, V) Γ(X, W) :=
    (X.presheaf.map (homOfLE hWV).op).hom.toAlgebra
  have instScalarTowerMvPolynomial : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.isScalarTower
  have instTW : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).isScalarTower
  have instFEV : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
    c.algebra_formallyEtale hV
  have instFEW : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, W) :=
    (c.restrict hWV).algebra_formallyEtale hW
  have halg : ∀ z : Γ(X, V),
      algebraMap Γ(X, V) Γ(X, W) z = (X.presheaf.map (homOfLE hWV).op).hom z := fun _ => rfl
  have instTkVW : IsScalarTower k Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [halg]
      exact (FunctorialResolution.EmbeddedResolution.sectionsAlgebraMap_restrict_apply k p hWV a).symm
  have instTPVW : IsScalarTower (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      rw [halg]
      show (c.restrict hWV).coordRingHom z
        = (X.presheaf.map (homOfLE hWV).op).hom (c.coordRingHom z)
      rw [etaleChart_restrict_coordRingHom c hWV]
      rfl
  have key : algebraMap Γ(X, V) Γ(X, W)
      ((EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).repr
        (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j))
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, W)).repr
        (KaehlerDifferential.D k Γ(X, W) (algebraMap Γ(X, V) Γ(X, W) f)) (ULift.up j) := by
    rw [← KaehlerDifferential.map_D k k Γ(X, V) Γ(X, W)]
    exact (basisKaehler_repr_kaehlerMap k (ULift.{u} (Fin n)) Γ(X, V) Γ(X, W)
      (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j)).symm
  have hl : chartPartialDeriv hV c j f
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, V)).repr
        (KaehlerDifferential.D k Γ(X, V) f) (ULift.up j) := rfl
  have hr : chartPartialDeriv hW (c.restrict hWV) j
      ((X.presheaf.map (homOfLE hWV).op).hom f)
      = (EtaleCoordinates.basisKaehler k (ULift.{u} (Fin n)) Γ(X, W)).repr
        (KaehlerDifferential.D k Γ(X, W) ((X.presheaf.map (homOfLE hWV).op).hom f))
        (ULift.up j) := rfl
  rw [hl, hr, ← halg]
  exact key

private theorem map_mem_primeIdealOf_of_mem_of_le {V₁ W₁ : X.Opens} (hV₁ : IsAffineOpen V₁)
    (hW₁ : IsAffineOpen W₁) (hle : W₁ ≤ V₁) {y : X} (hyV : y ∈ V₁) (hyW : y ∈ W₁)
    (f : Γ(X, V₁)) (hf : f ∈ (hV₁.primeIdealOf ⟨y, hyV⟩).asIdeal) :
    (X.presheaf.map (homOfLE hle).op).hom f ∈ (hW₁.primeIdealOf ⟨y, hyW⟩).asIdeal := by
  by_contra hcon
  have h1 : y ∈ X.basicOpen ((X.presheaf.map (homOfLE hle).op).hom f) :=
    mem_basicOpen_of_notMem_primeIdealOf hW₁ hyW _ hcon
  have hgerm : (X.presheaf.germ W₁ y hyW).hom ((X.presheaf.map (homOfLE hle).op).hom f)
      = (X.presheaf.germ V₁ y hyV).hom f := by
    simp
  have h2 : y ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f y hyV, ← hgerm]
    exact (X.mem_basicOpen _ y hyW).mp h1
  exact notMem_basicOpen_of_mem_primeIdealOf hV₁ hyV f hf h2

omit [AlgebraicGeometry.Smooth p] in
theorem exists_unlabeled_index_partialDeriv_notMem_primeIdealOf
    (hV : IsAffineOpen V) (c : EtaleChart p V n) {x : X} (hx : x ∈ V)
    (N : List X.IdealSheafData) (γ : ℕ → Option (Fin n)) (H : X.IdealSheafData)
    (g : Γ(X, V)) (hγ : IsCoordLabeling c γ N) (_hinj : LabelingInjective γ N.length)
    (hsnc : InStrictNormalCrossingPositionAt p (H :: N) x) (hg : H.ideal ⟨V, hV⟩ = Ideal.span {g})
    (hxH : x ∈ H.support)
    (hxN : ∀ i : ℕ, ∀ hi : i < N.length, ∀ j : Fin n,
      γ i = some j → x ∈ (N[i]'hi).support) :
    letI : Algebra k Γ(X, V) := sectionsAlgebra k p V
    letI : Algebra (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.algebra
    haveI : IsScalarTower k (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) := c.isScalarTower
    haveI : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin n)) k) Γ(X, V) :=
      c.algebra_formallyEtale hV
    ∃ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) ∧
      EtaleCoordinates.partialDeriv k (ULift.{u} (Fin n)) Γ(X, V) (ULift.up j) g ∉
        (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  classical
  show ∃ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) ∧
      chartPartialDeriv hV c j g ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  by_contra hcon
  have hall : ∀ j : Fin n, (∀ i : ℕ, i < N.length → γ i ≠ some j) →
      chartPartialDeriv hV c j g ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro j hj
    by_contra hm
    exact hcon ⟨j, hj, hm⟩
  obtain ⟨U, hxU, m, c₂, alab, hainj, hanone, hasome⟩ := hsnc.exists_etaleChart
  have hlen0 : 0 < (H :: N).length := by
    rw [List.length_cons]
    omega
  have hHget : (H :: N)[0]'hlen0 = H := rfl
  obtain ⟨t, hat⟩ : ∃ t : Fin m, alab 0 = some t := by
    rcases hopt : alab 0 with _ | t
    · exfalso
      have htop : restrictIdeal ((H :: N)[0]'hlen0) U = ⊤ := hanone 0 hlen0 hopt
      rw [hHget] at htop
      exact (notMem_support_of_restrictIdeal_eq_top_of_mem H htop hxU) hxH
    · exact ⟨t, rfl⟩
  have hHU : restrictIdeal H U = c₂.coordIdeal {t} := by
    have h1 := hasome 0 hlen0 t hat
    rwa [hHget] at h1
  have hxUV : x ∈ (U ⊓ V : X.Opens) := ⟨hxU, hx⟩
  obtain ⟨fW, hfWle, hxfW⟩ := hV.exists_basicOpen_le (⟨x, hxUV⟩ : (U ⊓ V : X.Opens)) hx
  obtain ⟨W, hWaff, hWV, hWU, hxW⟩ :
      ∃ W : X.Opens, IsAffineOpen W ∧ W ≤ V ∧ W ≤ U ∧ x ∈ W :=
    ⟨X.basicOpen fW, hV.basicOpen fW, X.basicOpen_le fW,
      le_trans hfWle inf_le_left, hxfW⟩
  have hHW : restrictIdeal H W = (c₂.restrict hWU).coordIdeal {t} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hWU c₂ H {t} hHU
  have hHidW : H.ideal ⟨W, hWaff⟩ = Ideal.span {(c₂.restrict hWU).coord t} := by
    have h1 := (c₂.restrict hWU).ideal_eq_span_coord hWaff H {t} hHW
    rwa [Finset.coe_singleton, Set.image_singleton] at h1
  have hgW : H.ideal ⟨W, hWaff⟩
      = Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom g} := by
    have h1 := ideal_eq_span_image_map_of_le H hV hWaff hWV {g} hg
    rwa [Set.image_singleton] at h1
  obtain ⟨u, hu, hgu⟩ := exists_isUnit_mul_of_span_singleton_eq
    (coord_mem_nonZeroDivisors hWaff (c₂.restrict hWU) t) (hgW.symm.trans hHidW)
  have hyq : (c₂.restrict hWU).coord t ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    refine ideal_le_primeIdealOf H hWaff hxW hxH ?_
    rw [hHidW]
    exact Ideal.mem_span_singleton_self _
  have hlabel : ∀ j : Fin n, (∃ i : ℕ, i < N.length ∧ γ i = some j) →
      chartPartialDeriv hWaff (c₂.restrict hWU) t ((c.restrict hWV).coord j) ∈
        (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rintro j ⟨i, hi, hγi⟩
    have hNV : restrictIdeal (N[i]'hi) V = c.coordIdeal {j} := (hγ i hi).2 j hγi
    have hNW : restrictIdeal (N[i]'hi) W = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c (N[i]'hi) {j} hNV
    have hNidW : (N[i]'hi).ideal ⟨W, hWaff⟩
        = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := (c.restrict hWV).ideal_eq_span_coord hWaff (N[i]'hi) {j} hNW
      rwa [Finset.coe_singleton, Set.image_singleton] at h1
    have hilen : i + 1 < (H :: N).length := by
      rw [List.length_cons]
      omega
    have hNget : (H :: N)[i + 1]'hilen = N[i]'hi := rfl
    obtain ⟨s, has⟩ : ∃ s : Fin m, alab (i + 1) = some s := by
      rcases hopt : alab (i + 1) with _ | s
      · exfalso
        have htop := hanone (i + 1) hilen hopt
        rw [hNget] at htop
        exact (notMem_support_of_restrictIdeal_eq_top_of_mem (N[i]'hi) htop hxU) (hxN i hi j hγi)
      · exact ⟨s, rfl⟩
    have hst : s ≠ t := by
      intro heq
      have h0 : (0 : ℕ) = i + 1 :=
        hainj 0 hlen0 (i + 1) hilen t hat (by rw [has, heq])
      omega
    have hNU : restrictIdeal (N[i]'hi) U = c₂.coordIdeal {s} := by
      have h1 := hasome (i + 1) hilen s has
      rwa [hNget] at h1
    have hNW2 : restrictIdeal (N[i]'hi) W = (c₂.restrict hWU).coordIdeal {s} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c₂ (N[i]'hi) {s} hNU
    have hNidW2 : (N[i]'hi).ideal ⟨W, hWaff⟩
        = Ideal.span {(c₂.restrict hWU).coord s} := by
      have h1 := (c₂.restrict hWU).ideal_eq_span_coord hWaff (N[i]'hi) {s} hNW2
      rwa [Finset.coe_singleton, Set.image_singleton] at h1
    obtain ⟨v, _, hvj⟩ := exists_isUnit_mul_of_span_singleton_eq
      (coord_mem_nonZeroDivisors hWaff (c₂.restrict hWU) s) (hNidW.symm.trans hNidW2)
    have hsq : (c₂.restrict hWU).coord s ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      refine ideal_le_primeIdealOf (N[i]'hi) hWaff hxW (hxN i hi j hγi) ?_
      rw [hNidW2]
      exact Ideal.mem_span_singleton_self _
    rw [hvj, chartPartialDeriv_mul,
      chartPartialDeriv_coord_of_ne hWaff (c₂.restrict hWU) t s (Ne.symm hst),
      mul_zero, zero_add]
    exact Ideal.mul_mem_right _ _ hsq
  have hdecomp := chartPartialDeriv_chainRule hWaff (c.restrict hWV) (c₂.restrict hWU) t
    ((X.presheaf.map (homOfLE hWV).op).hom g)
  have hsum : chartPartialDeriv hWaff (c₂.restrict hWU) t
      ((X.presheaf.map (homOfLE hWV).op).hom g)
      ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rw [hdecomp]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hlab : ∃ l : ℕ, l < N.length ∧ γ l = some i
    · exact Ideal.mul_mem_right _ _ (hlabel i hlab)
    · refine Ideal.mul_mem_left _ _ ?_
      have hunlab : ∀ l : ℕ, l < N.length → γ l ≠ some i := by
        intro l hl hcon2
        exact hlab ⟨l, hl, hcon2⟩
      have h1 := hall i hunlab
      have h2 := map_mem_primeIdealOf_of_mem_of_le hV hWaff hWV hx hxW _ h1
      rw [map_chartPartialDeriv_restrict hV c hWaff hWV i g] at h2
      exact h2
  have hgt : chartPartialDeriv hWaff (c₂.restrict hWU) t
      ((X.presheaf.map (homOfLE hWV).op).hom g)
      = u * 1 + (c₂.restrict hWU).coord t *
        chartPartialDeriv hWaff (c₂.restrict hWU) t u := by
    rw [hgu, chartPartialDeriv_mul, chartPartialDeriv_coord_self]
  rw [hgt] at hsum
  have huq : u ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    have h2 : (c₂.restrict hWU).coord t *
        chartPartialDeriv hWaff (c₂.restrict hWU) t u
        ∈ (hWaff.primeIdealOf ⟨x, hxW⟩).asIdeal := Ideal.mul_mem_right _ _ hyq
    have h3 := Ideal.sub_mem _ hsum h2
    rwa [add_sub_cancel_right, mul_one] at h3
  exact (hWaff.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ huq hu)

end FunctorialResolution.EmbeddedResolution
