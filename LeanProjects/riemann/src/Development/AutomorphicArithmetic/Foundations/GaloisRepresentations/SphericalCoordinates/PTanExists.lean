import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem exists_basis {B : Type} [CommRing B] [Algebra ℂ B] (d : ℕ) (a : Fin d → B)
    (he : (MvPolynomial.aeval a : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B).toRingHom.Etale) :
    ∃ b : Module.Basis (Fin d) B Ω[B⁄ℂ], ∀ l, b l = KaehlerDifferential.D ℂ B (a l) := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := (MvPolynomial.aeval a).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap ℂ B r = MvPolynomial.aeval a (MvPolynomial.C r)
    rw [MvPolynomial.aeval_C])
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := he
  let b0 := Algebra.TensorProduct.basis B (KaehlerDifferential.mvPolynomialBasis ℂ (Fin d))
  refine ⟨b0.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (MvPolynomial (Fin d) ℂ) B),
    fun l => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    ← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply,
    show algebraMap (MvPolynomial (Fin d) ℂ) B (MvPolynomial.X l) = a l from MvPolynomial.aeval_X a l]

private theorem exists_phi {B : Type} [CommRing B] [Algebra ℂ B] (e : B →ₐ[ℂ] ℂ) (d : ℕ)
    (bs : Module.Basis (Fin d) B Ω[B⁄ℂ]) :
    ∃ φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (r : B) (ω : Ω[B⁄ℂ]), φ (r • ω) = e r • φ ω) ∧ (∀ l, φ (bs l) = Pi.single l 1) ∧
      ∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]),
        (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
  let φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun ω l => e (bs.repr ω l)
      map_add' := by
        intro x y
        funext l
        simp
      map_smul' := by
        intro c x
        funext l
        rw [← algebraMap_smul B c x, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
          AlgHom.commutes]
        simp }
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro r ω
    funext l
    simp [φ]
  · intro l
    funext l'
    by_cases h : l' = l
    · subst h
      simp [φ]
    · simp [φ, Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]
  · intro ω hω
    refine ⟨d, fun l => bs.repr ω l, bs, ?_, (bs.sum_repr ω).symm⟩
    intro i
    simpa [φ] using congrFun hω i

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanExists_of :
    UpperTheory.Gal.W2.TanExists := by
  intro Z Y sZ s' d hsmooth c₁ c₂ h₁ h₂ hc₁ y hy
  haveI := hsmooth
  obtain ⟨U, x, hUaff, hzU, het⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := sZ) (D := d)
    ((↑y ≫ c₁ : Sp ℂ ⟶ Z) (IsLocalRing.closedPoint ℂ))
  have hyU : ⊤ ≤ (↑y : Sp ℂ ⟶ Y) ⁻¹ᵁ (c₁ ⁻¹ᵁ U ⊓ c₂ ⁻¹ᵁ U) := by
    rw [GlobalTheory.Points.le_preimage_iff]
    have h2 := hzU
    rw [hy] at h2
    exact ⟨hzU, h2⟩
  obtain ⟨V, hVaff, hyV, hVle⟩ := GlobalTheory.Points.exists_isAffineOpen_le (↑y : Sp ℂ ⟶ Y) hyU
  have hV1 : V ≤ c₁ ⁻¹ᵁ U := hVle.trans inf_le_left
  have hV2 : V ≤ c₂ ⁻¹ᵁ U := hVle.trans inf_le_right
  have hg := HasRingHomProperty.appLE @Etale c₁ hc₁ ⟨U, hUaff⟩ ⟨V, hVaff⟩ hV1
  have hres : ∀ t, (c₁.appLE U V hV1).hom t = Sec.res s' hV1 (appSec sZ s' c₁ U t) := by
    intro t
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  have heq : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom =
      (c₁.appLE U V hV1).hom.comp (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := semiHom_appSec h₁ U r 1
      simp only [Algebra.smul_def, _root_.mul_one, map_one, RingHom.id_apply] at h1
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.C r) =
          DVR.FlatBC.algX sZ U r := MvPolynomial.eval₂Hom_C _ _ _
      refine Eq.trans ?_ ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres _)).symm
      change algebraMap ℂ (Sec s' V) r = Sec.res s' hV1 (appSec sZ s' c₁ U (algebraMap ℂ (Sec sZ U) r))
      rw [h1, AlgHom.commutes]
    · intro i
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      have h4 : (MvPolynomial.eval₂Hom (DVR.FlatBC.algX sZ U) x) (MvPolynomial.X i) = x i :=
        MvPolynomial.eval₂Hom_X' _ _ _
      exact ((congrArg (c₁.appLE U V hV1).hom h4).trans (hres (x i))).symm
  have het' : (MvPolynomial.aeval (fun l => Sec.res s' hV1 (appSec sZ s' c₁ U (x l))) :
      MvPolynomial (Fin d) ℂ →ₐ[ℂ] Sec s' V).toRingHom.Etale := by
    rw [heq]
    exact RingHom.Etale.stableUnderComposition _ _ het hg
  obtain ⟨bs, hbs⟩ := UpperTheory.Gal.W2.exists_basis d _ het'
  have hyV' : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := hyV
  let e : Sec s' V →ₐ[ℂ] ℂ :=
    { toRingHom := CxPts.evHom hyV'
      commutes' := fun r => (CxPts.ev_eq hyV' _).symm.trans (CxPts.ev_algX hyV' r) }
  obtain ⟨φ, hsm, hbasis, hker⟩ := UpperTheory.Gal.W2.exists_phi e d bs
  refine ⟨fun j l => φ (KaehlerDifferential.D ℂ (Sec s' V) (Sec.res s' hV2 (appSec sZ s' c₂ U (x j)))) l,
    U, V, hV1, hV2, x, hyV', hUaff, hVaff, φ, ?_, ?_, ?_, ?_⟩
  · intro b ω
    rw [hsm]
    congr 1
    exact (CxPts.ev_eq hyV' b).symm
  · intro l
    have h3 := hbasis l
    rw [hbs l] at h3
    exact h3
  · intro j
    rfl
  · intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hker ω hω
    exact ⟨m, b, ω', fun i => (CxPts.ev_eq hyV' (b i)).trans (hb i), hsum⟩
