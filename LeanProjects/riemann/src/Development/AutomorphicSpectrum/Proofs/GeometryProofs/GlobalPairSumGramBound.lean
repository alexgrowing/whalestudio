import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBdryChartOfHol
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsRiemannFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryDiscMapEmbeddingFixedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscInAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecializationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecializationFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexLinearComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriodsStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroSecond

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FramePeriods

theorem interior_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    (z : Sp ℂ ⟶ 𝔐.X) (hz : 𝔐.Interior z) (x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
    (hx : x ≫ pullback.fst _ _ = z ≫ 𝔐.f) : Set.range x ⊆ Set.range Y.jQ := by
  rintro _ ⟨q, rfl⟩
  have hab : 𝔐.f (centre z) ∈ abLocus Y.t.G :=
    (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  have hq : z q = centre z := congrArg z (Subsingleton.elim (α := PrimeSpectrum ℂ) q _)
  have e : (x ≫ pullback.fst _ _) q = (z ≫ 𝔐.f) q := by rw [hx]
  simp only [Scheme.Hom.comp_apply] at e
  have : x q ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Set.mem_preimage, e, hq]
    exact hab
  rwa [Y.ab_gen] at this

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [show dualMap (g.comp f) = (dualMap g).comp (dualMap f) from RingHom.ext fun a => by
    ext <;> simp [dualMap]]
  exact Spec.map_comp (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (dualMap g))

theorem smul_mem_ball' {n : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : (ρ : ℂ) • u ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  nlinarith [norm_nonneg u]

theorem smul_mem_punct' {n a : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ Flat.punct n a 1) : (ρ : ℂ) • u ∈ Flat.punct n a 1 := by
  refine ⟨smul_mem_ball' h0 h1 hu.1, fun i hi => ?_⟩
  have : (ρ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simpa [this] using hu.2 i hi

theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n a₀ : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (τ : c.F →+* ℂ) (hpq : 1 ≤ D.p + D.q)
    (hτ : (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0) (ha : a₀ ≤ n)
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hc : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)))
    (hi : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u)) (h0 : genPt 𝔐.ξ ⤳ centre (p 0))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), h0⟩) :
    ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
      ∀ u ∈ Flat.punct n a₀ 1, 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u))
        (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u) := by
  classical
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨W, hW, v, hq, htan, hval⟩ := GlobalTheory.T.lattice_tangent_vectors_affine_open 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ⟨centre (p 0), h0⟩ N
    (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) 𝔐.tie.gen
    (GlobalTheory.T.hodge_generated_sum_specialization E H D l Xo c Y S Ω K J y 𝔐 a b N bb (p 0) h0 hfr)
  have hW0 : ⊤ ≤ p 0 ⁻¹ᵁ W := fun x _ => by
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hq
  obtain ⟨ρ₁, ψ, hρ₁, hρ₁', hψ, hψp⟩ := GlobalTheory.T.holomorphic_disc_in_affine_open 𝔐.X W hW n p hp hW0
  have hp₁ : IsHolTo (Metric.ball 0 1) (fun u => spMap (ψ u)) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap Metric.isOpen_ball hψ.2
  obtain ⟨tW, ⟨mW⟩⟩ := exists_sab hW.fromSpec 𝔐.t
  obtain ⟨mY, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp 𝔐.m mW
  obtain ⟨ρ₂, C, h, hρ₂, hρ₂', ⟨mC⟩, hC⟩ := GlobalTheory.T.boundary_disc_map_embedding_fixed E H D l Xo c Y _ (hW.fromSpec ≫ 𝔐.f) tW mY τ n a₀
    (fun u => spMap (ψ u)) ha hp₁
    (fun u hu => by
      have := hc _ (smul_mem_ball' hρ₁ hρ₁' hu)
      rw [← hψp u hu] at this
      simpa using this)
    (fun u hu x hx => interior_range 𝔐 _ (hi _ (smul_mem_punct' hρ₁ hρ₁' hu)) x (by
      rw [hx, ← hψp u hu.1, Category.assoc]))
  obtain ⟨ρ₃, Λ, _, L, hρ₃, hρ₃', hR⟩ := GlobalTheory.T.log_periods_riemann_form E H D l Xo _ n a₀ C hpq hτ
  obtain ⟨θ, hθ⟩ : ∃ θ : Γ(𝔐.X, W) →+* C.R, spMap θ = h := ⟨(Spec.preimage h).hom, Spec.map_preimage _⟩
  subst hθ
  obtain ⟨mX, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mW mC
  obtain ⟨x, hx⟩ := GlobalTheory.T.abelian_map_tangent_coordinates E H 𝔐.X 𝔐.t Γ(𝔐.X, W) hW.fromSpec N v C.R C.t θ mX C.g C.M htan

  have hw : ∀ z : Fin n → ℂ, ∃ w : Fin N → (epsAt (spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec) ⟶ 𝔐.t.G),
      (∀ k, 𝔐.M.ValAt _ ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (w k)) ∧
      ∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ mX.φ := fun z => by
    have e : spMap ((C.ψ z).comp θ) ≫ hW.fromSpec = spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec := by
      rw [← Category.assoc]; congr 1; exact Spec.map_comp _ _
    choose w hw1 hw2 using hval ((C.ψ z).comp θ) _ e (𝔐.all _)
    refine ⟨w, hw1, fun k => ?_⟩
    rw [hw2, dualMap_comp', hx, Category.assoc]
  have hpt : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec =
      p (((ρ₁ * ρ₂ : ℝ) : ℂ) • z) := fun z hz => by
    rw [← Category.assoc, hC z hz, hψp _ (smul_mem_ball' hρ₂ hρ₂' hz), smul_smul]
    push_cast
    rfl
  refine ⟨C.g, Λ, inferInstance, L, ρ₁ * ρ₂ * ρ₃, fun k u e => C.ψ ((ρ₃ : ℂ) • u) (x k e),
    by positivity, by nlinarith [mul_pos hρ₁ hρ₂, mul_le_one₀ hρ₁' hρ₂.le hρ₂'], fun k => ?_, ?_, fun u hu => ?_⟩
  · refine differentiableOn_pi.2 fun e => ?_
    exact (C.hol.2 (x k e)).comp (by fun_prop) fun u hu => smul_mem_ball' hρ₃ hρ₃' hu
  · obtain ⟨w, hw1, hw2⟩ := hw 0
    obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ (spMap (C.ψ 0) ≫ spMap θ ≫ hW.fromSpec)
    obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.lie_model_complex_linear_comparison E H 𝔐.X 𝔐.t C.R C.t _ mX C.g C.M (C.ψ 0) Vz MR
    have hz0 : spMap (C.ψ 0) ≫ spMap θ ≫ hW.fromSpec = p 0 := by
      simpa using hpt 0 (by simp)
    have hfr' : ∀ (z : Sp ℂ ⟶ 𝔐.X) (hz : z = p 0) (h' : genPt 𝔐.ξ ⤳ centre z),
        (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h'⟩ := by
      rintro z rfl h'
      exact hfr
    have hin := GlobalTheory.T.hodge_generated_sum_specialization_frame E H D l Xo c Y S Ω K J y 𝔐 a b N bb _ (𝔐.all _) Vz MR (fun k => Θ fun e => C.ψ 0 (x k e))
      (hfr' _ hz0 _) (fun k => by
        have e : MR.pt (Θ fun e => C.ψ 0 (x k e)) = w k :=
          Over.OverMorphism.ext ((hΘ (x k)).trans (hw2 k).symm)
        rw [e]
        exact hw1 k)
    have := LinearIndependent.of_comp Θ hin
    simpa using this
  · have hz : (ρ₃ : ℂ) • u ∈ Metric.ball (0 : Fin n → ℂ) 1 := smul_mem_ball' hρ₃ hρ₃' hu.1
    obtain ⟨w, hw1, hw2⟩ := hw ((ρ₃ : ℂ) • u)
    have hg := GlobalTheory.T.chart_lattice_tangent_coordinates E H D l Xo _ n a₀ C 𝔐.X 𝔐.t _ mX Ω 𝔐.ξ 𝔐.Li 𝔐.M N _ x _ (L.H u) w (hR u hu) hw1 hw2
    have e := hpt _ hz
    rw [smul_smul] at e
    rw [show ((ρ₁ * ρ₂ * ρ₃ : ℝ) : ℂ) = ((ρ₁ * ρ₂ : ℝ) : ℂ) * (ρ₃ : ℂ) by push_cast; ring, ← e]
    exact hg

theorem recentre_mul {n : ℕ} (t₀ : Fin n → ℂ) (ρ₀ ρ₁ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) :
    HodgeMetric.recentre t₀ (ρ₀ * ρ₁) π u = HodgeMetric.recentre t₀ ρ₀ π ((ρ₁ : ℂ) • u) := by
  funext i
  simp [HodgeMetric.recentre, _root_.mul_assoc]

theorem star_mem_ball' {n : ℕ} {u : Fin n → ℂ} (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star u ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  rwa [norm_star]

theorem star_mem_punct' {n a : ℕ} {u : Fin n → ℂ} (hu : u ∈ Flat.punct n a 1) :
    star u ∈ Flat.punct n a 1 :=
  ⟨star_mem_ball' hu.1, fun i hi => by simpa using hu.2 i hi⟩

theorem diffOn_star' {n : ℕ} {V : Type} [Fintype V] {f : (Fin n → ℂ) → V → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    DifferentiableOn ℂ (fun u => star (f (star u))) (Metric.ball 0 1) := fun u hu => by
  have := (hf.differentiableAt (Metric.isOpen_ball.mem_nhds (star_mem_ball' hu))).star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (starRingEnd ℂ) H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ConjugateRootZeroSecond.rt0_conj_neg_ne_zero H

theorem zeroPeriods (n a : ℕ) (ha : a ≤ n) : ∃ (Λ : Type) (_ : AddCommGroup Λ), Nonempty (Flat.LogPeriods n a 0 Λ) :=
  ⟨PUnit, inferInstance, ⟨{
    a_le := ha
    free := inferInstance
    fin := inferInstance
    rank := by rw [mul_zero]; exact Module.finrank_zero_of_subsingleton
    E := 0
    alt := fun _ => rfl
    unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, LinearMap.ext fun x => by
      rw [show x = 0 from Subsingleton.elim _ _, map_zero, map_zero]⟩⟩
    P := fun _ => 0
    hol := fun _ => differentiableOn_const _
    H := fun _ => 0
    herm := fun _ _ => by ext i; exact i.elim0
    pos := fun _ _ z hz => absurd (Subsingleton.elim z 0) hz
    im := fun _ _ _ _ => by simp
    T := fun _ => 0
    mono := fun _ _ _ _ => rfl
    W := ⊤
    coiso := fun _ _ => ⟨1, one_ne_zero, trivial⟩
    s := fun _ _ => 0
    s_hol := fun _ => differentiableOn_const _
    s_eq := fun _ _ _ => rfl
    span := Subsingleton.elim _ _ }⟩⟩

theorem exists_isFramePeriods : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Top.IsGlobal Xo l c Y → ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro _ E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 _ a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := GlobalTheory.T.snc_chart_local_normal_form K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_conjugate_log_periods n a₀ g N Λ L' U' (GlobalTheory.T.bijective_logPeriods_T n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.FramePeriods
