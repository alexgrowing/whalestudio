import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBdryChartOfHol
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryDiscMapEmbeddingFixedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscInAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinatesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBdry

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

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [show dualMap (g.comp f) = (dualMap g).comp (dualMap f) from RingHom.ext fun a => by
    ext <;> simp [dualMap]]
  exact Spec.map_comp (CommRingCat.ofHom (dualMap f)) (CommRingCat.ofHom (dualMap g))

theorem smul_mem_ball {n : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : (ρ : ℂ) • u ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  nlinarith [norm_nonneg u]

theorem smul_mem_punct {n a : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ Flat.punct n a 1) : (ρ : ℂ) • u ∈ Flat.punct n a 1 := by
  refine ⟨smul_mem_ball h0 h1 hu.1, fun i hi => ?_⟩
  have : (ρ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simpa [this] using hu.2 i hi

theorem recentre_mul {n : ℕ} (t₀ : Fin n → ℂ) (ρ₀ ρ₁ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) :
    HodgeMetric.recentre t₀ (ρ₀ * ρ₁) π u = HodgeMetric.recentre t₀ ρ₀ π ((ρ₁ : ℂ) • u) := by
  funext i
  simp [HodgeMetric.recentre, _root_.mul_assoc]

theorem exists_bdryChart_at : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) (I : Type) [Finite I] (s : I → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), (∀ (z : Sp ℂ ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → CoordsAt 𝔐.ξ y z₀ (χ.γ t₀) → InFrameDomain y cc f (χ.γ t₀) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (σ : KA l →+* ℂ) (C : Flat.BdryChart Xo σ n a₀) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : I → Fin C.g → C.R), 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, t₀ + (ρ : ℂ) • (u ∘ π) ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π)) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 n Bd χ t₀ cc f I _ s z₀ hBd ht₀ hz₀ hdom hval
  classical
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin I
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
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨z₀⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hp0 : p 0 = z₀ := by
    refine huniq _ _ (w 0) (hp 0 hb0) ?_
    have : w 0 = χ.γ t₀ := by
      simp only [hwdef]
      rw [HodgeMetric.recentre_zero]
    rw [this]
    exact hz₀
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  have hlat : ∀ k : Fin N, s (e.symm k) ∈ 𝔐.M.lat ⟨centre z₀, hall _⟩ := fun k => by
    obtain ⟨_, _, v', hext, _⟩ := hval (e.symm k)
    exact Submodule.subset_span ⟨v', hext⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨W, hW, v, hq, htan, hv⟩ := GlobalTheory.T.lattice_tangent_vectors_affine_open 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ⟨centre z₀, hall _⟩ N
    (fun k => s (e.symm k)) 𝔐.tie.gen hlat
  have hW0 : ⊤ ≤ p 0 ⁻¹ᵁ W := fun x _ => by
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    rw [hp0]
    exact hq
  obtain ⟨ρ₁, ψ, hρ₁, hρ₁', hψ, hψp⟩ := GlobalTheory.T.holomorphic_disc_in_affine_open 𝔐.X W hW n p hhol hW0
  have hp₁ : IsHolTo (Metric.ball 0 1) (fun u => spMap (ψ u)) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap Metric.isOpen_ball hψ.2
  obtain ⟨tW, ⟨mW⟩⟩ := exists_sab hW.fromSpec 𝔐.t
  obtain ⟨mY, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp 𝔐.m mW
  obtain ⟨ρ₂, C, h, hρ₂, hρ₂', ⟨mC⟩, hC⟩ := GlobalTheory.T.boundary_disc_map_embedding_fixed E H D l Xo c Y _ (hW.fromSpec ≫ 𝔐.f) tW mY τ n a₀
    (fun u => spMap (ψ u)) ha hp₁
    (fun u hu => by
      have := hτ _ (smul_mem_ball hρ₁ hρ₁' hu)
      rw [← hψp u hu] at this
      simpa using this)
    (fun u hu x hx => interior_range 𝔐 _ (hint _ (smul_mem_punct hρ₁ hρ₁' hu)) x (by
      rw [hx, ← hψp u hu.1, Category.assoc]))
  obtain ⟨θ, hθ⟩ : ∃ θ : Γ(𝔐.X, W) →+* C.R, spMap θ = h := ⟨(Spec.preimage h).hom, Spec.map_preimage _⟩
  subst hθ
  obtain ⟨mX, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mW mC
  obtain ⟨x, hx⟩ := GlobalTheory.T.abelian_map_tangent_coordinates E H 𝔐.X 𝔐.t Γ(𝔐.X, W) hW.fromSpec N v C.R C.t θ mX C.g C.M htan
  have hpt : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec =
      p (((ρ₁ * ρ₂ : ℝ) : ℂ) • z) := fun z hz => by
    rw [← Category.assoc, hC z hz, hψp _ (smul_mem_ball hρ₂ hρ₂' hz), smul_smul]
    push_cast
    rfl
  have h12 : 0 < ρ₁ * ρ₂ := mul_pos hρ₁ hρ₂
  have h12' : ρ₁ * ρ₂ ≤ 1 := mul_le_one₀ hρ₁' hρ₂.le hρ₂'
  have hle : ρ₀ * (ρ₁ * ρ₂) ≤ ρ₀ := by nlinarith
  have hpos : 0 < ρ₀ * (ρ₁ * ρ₂) := mul_pos hρ₀ h12
  refine ⟨a₀, π, ρ₀ * (ρ₁ * ρ₂), τ.comp (IntermediateField.inclusion c.le).toRingHom, C,
    spMap θ ≫ hW.fromSpec, mX, fun i => x (e i), hpos, fun u hu => ?_⟩
  obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
  refine ⟨g1, g2, ?_, g3, fun i => ?_⟩
  · rw [hpt u hu]
    have := hp _ (smul_mem_ball h12 h12' hu)
    simp only [hwdef] at this
    rw [← recentre_mul] at this
    exact this
  · have e' : spMap ((C.ψ u).comp θ) ≫ hW.fromSpec = spMap (C.ψ u) ≫ spMap θ ≫ hW.fromSpec := by
      rw [← Category.assoc]; congr 1; exact Spec.map_comp _ _
    obtain ⟨w', hw1, hw2⟩ := hv ((C.ψ u).comp θ) _ e' (𝔐.all _) (e i)
    simp only [Equiv.symm_apply_apply] at hw1
    refine ⟨w', hw1, ?_⟩
    rw [hw2, dualMap_comp, hx, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.SncBdry
