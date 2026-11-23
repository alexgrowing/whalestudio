import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifTangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem eq_of_values {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp ℂ ⟶ X} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : ∀ f, valAt' x U f = valAt' x' U f) : x = x' := by
  refine (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h).symm.trans
    (Eq.trans ?_ (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h'))
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := e f
  rw [valAt', valAt', dif_pos h, dif_pos h'] at this
  exact this

theorem fderiv_eq_zero_of_origin {w : Fin g → ℂ}
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z w = 0 := by
  let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
  have hτ : ∀ v, u.ex v ≫ τ = u.ex (z + v) := fun v => by
    rw [u.ex_add, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (τ.left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, hτ, add_zero]
    exact h
  have e : (fun v => valAt' (u.ex v).left (τ.left ⁻¹ᵁ U) ((τ.left.app U).hom f)) =
      fun v => valAt' (u.ex (z + v)).left U f := funext fun v => by
    rw [valAt'_comp, ← Over.comp_left, hτ]
  have := hw _ ((τ.left.app U).hom f) h0
  rw [e, fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at this
  exact this

theorem eq_zero_of_fderiv_eq_zero (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  haveI := u.discrete
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set u.Λ))
  have hO0 : (0 : Fin g → ℂ) ∈ O := by
    have : (0 : u.Λ) ∈ Subtype.val ⁻¹' O := hOe ▸ rfl
    exact this
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 ((((u.hol U 0).1).inter hO).preimage hc) 0
    (by simpa only [Set.mem_preimage, zero_smul] using ⟨h0, hO0⟩)
  have ht : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hd : ∀ f, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U f) 0 t := by
    intro f t ht
    have h1 := ((u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hB ht).1)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)
    rw [one_smul, fderiv_eq_zero_of_origin u hw _ U f (hB ht).1] at h2
    exact h2
  have he : u.ex (((ε / 2 : ℝ) : ℂ) • w) = u.ex ((0 : ℂ) • w) := by
    refine Over.OverMorphism.ext (eq_of_values hU (hB ht).1 (hB (Metric.mem_ball_self hε)).1 fun f => ?_)
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ε).isPreconnected
      (fun t ht => (hd f t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd f t ht).deriv) ht
      (Metric.mem_ball_self hε)
  rw [zero_smul, (u.ker 0).2 (zero_mem _), u.ker] at he
  have h3 : (⟨_, he⟩ : u.Λ) ∈ ({0} : Set u.Λ) := hOe ▸ (hB ht).2
  exact (smul_eq_zero.1 (congrArg Subtype.val h3)).resolve_left (Complex.ofReal_ne_zero.2 (by positivity))

theorem tangent_bijection (hs : SmoothOfRelativeDimension g A.hom) :
    (∀ v : epsR ℂ ⟶ A, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v : epsR ℂ ⟶ A, IsTangent v ∧ u.IsDiff w v :=
  TangentOrigin.tangent_bijection_of_values valAt'_rules A L g u
    (exists_coord_adapted (HolChart.exists_holomorphic_chart valAt'_rules existsUnique_point_of_ringHom
      exists_holomorphic_section_of_etale) A L g u hs (eq_zero_of_fderiv_eq_zero u))

theorem riemannData_tangent : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y),
    (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧
      (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v) := fun _ P _ d =>
  tangent_bijection d.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d.isPull.1 P.smoothDim)

end GlobalTheory.UnifTangent
