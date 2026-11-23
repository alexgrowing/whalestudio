import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HolUnifSec

open GlobalTheory.CxPts Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ} (u : HolUnif A M g)

def pt (z : Fin g → ℂ) : CxPts A.hom (RingHom.id ℂ) :=
  ⟨(u.ex z).left, (Over.w (u.ex z)).trans (Spec.map_id _).symm⟩

theorem pt_surjective : Function.Surjective (pt u) := fun y => by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y.1 (y.2.trans (Spec.map_id _)))
  exact ⟨z, Subtype.ext (congrArg (·.left) hz)⟩

theorem sub_mem_of_pt_eq {z w : Fin g → ℂ} (h : pt u z = pt u w) : z - w ∈ u.Λ := by
  have h' : u.ex z = u.ex w := Over.OverMorphism.ext (congrArg Subtype.val h)
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h'] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem isOpen_pre (U : A.left.Opens) : IsOpen (pt u ⁻¹' ptsIn _ _ U) := (u.hol U 0).1

theorem differentiableOn_ev (U : A.left.Opens) (f : Γ(A.left, U)) :
    DifferentiableOn ℂ (ev _ _ U f ∘ pt u) (pt u ⁻¹' ptsIn _ _ U) := (u.hol U f).2

theorem continuous_pt : Continuous (pt u) :=
  CxPts.continuous_iff.2 fun U => ⟨isOpen_pre u U, fun f => (differentiableOn_ev u U f).continuousOn⟩

theorem eq_zero_of_fderiv_eq_zero (z₀ w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0) : w = 0 := by
  refine TorusTransfer.eq_zero_of_fderiv_eq_zero u w fun U f h => ?_
  let T : A ⟶ A := (toUnit A ≫ u.ex (-z₀)) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (-z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, neg_add_cancel]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), neg_add_cancel] at h1
  exact h1

variable {D : ℕ} (c : AlgChart A.hom (RingHom.id ℂ) D)

theorem isOpen_pre_source : IsOpen (pt u ⁻¹' c.e.source) := c.e.open_source.preimage (continuous_pt u)

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (c.e ∘ pt u) (pt u ⁻¹' c.e.source) :=
  SCV.analyticOnNhd_of_differentiableOn (isOpen_pre_source u c) (differentiableOn_euclidean.2 fun a =>
    ((differentiableOn_ev u _ (c.x a)).mono fun _ hz => c.source_subset hz).congr fun _ hz => c.apply_eq _ hz a)

theorem injective_fderiv {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) :
    Function.Injective (fderiv ℂ (c.e ∘ pt u) z₀) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => eq_zero_of_fderiv_eq_zero u z₀ w fun U f hU => ?_
  have e : ev _ _ U f ∘ pt u =ᶠ[𝓝 z₀] (ev _ _ U f ∘ c.e.symm) ∘ (c.e ∘ pt u) :=
    eventually_of_mem ((isOpen_pre_source u c).mem_nhds hz) fun z hz =>
      (congrArg (ev _ _ U f) (c.e.left_inv hz)).symm
  change fderiv ℂ (ev _ _ U f ∘ pt u) z₀ w = 0
  rw [e.fderiv_eq, fderiv_comp (f := c.e ∘ pt u) z₀ (c.differentiableAt_ev f hz hU)
    (analyticOnNhd_chart u c z₀ hz).differentiableAt, ContinuousLinearMap.comp_apply, hw, map_zero]

theorem dim_le {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) : D ≤ g := by
  have h1 : dimH ((c.e ∘ pt u) '' (pt u ⁻¹' c.e.source)) ≤ dimH (pt u ⁻¹' c.e.source) :=
    dimH_image_le_of_locally_lipschitzOn fun z hz => by
      obtain ⟨K, t, ht, h⟩ := (analyticOnNhd_chart u c z hz).contDiffAt.exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  rw [Set.image_comp, Set.image_preimage_eq _ (pt_surjective u), c.e.image_source_eq_target,
    Real.dimH_of_mem_nhds (c.e.open_target.mem_nhds (c.e.map_source hz)),
    Real.dimH_of_mem_nhds ((isOpen_pre_source u c).mem_nhds hz), Nat.cast_le,
    finrank_real_of_complex, finrank_real_of_complex] at h1
  simpa using h1

theorem holoOn_of_comp (R : AnRead A.hom (RingHom.id ℂ) D) {S : Set (CxPts A.hom (RingHom.id ℂ))} (hS : IsOpen S)
    {F : CxPts A.hom (RingHom.id ℂ) → ℂ} (hF : DifferentiableOn ℂ (F ∘ pt u) (pt u ⁻¹' S)) : R.HoloOn S F := by
  intro i v hv
  set c := R.chart i
  obtain ⟨z₀, hz₀⟩ := pt_surjective u (c.e.symm v)
  have hz : pt u z₀ ∈ c.e.source := hz₀ ▸ c.e.map_target hv.1
  have hv₀ : (c.e ∘ pt u) z₀ = v := by rw [Function.comp_apply, hz₀, c.e.right_inv hv.1]
  have hinj := injective_fderiv u c hz
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)) hinj
  have hrk : Module.finrank ℂ (Fin g → ℂ) = Module.finrank ℂ (V D) :=
    le_antisymm hle (by simpa using dim_le u c hz)
  let L : (Fin g → ℂ) ≃L[ℂ] V D := (LinearEquiv.ofBijective
    (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj⟩).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt (c.e ∘ pt u) (L : (Fin g → ℂ) →L[ℂ] V D) z₀ :=
    (analyticOnNhd_chart u c z₀ hz).hasStrictFDerivAt
  have hd := hs.to_localInverse.hasFDerivAt.differentiableAt
  have hr := hs.eventually_right_inverse
  have hl := hs.localInverse_apply_image
  have ht := hs.localInverse_tendsto
  rw [hv₀] at hd hr hl ht
  have hFz : DifferentiableAt ℂ (F ∘ pt u) (hs.localInverse _ _ _ v) := by
    rw [hl]
    exact hF.differentiableAt ((hS.preimage (continuous_pt u)).mem_nhds (show pt u z₀ ∈ S from hz₀ ▸ hv.2))
  refine ((hFz.comp v hd).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hr, ht ((isOpen_pre_source u c).mem_nhds hz)] with w hw hw'
  exact congrArg F ((congrArg c.e.symm hw.symm).trans (c.e.left_inv hw'))

theorem exists_isFn (hA : IsAbelianScheme A) (hp : IsProjOver A.hom) (hM : M.IsLB) {θ : (Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (hper : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) :
    ∃ s : M.Sec, u.IsFn s θ := by
  classical
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then θ (r y) * u.fr i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = θ z * u.fr i z := fun i z hz => by
    have := hper _ (sub_mem_of_pt_eq u (hr (pt u z))) i z hz
    rw [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : u.fr i z = gv _ _ M i j (pt u z) * u.fr j z := u.fr_compat i j z hij
      rw [hs i z hi, hs j z hj, e, mul_left_comm]
    · exact (hθ.differentiableOn.mul (u.fr_hol i)).congr fun z hz => hs i z hz
  obtain ⟨σ, hσ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  exact ⟨σ, fun i z hz => (congrFun₂ (congrArg Subtype.val hσ) i (pt u z)).trans (hs i z hz)⟩

theorem isUnit_of_ev_ne_zero {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] {U : Y.Opens} (f : Γ(Y, U))
    (h : ∀ y ∈ ptsIn p (RingHom.id ℂ) U, ev p _ U f y ≠ 0) : IsUnit f := by
  have := LocallyOfFiniteType.jacobsonSpace p
  have hU : U ≤ Y.basicOpen f := by
    by_contra hn
    obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
    obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (Y.basicOpen f : Set Y)ᶜ) ⟨x, hx, hx'⟩
      (U.isOpen.isLocallyClosed.inter (Y.basicOpen f).isOpen.isClosed_compl.isLocallyClosed)
    let q : CxPts p (RingHom.id ℂ) :=
      ⟨pointOfClosedPoint p y hy', (pointOfClosedPoint_comp p y hy').trans (Spec.map_id _).symm⟩
    have hq : q.1 (IsLocalRing.closedPoint ℂ) = y := pointOfClosedPoint_apply p y hy' _
    have hqU : q ∈ ptsIn p _ U := mem_ptsIn.2 (hq ▸ hy.1)
    exact hy.2 (hq ▸ mem_ptsIn.1 ((mem_ptsIn_basicOpen hqU f).2 (h q hqU)))
  exact Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (Y.mem_basicOpen f x hx).1 (hU hx)

theorem hasGen_of_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  intro A _ hA hp M hM g u θ hθ h0 hper
  obtain ⟨s, hs⟩ := exists_isFn u hA hp hM hθ hper
  have := hA.proper
  have hu : ∀ i, IsUnit (s.f i) := fun i => isUnit_of_ev_ne_zero A.hom _ fun y hy => by
    obtain ⟨z, rfl⟩ := pt_surjective u y
    exact (hs i z hy).trans_ne (mul_ne_zero (h0 z) (u.fr_ne i z hy))
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

end GlobalTheory.HolUnifSec
