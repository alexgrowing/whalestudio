import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open GlobalTheory.CxPts

namespace GlobalTheory.DetLine.SameIndex

theorem exists_lift {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : Sp ℂ ⟶ Y)
    (hx : x (IsLocalRing.closedPoint ℂ) ∈ Set.range j) : ∃ y : Sp ℂ ⟶ X, y ≫ j = x := by
  refine ⟨IsOpenImmersion.lift j x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hx

theorem isHolTo_chart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

theorem index_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.XF c) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → y ≫ toX Xo c = Fu.u i P → y' ≫ toX Xo c = Fu.u i' P' → i = i' := by
  intro E _ _ _ H D l Xo c O _ β Y U e g ty Fu i i' P P' y y' B io _ hio hr hs hy hy' hU hU' hP hP' hu hu'
  classical
  haveI := Y.jQ_open
  let W : B.X.Opens := io ⁻¹ᵁ Y.jQ.opensRange
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨y⟩
  have hl : ∀ z : CxPts B.str e, z ∈ ptsIn B.str e W → ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Y.jQ = z.1 ≫ io :=
    fun z hz => exists_lift Y.jQ _ (mem_ptsIn.1 hz)
  choose! w hw using hl
  have hwσ : ∀ z ∈ ptsIn B.str e W,
      (w z ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hw z hz,
      ← OpenReg.spMap_comp, Category.assoc _ io]
    exact congrArg (· ≫ _) ((congrArg (z.1 ≫ ·) hs).trans z.2)
  have hex : ∀ z : CxPts B.str e, ∃ k : Fin Fu.n, z ∈ ptsIn B.str e W →
      ∃ Q, IsPeriod (Fu.Di k) ty Q ∧ Fu.u k Q = w z ≫ toX Xo c := fun z => by
    by_cases hz : z ∈ ptsIn B.str e W
    · obtain ⟨k, Q, h⟩ := Fu.onto _ (hwσ z hz)
      exact ⟨k, fun _ => ⟨Q, h⟩⟩
    · exact ⟨i, fun h => absurd h hz⟩
  choose k hk using hex
  have hcont : ContinuousOn k (ptsIn B.str e W) := by
    intro z₀ hz₀
    obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := B.str) (σ := e) (D := B.dim) z₀
    let T := ch.e.target ∩ ch.e.symm ⁻¹' ptsIn B.str e W
    have hT : IsOpen T := ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)
    have h1 : IsHolTo T fun b => w (ch.e.symm b) :=
      HorLift.isHolTo_of_comp_open Y.jQ (LocLift.isHolTo_congr
        (LocLift.isHolTo_comp_hom (isHolTo_chart_symm ch hT Set.inter_subset_left) io) fun b hb => hw _ hb.2)
    let φ : ReciprocityTheory.L2DbarEstimates.V B.dim ≃L[ℂ] (Fin B.dim → ℂ) := EuclideanSpace.equiv (Fin B.dim) ℂ
    have hTφ : IsOpen (φ.symm ⁻¹' T) := hT.preimage φ.symm.continuous
    obtain ⟨B₁, k₀, Q, hB₁, hb₁, hsub, hQ, hQu⟩ := Fu.lift _ (φ.symm ⁻¹' T)
      (fun t => w (ch.e.symm (φ.symm t)) ≫ toX Xo c) hTφ (fun t ht => hwσ _ ht.2)
      (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom h1 _) hTφ φ.symm.differentiableOn fun _ h => h)
      (φ (ch.e z₀)) (by
        rw [Set.mem_preimage, φ.symm_apply_apply]
        exact ChartGlue.mem_over ch.e hch hz₀)
    have hc : ContinuousAt (fun z => φ (ch.e z)) z₀ := φ.continuous.continuousAt.comp (ch.e.continuousAt hch)
    have hev : k =ᶠ[nhds z₀] fun _ => k₀ := by
      filter_upwards [hc.eventually (hB₁.mem_nhds hb₁), ch.e.open_source.mem_nhds hch,
        (isOpen_ptsIn W).mem_nhds hz₀] with z h₁ h₂ h₃
      obtain ⟨Q', hQ', hQu'⟩ := hk z h₃
      refine Fu.disj _ _ Q' (Q _) hQ' (hQ.1 _ h₁) (hQu'.trans ?_)
      rw [hQu _ h₁, φ.symm_apply_apply, ch.e.left_inv h₂]
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have hpt : ∀ (j : Fin Fu.n) (R : (Fu.Di j).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.XF c), x ≫ toF Xo c = spMap e →
      Set.range x ⊆ U → IsPeriod (Fu.Di j) ty R → x ≫ toX Xo c = Fu.u j R → ∃ z ∈ ptsIn B.str e W, k z = j := by
    intro j R x hx hxU hR hxu
    obtain ⟨z, hz⟩ := exists_lift io (x ≫ Y.jQ) (by
      rw [hr]
      exact subset_closure ⟨_, hxU ⟨_, rfl⟩, rfl⟩)
    have hze : z ≫ B.str = spMap e := by
      rw [← hs, ← Category.assoc, hz, Category.assoc]
      exact (congrArg (x ≫ ·) Y.jQ_over).trans hx
    have hzW : (⟨z, hze⟩ : CxPts B.str e) ∈ ptsIn B.str e W :=
      mem_ptsIn.2 ⟨x (IsLocalRing.closedPoint ℂ), (congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) hz).symm⟩
    refine ⟨_, hzW, ?_⟩
    obtain ⟨Q', hQ', hQu'⟩ := hk _ hzW
    have hwx : w ⟨z, hze⟩ = x := (cancel_mono Y.jQ).1 ((hw _ hzW).trans hz)
    exact Fu.disj _ _ Q' R hQ' hR (hQu'.trans (by rw [hwx, hxu]))
  obtain ⟨z, hz, rfl⟩ := hpt i P y hy hU hP hu
  obtain ⟨z', hz', rfl⟩ := hpt i' P' y' hy' hU' hP' hu'
  exact (GlobalTheory.T.isPreconnected_complexPoints_open_variety c.F B e W).constant hcont hz hz'

end GlobalTheory.DetLine.SameIndex
