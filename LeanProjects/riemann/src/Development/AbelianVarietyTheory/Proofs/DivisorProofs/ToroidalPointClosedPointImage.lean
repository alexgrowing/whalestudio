import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InteriorFibre

theorem exists_polAV_of_not_mem_genBd : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K] (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z), yK (IsLocalRing.closedPoint K) ∉ GlobalTheory.Toroidal.genBd Z → ∃ (P₀ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (θ : P₀.A.left ⟶ Z.t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback P₀.A Z.t.G (yK ≫ GlobalTheory.Toroidal.genι Z) θ ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso (Z.t.PP.L.pull θ) P₀.L := by
  intro E _ _ _ H Dw l Xo c Z K _ _ yK hy
  have hr : Set.range yK ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst hp
    by_contra h
    exact hy (GlobalTheory.Toroidal.mem_genBd.2 h)
  haveI := Z.jQ_open
  let y' := IsOpenImmersion.lift Z.jQ yK hr
  have hy' : y' ≫ Z.jQ = yK := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull y' Z.oF.t
  generalize (⟨(Over.pullback y').obj Z.oF.t.G, IsSemiAbelian.pullback y' Z.oF.t.G Z.oF.t.semi,
    OAct.pullback y' Z.oF.t.G Z.oF.t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m m₁
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, g, -⟩ := m₁.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := Xo.XF c) (U := ⊤)
    (x := y' (IsLocalRing.closedPoint K)) trivial
  have hyU : ∀ x, y' x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y' hc)).mpr trivial
  have am := relAmple_pull m₁.cart.1 Z.oF.t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) U hU hyU Z.oF.ample
  have kt := kTriv_pull m₁.cart Z.oF.t.PP.isLB t'.PP.isLB ((isGen_iff w).1 g) Z.oF.ktriv
  have := GlobalTheory.LocalFibre.connectedSpace_sp K
  have : ConnectedSpace t'.G.left := GeometricallyConnected.connectedSpace t'.G.hom t'.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t'.G.hom (eSec t'.G (IsLocalRing.closedPoint K))
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  obtain ⟨wn, gn, -⟩ := n.lin
  have e : y' ≫ Z.jQ ≫ pullback.fst _ _ = yK ≫ GlobalTheory.Toroidal.genι Z := by
    rw [← Category.assoc, hy']
  refine ⟨{ A := t'.G, g := d, smoothDim := hd, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt,
            isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 Z.oF.proper, ‹_›⟩,
            rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩,
            sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ },
    m₁.φ ≫ Z.m.φ, ?_, ?_⟩
  · rw [← e, ← hn]; exact n.cart
  · have h : LBIso t'.PP.L (Z.t.PP.L.pull n.φ) := ⟨wn, gn⟩
    rw [hn] at h
    exact h.symm

end GlobalTheory.InteriorFibre
