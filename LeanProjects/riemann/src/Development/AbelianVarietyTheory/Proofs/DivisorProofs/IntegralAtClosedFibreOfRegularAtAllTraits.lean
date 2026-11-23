import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubringStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_chart_affineOpen {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    (hL : L.IsLB) (x : G.left) : ∃ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (_ : W ≤ L.U j) (_ : W ≤ G.hom ⁻¹ᵁ U),
      x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen U := by
  obtain ⟨j, hj⟩ := exists_chart hL x
  obtain ⟨U, hUa, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hWa, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  exact ⟨j, U, W, fun y hy => (hWle hy).1, fun y hy => (hWle hy).2, hxW, hWa, hUa⟩

theorem intAt_closed_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs x hx
  obtain ⟨j, U, W, hW, hWU, hxW, hWa, hUa⟩ := exists_chart_affineOpen M G L hL x
  obtain ⟨hinj, hloc⟩ := GlobalTheory.T.generic_chart_functions_fractions_smooth R M G hsm Y α t hpb W U hWU hWa hUa
  haveI : IsIntegral G.left := GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification R M G hsm hgi ⟨x⟩
  haveI : IsLocallyNoetherian G.left := GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification R M G hsm
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI : IsNoetherianRing Γ(G.left, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
  let p : Ideal Γ(G.left, W) := RingHom.ker ((G.left.residue x).hom.comp (G.left.presheaf.germ W x hxW).hom)
  obtain ⟨d, hd, hi⟩ := GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (α.app W).hom hinj hloc p (RingHom.ker_isPrime _)
    (chartVal L α s j W hW) (fun F _ β V hV h1 h2 =>
      GlobalTheory.T.chartValue_mem_dominating_valuationSubring R M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hxW hx F β V hV h1
        (fun c hc => h2 c (RingHom.mem_ker.2 hc)))
  refine GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue L α k s j W hW hWa x d ?_ hi
  rw [Scheme.mem_basicOpen _ _ _ hxW]
  have : (G.left.residue x).hom ((G.left.presheaf.germ W x hxW).hom d) ≠ 0 := fun h => hd (RingHom.mem_ker.2 h)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 this

end GlobalTheory.Mum
