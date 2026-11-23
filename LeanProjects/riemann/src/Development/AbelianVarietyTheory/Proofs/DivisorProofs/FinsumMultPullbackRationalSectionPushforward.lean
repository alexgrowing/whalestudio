import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimAddOneLeOfSsubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSchemeOrdPullbackResidueDegreeCodimOneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PushDiv

theorem hasDim_lt {X : Scheme.{0}} {x y : X} {d d' : ℕ} (hxy : y ⤳ x) (hne : x ≠ y)
    (hx : HasDim x d) (hy : HasDim y d') : d < d' := by
  have hsub : closure ({x} : Set X) ⊆ closure {y} := specializes_iff_closure_subset.1 hxy
  have hne' : closure ({x} : Set X) ≠ closure {y} := fun e =>
    hne (inseparable_iff_closure_eq.2 e).eq
  have h := topologicalKrullDim_add_one_le_of_ssubset X _ _ isClosed_closure
    isIrreducible_singleton.closure isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub hne')
  rw [show topologicalKrullDim (closure ({x} : Set X)) = d from hx,
    show topologicalKrullDim (closure ({y} : Set X)) = d' from hy] at h
  have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d' : WithBot ℕ∞) := by exact_mod_cast h
  have h'' : d + 1 ≤ d' := by exact_mod_cast h'
  omega

theorem mult_genericPoint {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] (D : CartierDiv Z) :
    D.mult (genericPoint Z) = 0 := by
  rw [(D.isEqn_genericPoint 1).mult_eq]
  exact (unitAt_one _).ord_eq_zero

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)

theorem mult_pull_eq (w : Y) (i : B.ι) (hi : g w ∈ B.U i) :
    (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w =
      Scheme.ord (TrueGeo.SmallSec.fnMap g hη' (r i : X.functionField)) w :=
  by
  have hm : w ∈ (B.pull g).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have h := (presents_divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).isEqn
    (fun _ => i) w hm
  rw [h.mult_eq]
  rfl

theorem mult_eq_chart (z : X) (i : B.ι) (hi : z ∈ B.U i) :
    (divOfRatSec hB hr).mult z = Scheme.ord (r i : X.functionField) z :=
  ((presents_divOfRatSec hB hr).isEqn i z hi).mult_eq

theorem map_ne_genericPoint (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0) :
    g w ≠ genericPoint X := by
  intro e
  obtain ⟨i, hi⟩ := exists_chart hB (g w)
  apply hw
  rw [mult_pull_eq g hη' hB hr w i hi]
  exact (FrameGlue.Pull.unitAt_fnMap g hη' (e ▸ unitAt_genericPoint (r i).ne_zero)).ord_eq_zero

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem degree_ne_zero_and_coheight (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) (w : Y)
    (hw : (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w ≠ 0)
    (hd : g.residueDegree w ≠ 0) :
    g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight (g w) = 1 := by
  have hw1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hw
  have hgw := map_ne_genericPoint g hη' hB hr w hw
  have hwY : w ≠ genericPoint Y := fun e => hw (e ▸ mult_genericPoint _)
  have AY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  have AX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  obtain ⟨mY, hmY⟩ := AY.1
  obtain ⟨mX, hmX⟩ := AX.1
  obtain ⟨dY, -, hdY⟩ := hmY (genericPoint Y)
  obtain ⟨dw, -, hdw⟩ := hmY w
  have hlt : dw < dY := hasDim_lt (genericPoint_specializes w) hwY hdw hdY
  obtain ⟨e, rfl⟩ : ∃ e, dY = e + 1 := ⟨dY - 1, by omega⟩
  have hYdim : topologicalKrullDim Y = ((e + 1 : ℕ) : WithBot ℕ∞) := (AY.2.2.2.2.2 Y (e + 1)).1 hdY
  have hwe : HasDim w e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hYdim).1 w).1 hw1
  obtain ⟨dgw, -, hdgw⟩ := hmX (g w)
  obtain ⟨dX, -, hdX⟩ := hmX (genericPoint X)
  have h1 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg w e dgw hwe hdgw
  have hdX' : HasDim (g (genericPoint Y)) dX := by rw [hη]; exact hdX
  have h2 := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hp hq g hg (genericPoint Y) (e + 1) dX hdY hdX'
  have h3 : dgw < dX := hasDim_lt (genericPoint_specializes (g w)) hgw hdgw hdX
  have he : e = dgw := h1.2.1 hd
  have hXe : dX = e + 1 := by omega
  refine ⟨h2.2.2 hXe.symm, ?_⟩
  have hXdim : topologicalKrullDim X = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (AX.2.2.2.2.2 X (e + 1)).1 (hXe ▸ hdX)
  exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hp e hXdim).1 (g w)).2 (he ▸ hdgw)

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : Y ⟶ X) (hη' : g (genericPoint Y) ⤳ genericPoint X) {B : LB X} (hB : B.IsLB)
  {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r)
  {k : Type} [CommRing k] {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

open Classical in

theorem fiber_sum (hp : IsAmb p) (hq : IsAmb q) (hg : g ≫ p = q)
    (hη : g (genericPoint Y) = genericPoint X) [CompactSpace Y] (z : X) :
    ∑ w ∈ (CartierDiv.finite_support_mult
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr))).toFinset with g w = z,
      (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
        (g.residueDegree w : ℤ) =
    (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
  by_cases h : g.residueDegree (genericPoint Y) ≠ 0 ∧ Order.coheight z = 1
  · obtain ⟨i, hi⟩ := exists_chart hB z
    have H := GlobalTheory.T.sum_schemeOrd_pullback_residueDegree_codimOne k X Y p q hp hq g hg hη h.1 z h.2 (r i : X.functionField) (r i).ne_zero
    have H2 : ∑ᶠ w ∈ g ⁻¹' {z},
        (divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g hη' hr)).mult w *
          (g.residueDegree w : ℤ) =
        (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z := by
      rw [mult_eq_chart hB hr z i hi, ← H]
      refine finsum_mem_congr rfl fun w hw => ?_
      have hw' : g w = z := hw
      rw [mult_pull_eq g hη' hB hr w i (by rw [hw']; exact hi)]
    rw [← H2]
    refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter,
      Set.Finite.mem_toFinset, Function.mem_support, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨left_ne_zero_of_mul h2, h1⟩, h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · have hR : (g.residueDegree (genericPoint Y) : ℤ) * (divOfRatSec hB hr).mult z = 0 := by
      by_cases hδ : g.residueDegree (genericPoint Y) = 0
      · rw [hδ, Nat.cast_zero, zero_mul]
      · have hz : Order.coheight z ≠ 1 := fun hz => h ⟨hδ, hz⟩
        rw [show (divOfRatSec hB hr).mult z = 0 from
          by_contra fun h0 => hz (CartierDiv.coheight_eq_one_of_mult_ne_zero h0), mul_zero]
    rw [hR]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hwz : g w = z := (Finset.mem_filter.1 hw).2
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 : g.residueDegree w ≠ 0 := fun h0 => hne (by rw [h0, Nat.cast_zero, mul_zero])
    obtain ⟨hδ, hc⟩ := degree_ne_zero_and_coheight g hη' hB hr hp hq hg hη w h1 h2
    exact h ⟨hδ, hwz ▸ hc⟩

end GlobalTheory.PushDiv

namespace GlobalTheory.PushDiv

theorem finsum_mult_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), ∀ (B : LB X) (hB : B.IsLB) (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (φ : X → ℝ), ∑ᶠ w, ((divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr)).mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) = (g.residueDegree (genericPoint Y) : ℝ) * ∑ᶠ z, ((divOfRatSec hB hr).mult z : ℝ) * φ z := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη B hB r hr φ
  classical
  haveI := hq.isNoetherian
  haveI := hp.isNoetherian
  set D' := divOfRatSec (LB.isLB_pull hB g) (MultPull.isRatSec_pull_map g
    (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) with hD'
  set D := divOfRatSec hB hr with hD
  set S := D'.finite_support_mult.toFinset with hS
  set T := S.image g ∪ D.finite_support_mult.toFinset with hT
  have hL : ∑ᶠ w, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) =
      ∑ w ∈ S, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w)) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hw (by simp only [h0, Int.cast_zero, zero_mul])
  have hR : ∑ᶠ z, (D.mult z : ℝ) * φ z = ∑ z ∈ T, (D.mult z : ℝ) * φ z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr fun h0 => hz (by simp only [h0, Int.cast_zero, zero_mul])
  rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := g)
    (fun w hw => Finset.mem_union_left _ (Finset.mem_image_of_mem g hw)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hF := fiber_sum g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hB hr hp hq hg hη z
  calc ∑ w ∈ S with g w = z, (D'.mult w : ℝ) * ((g.residueDegree w : ℝ) * φ (g w))
      = ((∑ w ∈ S with g w = z, D'.mult w * (g.residueDegree w : ℤ) : ℤ) : ℝ) * φ z := by
        rw [Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [(Finset.mem_filter.1 hw).2]
        push_cast
        ring
    _ = (g.residueDegree (genericPoint Y) : ℝ) * ((D.mult z : ℝ) * φ z) := by
        rw [hF]
        push_cast
        ring

end GlobalTheory.PushDiv
