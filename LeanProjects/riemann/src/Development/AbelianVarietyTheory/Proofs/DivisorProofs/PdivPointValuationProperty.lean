import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.EigenSplit GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel ReciprocityTheory.ChartRestriction.G.Pdiv TensorProduct in

theorem finrank_eigW_embInt_eq_mult : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg →
    ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E))
      (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C),
      (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) →
      ∀ σ : E →+* ℂ, Module.finrank C (P.eigW (embInt c P.integers σ)) = Dw.mult σ := by
  intro hPr E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ hy k kO P ψ z hPO hFr σ
  obtain ⟨-, -, hcok, hshape⟩ := GlobalTheory.HTKernel.hodgeTateKernelAtPoint hPr p C v O (𝓞 E) P
  have hW : P.W = Submodule.span C (Set.range P.bLie) := hshape.2.2.2.2.2.2
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O (𝓞 E) P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective P.bLie := by
    intro x y hxy
    have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
      rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
    have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
      | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
    refine hb.1 (LinearMap.ext fun f => ?_)
    obtain ⟨z, hz⟩ := hcok f
    have h2 := h1 z
    rw [hz] at h2
    exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2
  have hE : P.eigW (embInt c P.integers σ) =
      Submodule.span C (P.wRec (embInt c P.integers σ) : Set P.V) := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨hw, hwτ⟩
      rw [hW] at hw
      obtain ⟨s, hs, x, hx⟩ := GlobalTheory.HodgeTateEigenRank.exists_smul_mem_of_mem_span (C := C) P.latLie hw
      have hs' : algebraMap O C s ≠ 0 := fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))
      have hxτ : P.bLie x ∈ P.eigV (embInt c P.integers σ) := by
        rw [hx, ← algebraMap_smul C s]
        exact Submodule.smul_mem _ _ hwτ
      have hx' : AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := fun a => hinj (by
        rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])
      have : w = (algebraMap O C s)⁻¹ • P.bLie x := by
        rw [hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)
    · have h := P.wRec_le _ hw
      refine ⟨?_, h.2⟩
      rw [hW]
      exact Submodule.subset_span h.1
  obtain ⟨x, hx⟩ := TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr
  have hli := linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  have hht : HTChar p v P.Gt := by
    letI := io.toAlgebra
    exact htChar_of_pointOver E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hPO
  have hbl := (alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P hht).2 _ _ hli
  have hsp := RecSpan.span_bLie_eq_wRec E H Dw l Xo c p C v O T io y₀ k kO P ψ z hPO hFr σ (x σ) (hx σ)
  rw [hE, ← hsp, Submodule.span_span_of_tower, finrank_span_eq_card hbl, Fintype.card_fin]

end GlobalTheory.CompHt
