import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.InjectivityWeightSectionsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightLowerBoundOfRegulator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RegulatorLowerBound

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
namespace PositivityTheory.Xj7N.Inj
open GlobalTheory
section Generic
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
end Generic
set_option maxHeartbeats 1000000 in
theorem small_sections_injective_of_self_intersection_bound (hK : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t)) : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi
  have hex : ∃ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0),
      genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hz : genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := by
      have hle : Submodule.span Y.d.c₂.F (latOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≤
          LinearMap.ker (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) :=
        Submodule.span_le.2 fun v hv => by
          simpa [genPoint] using hno ⟨v, hv⟩
      rw [hGood.2.2] at hle
      exact LinearMap.ext fun v => hle Submodule.mem_top
    have h0 : Y.dg u Z = 0 := by
      show ((compDeg Y.U Z (wtOf (T.Q.Dw j) u 0) : ℕ) : ℝ) = 0
      rw [compDeg, hz, GlobalTheory.CompHt.Test.imageDeg_zero, Nat.cast_zero]
    exact absurd hdg (by rw [h0]; exact lt_irrefl 0)
  obtain ⟨w, hw⟩ : ∃ w, genericPoint X ∈ nonzeroLocus (s w) := by
    have h : genericPoint X ∈ (⨆ w, nonzeroLocus (s w) : X.Opens) := by
      rw [hM.bpf]; trivial
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at h
    exact h
  obtain ⟨k₀, hk₀⟩ := exists_chart L.isLB (genericPoint X)
  have hw0 : genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    intro h0
    obtain ⟨w₁, hw₁⟩ := hex
    have hr := hM.ratio w₁ w k₀ hk₀
    have e0 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) = 0 := by
      have : (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := h0
      rw [this, map_zero]
    have h1 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w₁ : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≠ 0 :=
      (map_ne_zero_iff ψ hM.bij.1).2 hw₁
    exact mul_ne_zero h1 (fnOf_sec_ne_zero hw hk₀) (hr.trans (by rw [e0, zero_mul]))
  have hψinj : Function.Injective ψ := hM.bij.1
  obtain ⟨R, hRinj, hR⟩ := exists_rat_small L (s w) hw (8 * i) t
  have key : ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t,
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec, R S = ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) *
          (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) := fun f hf =>
    hR _ (_root_.ChowFormHeightComparison₂.height_lower_bound_of_regulator hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0
      (_root_.ChowFormHeightComparison₂.regulator_lower_bound hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0))
      (hK hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0)
  choose! Sf hSf hRf using key
  have hinj : Set.InjOn Sf (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t) := by
    intro f hf g hg hfg
    have h1 := (hRf f hf).symm.trans ((congrArg R hfg).trans (hRf g hg))
    have hψw : ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 :=
      (map_ne_zero_iff ψ hψinj).2 hw0
    have hc : (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero hψw)
    have h2 := hψinj (mul_right_cancel₀ hc h1)
    have h3 : genVal Z ((f : Rul Y.d.Xo₂ Y.d.c₂) - (g : Rul Y.d.Xo₂ Y.d.c₂)) = 0 := by
      rw [map_sub, h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_genVal' (Submodule.sub_mem _ f.2 g.2) h3))
  rw [← hinj.encard_image]
  exact Set.encard_le_encard (Set.image_subset_iff.2 fun f hf => hSf f hf)
end PositivityTheory.Xj7N.Inj
end
end
