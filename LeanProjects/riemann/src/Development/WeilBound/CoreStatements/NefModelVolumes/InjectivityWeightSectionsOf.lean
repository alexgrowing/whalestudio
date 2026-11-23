import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.WeightSectionsHeightEstimate
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.WeightSectionsCdvrEstimate
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

theorem exists_rat_small (L : HermLB p) (s₀ : L.B.Sec) (hs₀ : genericPoint X ∈ nonzeroLocus s₀) (τ : ℕ) (t : ℝ) :
    ∃ R : (lbPow L.B τ).Sec → X.functionField, Function.Injective R ∧ ∀ h : X.functionField,
      (∀ (c : L.B.ι) (x : X) (hx : x ∈ L.B.U c), RegAt x (h * fnOf (L.B.U c) (gen_mem hx) (s₀.f c) ^ τ)) →
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) (c : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U c)),
        RegAt (under y) (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) →
        ‖ratVal (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) y‖ ^ 2 *
          Real.exp (-((τ : ℝ) * (L.φ σ).φ c y)) ≤ Real.exp (2 * (τ : ℝ) * t)) →
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow τ).smallSec, R S = h := by
  have hr := isRatSec_ratOfSec s₀ hs₀
  have hrτ := GlobalTheory.TrueGeo.SmallSec.isRatSec_pow hr τ
  have hPr := presents_divOfRatSec (L.pow τ).isLB hrτ
  refine ⟨hPr.rat, hPr.rat_injective, fun h hreg hb => ?_⟩
  have hsec : h ∈ (divOfRatSec (L.pow τ).isLB hrτ).sections := by
    refine CartierDiv.mem_sections.2 fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart (L.pow τ).isLB x
    have hx : x ∈ L.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
    refine ⟨_, hPr.isEqn c x hc, ?_⟩
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hx)]
    exact hreg _ x hx
  obtain ⟨S, hS⟩ := hPr.exists_rat_eq hsec
  refine ⟨S, fun σ y => ?_, hS⟩
  let Lτ := (L.shift (fun _ => t) (fun _ => rfl)).pow τ
  obtain ⟨c, hc⟩ := exists_chart Lτ.isLB (under y)
  have hy : y ∈ ptsIn p σ (Lτ.B.U c) := mem_ptsIn.2 hc
  have hy1 : y ∈ ptsIn p σ (L.B.U (c PUnit.unit)) := mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hgen : genericPoint X ∈ Lτ.B.U c := gen_mem hc
  have e0 : fnOf (Lτ.B.U c) hgen ((S : Lτ.B.Sec).f c) =
      h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ := by
    have := hPr.rat_mul S c hgen
    rw [hS, Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem (mem_ptsIn.1 hy1))] at this
    exact this.symm
  have e1 : ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y =
      ratVal (h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ) y := by
    rw [← e0]; exact (ratVal_fnOf hy hgen ((S : Lτ.B.Sec).f c)).symm
  have e2 : (Lτ.φ σ).φ c y = (τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t) := by
    have := Weight.zpow_φ ((L.φ σ).addFn fun _ => 2 * t) (τ : ℤ) c y
    exact this.trans (by push_cast; rfl)
  have hb' := hb σ y (c PUnit.unit) hy1 (hreg _ _ (mem_ptsIn.1 hy1))
  have hn := Weight.nsq_eq (Lτ.φ σ) (secVal_mem (p := p) (σ := σ) (S : Lτ.B.Sec)) hy
  show (Lτ.φ σ).nsq (secVal p σ (S : Lτ.B.Sec)) y ≤ 1
  refine hn.le.trans ?_
  have e4 : secVal p σ (S : Lτ.B.Sec) c y = ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y := by
    erw [secVal_apply]; rfl
  rw [e4, e1, e2]
  have e3 : Real.exp (-((τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t))) =
      Real.exp (-((τ : ℝ) * (L.φ σ).φ (c PUnit.unit) y)) * (Real.exp (2 * (τ : ℝ) * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e3, ← mul_assoc, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  exact hb'

end Generic

theorem eq_zero_of_genVal' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) : f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hZ hf.2

set_option maxHeartbeats 1000000 in

theorem injectivity_weight_sections_of (hK : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t)) : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard := by
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
    hR _ (ChowFormHeightComparison₂.weight_sections_cdvr_estimate hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0
      (ChowFormHeightComparison₂.weight_sections_height_estimate hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0))
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
