import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionIsFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfDetSymSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalization
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.Cartier
open scoped Classical
set_option autoImplicit false

theorem GlobalTheory.FlatRat.exists_unit_ratSec_comb_root : ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (W : O.LatModel ∅ c) (τ : D.what₂.Tau), ∃ r : ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j).ι → W.V.G.functionFieldˣ, GlobalTheory.Cartier.IsRatSec ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j) r ∧ ∀ i, ∀ x ∈ ((GlobalTheory.ArInt.comb (fun i : Fin O.N => W.root ∅ (τ, i)) (fun _ => 1)).B.pull W.V.j).U i, UnitAt x (r i : W.V.G.functionField) := by
  intro D O hC c W τ
  have hdr := hC.dualRef
  set Y := O.var c with hYdef
  set Dv : Fin O.N → Y.Dv := fun i => (O.root0 c ∅ (τ, i)).D with hDv
  have hN : ∀ i : Fin O.N, GlobalTheory.CoverNorm.Norms W.V (W.root ∅ (τ, i)) (fun x => genAt (O.root0 c ∅ (τ, i)).D x ^ 1) _ _ :=
    fun i => GlobalTheory.CoverNorm.norms_of_induces (Setup.induces_root0 D O hdr ∅ c W ∅ subset_rfl (τ, i))
  obtain ⟨r, hr, hu, -, -⟩ := GlobalTheory.CoverNorm.norms_comb hN (fun _ => 1)
  have hF := GlobalTheory.ShFam.Hor.isFlat_flatSec D O.A O.N O.j O.S O.κ O.s O.Φ c τ

  have hdivsum : ∀ (s : Finset (Fin O.N)) (n : Fin O.N → Letter O.S.Dw → ℤ),
      divOf (O.Φ.C c) (∑ i ∈ s, n i) = ∑ i ∈ s, divOf (O.Φ.C c) (n i) := by
    intro s n
    simp only [divOf, Finset.sum_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hind : ArIn.ind ∅ = fun _ => false := by
    funext q; simp [ArIn.ind]
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hsum : divOf (O.Φ.C c) (expo O.S.Dw (detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ))) = ∑ i, Dv i := by
    have e1 : detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ) =
        ∑ i : Fin O.N, rootSym O.S.Dw (ArIn.ind ∅) none (DV.tauEmb D τ) (i : ℕ) := by
      rw [hind, detSym, hpq, Fin.sum_univ_eq_sum_range (fun i => rootSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ) i)]
    rw [e1, GlobalTheory.CovolFin.expo_sum, hdivsum]
    rfl
  have hgen : ∀ y : Y.X, (∑ i, Dv i).GeneratesAt y (∏ i, genAt (Dv i) y) := by
    intro y
    refine Finset.induction_on (Finset.univ : Finset (Fin O.N)) ?_ ?_
    · simpa using (CartierDiv.generatesAt_zero_iff (x := y) (f := (1 : Y.Fn))).2 (unitAt_one y)
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (generatesAt_genAt (Dv a) y).mul ih

  set fl := flatSec O.s O.Φ c τ with hfl
  have hq : ∀ y : Y.X, UnitAt y (fl * (∏ i, genAt (Dv i) y)⁻¹) := by
    intro y
    have h1 : (∑ i, Dv i).GeneratesAt y fl := hsum ▸ hF y
    obtain ⟨t, ht⟩ := (∑ i, Dv i).exists_isEqn y
    have a1 := ht.generatesAt_iff.1 h1
    have a2 := ht.generatesAt_iff.1 (hgen y)
    have e : fl * (∏ i, genAt (Dv i) y)⁻¹ = (fl * (t : Y.Fn)) * ((∏ i, genAt (Dv i) y) * (t : Y.Fn))⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel₀ (Units.ne_zero t), mul_one]
    rw [e]
    exact a1.mul a2.inv
  have hfl0 : fl ≠ 0 := (hF (genericPoint Y.X)).ne_zero
  have hφ0 : W.V.φ fl ≠ 0 := (map_ne_zero _).2 hfl0
  refine ⟨fun i => Units.mk0 (W.V.φ fl) hφ0 * r i, ?_, ?_⟩
  · intro i j h
    simp only [Units.val_mul, Units.val_mk0]
    rw [hr i j h]
    ring
  · intro i x hx
    have H := hu i x hx
    simp only [pow_one, one_pow] at H
    have hp0 : (∏ k, genAt (Dv k) (W.V.π x)) ≠ 0 := (hgen (W.V.π x)).ne_zero
    have e : ((Units.mk0 (W.V.φ fl) hφ0 * r i : W.V.G.functionFieldˣ) : W.V.G.functionField) =
        W.V.φ (fl * (∏ k, genAt (Dv k) (W.V.π x))⁻¹) * (W.V.φ (∏ k, genAt (Dv k) (W.V.π x)) * r i) := by
      have : W.V.φ (∏ k, genAt (Dv k) (W.V.π x)) ≠ 0 := (map_ne_zero _).2 hp0
      rw [Units.val_mul, Units.val_mk0, map_mul, map_inv₀]
      field_simp
    rw [e]
    exact (W.V.unitAt_φ (hq _)).mul (by simpa only [pow_one, zpow_one] using H)
