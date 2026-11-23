import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusBasisTensorLatticeFree
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitInvertibleMatrixIdentificationBasis
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonImageEisensteinPowPhiInvColumns
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FiltrationEqSpanOfEisensteinPowBasisChange
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (α β : ℕ), (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → (∀ v ∈ P.M, E ↥LL.1 l e ^ β • v ∈ P.L) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), w ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) ((β : ℤ)) ↔ ∃ d : ι → OD l ↥(OL LL), w = ∑ i, act (d i) (∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1)))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Pl AI Td hC X hX act hA α β _ _ hβ w
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  have hb0 := (GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b).1
  obtain ⟨m, m', u, r, hu, hm, hr, hrm⟩ := UpperTheory.KN.exists_unit_invertible_matrix_identification_basis l a e ϖ LL ι P T I b
  have hf := UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns l a e ϖ LL ι P T I jB Pl AI Td hC X hX act hA b m u r hu hr hrm β hβ
  exact UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange _ _ act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j))
    hshift ι β
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) m m' hm hf hb0 w
