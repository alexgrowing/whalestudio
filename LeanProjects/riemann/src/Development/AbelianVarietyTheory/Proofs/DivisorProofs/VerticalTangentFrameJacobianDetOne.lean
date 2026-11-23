import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBigCellCoordinateJacobianVerticalChangesEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LuDecompositionUnitriangularUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeBasePullbackEqZeroAlongVerticalDeformaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointVectorsVerticalDeformationEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUniqueStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.vert_jac_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h K _ _ z hz P₀ P hU hzP hPG hB w zw hzw hw hzw'
  have key : ∀ b σ', (N σ').map (ev (zw b) W (hzw b)) = GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
      ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
    intro b σ'
    have hx : frX (w b) ≫ TF.Y.j = zw b ≫ toBase TF Z := by
      rw [toBase, ← Category.assoc, hzw' b]; exact (TF.X.lies_ptY (w b)).1.symm
    have hUx : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzw b)
    have hk : ⊤ ≤ (zw b ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 (hzw b)
    have hM : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ (TF.X.F.M k).U := TF.X.F.inM hk (Category.assoc _ _ _)
    obtain ⟨B, hBl, hBu, hBc⟩ := GlobalTheory.T.bigCell_framedPointVectors_lowerTriangular_eigenbasis E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (w b) (zw b) (hzw b)
      _ hx hUx (hzw' b)
    have hF := GlobalTheory.T.framedPointVectors_verticalDeformation_eigenbasis E H Dw l Xo c TF U n e v hv K P₀ P hU _ hPG hB (Pi.single b.toF (1 : K)) (w b) _ hx hUx
      (TF.X.F.M k).toMChart hM (hw b)
    have eq : B σ' * (L σ').map (ev (zw b) W (hzw b)) * (N σ').map (ev (zw b) W (hzw b)) =
        GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
          ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
      refine Matrix.ext fun i j => ?_
      have := GlobalTheory.T.bigCell_eigenbasisCombination_coeff_unique E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (zw b) (hzw b) _ rfl hUx σ' _ _ _
        (hBc σ' i) (hF σ' i)
      have := congrFun this j
      simpa [Matrix.map_mul, Matrix.mul_assoc] using this
    have hN : ∀ i j, j < i → (N σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN1 : ∀ i, (N σ').map (ev (zw b) W (hzw b)) i i = 1 := fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hL : ∀ i j, i < j → (L σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.1 σ' i j hij]
    have hN0 : ∀ i j, j < i → ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i j = 0 :=
      fun i j hij => by simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN01 : ∀ i, ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i i = 1 :=
      fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hbt : ∀ (p q : Fin (Dw.mult σ')), some ⟨σ', (p, q)⟩ = b.toF → p < q := by
      intro p q hpq
      obtain ⟨σb, ⟨⟨i, j⟩, hij⟩⟩ := b
      simp only [GlobalTheory.FlagTan.VIx.toF, Option.some.injEq, Sigma.mk.inj_iff] at hpq
      obtain ⟨rfl, hq⟩ := hpq
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (eq_of_heq hq)
      exact hij
    have hU0 : ∀ i j, j < i → GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i j = 0 := fun i j hij => by
      have h1 : (1 : Matrix (Fin (Dw.mult σ')) (Fin (Dw.mult σ')) K) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, j)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i j hh) (not_lt.2 hij.le)) _
      simp [GlobalTheory.FlagTan.unip, h1, h2]
    have hU1 : ∀ i, GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i i = 1 := fun i => by
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, i)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i i hh) (lt_irrefl _)) _
      simp [GlobalTheory.FlagTan.unip, h2]
    exact GlobalTheory.T.lu_decomposition_unitriangular_unique _ _ _ _ _ _ _ (hBl σ') hL hN hN1 hU0 hU1 hN0 hN01 eq
  refine ⟨?_, fun b r => GlobalTheory.T.derivative_basePullback_eq_zero_along_verticalDeformation E H Dw l Xo c TF Z U.1 W h.2.1 K P _ (w b) (zw b) (hzw b) (hw b) (hzw' b) r⟩
  have hM : ∀ σ i j, j < i → (N σ).map (ev z W hz) i j = 0 := fun σ i j hij => by simp [h.2.2.2.2.2.1 σ i j hij]
  have hM1 : ∀ σ i, (N σ).map (ev z W hz) i i = 1 := fun σ i => by simp [h.2.2.2.2.2.2.1 σ i]
  convert GlobalTheory.T.det_bigCellCoordinateJacobian_verticalChanges_eq_one E H Dw K (fun σ => (N σ).map (ev z W hz)) hM hM1 using 2
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.of_apply, cellCoord]
  rw [← key b a.1]
  rfl
