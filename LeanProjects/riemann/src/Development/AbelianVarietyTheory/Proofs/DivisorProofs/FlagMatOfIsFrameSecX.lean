import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalAdaptedSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotient
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

theorem flagMat_of_lifts {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f)
    {K : Type} [Field K] (y : Sp K ⟶ Y) (hV : ⊤ ≤ (y ≫ π) ⁻¹ᵁ V) (d : Matrix (Fin r) (Fin r) K)
    (h : ∀ (i : Fin r) (ch : Chart (fl.gr i) 1) (W : Y.Opens) (hW : W ≤ ch.U) (hWV : W ≤ π ⁻¹ᵁ V)
      (t : Γ(fl.F i.succ, W)), (fl.π i).app W t = Twist.resM _ hW (ch.e 0) → ∀ hy : ⊤ ≤ y ⁻¹ᵁ W,
      ∃ cf : Fin r → K, (∀ k, i < k → cf k = 0) ∧
        coordAt hM π hf y hWV hy ((fl.ι i.succ).app W t) = Matrix.vecMul cf d) :
    FlagMat hM π fl hf y d := by
  have hp0 : y (IsLocalRing.closedPoint K) ∈ π ⁻¹ᵁ V := hV (Set.mem_univ (IsLocalRing.closedPoint K))
  obtain ⟨W₀, s, hWV₀, hp, hs⟩ := exists_adapted Y _ r fl _ _ hp0
  have hy₀ : ⊤ ≤ y ⁻¹ᵁ W₀ := (Scheme.preimage_eq_top_of_closedPoint_mem y hp).ge
  have h0 := AdaptMat.flagMat_of_adapted B Y M r hM π fl V f hf K y W₀ hWV₀ hy₀ s hs
  generalize (Matrix.of fun i => coordAt hM π hf y hWV₀ hy₀ (s i)) = S at h0
  have key : ∀ i : Fin r, ∃ a b : Fin r → K, (∀ k, i < k → a k = 0) ∧ a i ≠ 0 ∧ (∀ k, i < k → b k = 0) ∧
      Matrix.vecMul a S = Matrix.vecMul b d := by
    intro i
    obtain ⟨U, e, hU, hpU, hUV, he⟩ := (fl.isVB_gr i).exists_affine hp0
    obtain ⟨W, hWU, hpW, u, hu⟩ := VBExt.exists_lifts (fl.π i) e hpU
    have hy : ⊤ ≤ y ⁻¹ᵁ W := (Scheme.preimage_eq_top_of_closedPoint_mem y hpW).ge
    let ch : Chart (fl.gr i) 1 := { U := U, e := e, isFrame := he }
    obtain ⟨b, hb, hb'⟩ := h i ch W hWU (hWU.trans hUV) (u 0) (hu 0) hy
    obtain ⟨a, ha, ha'⟩ := h0.2 i.succ W (hWU.trans hUV) (u 0) hy
    exact ⟨a, b, fun k hk => ha k hk,
      FlagMat.coeff_ne_zero B Y M r hM π fl V f hf K y S h0 i ch W hWU _ (u 0) (hu 0) hy a ha', hb, ha'.symm.trans hb'⟩
  choose a b ha ha' hb hab using key
  have e : Matrix.of a * S = Matrix.of b * d := by
    ext i k
    exact congrFun (hab i) k
  have hA : IsUnit (Matrix.of a).det := by
    rw [Matrix.det_of_lowerTriangular (Matrix.of a) fun i k hik => ha i k hik]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => ha' i).isUnit
  have h1 := h0.mul hA ha
  rw [e] at h1
  have hB : IsUnit (Matrix.of b).det := by
    have := h1.1
    rw [Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := (Matrix.of b).invertibleOfIsUnitDet hB
  have hbt : (Matrix.of b).BlockTriangular OrderDual.toDual := fun i k hik => hb i k hik
  have h2 := h1.mul (Matrix.isUnit_nonsing_inv_det _ hB)
    fun i k hik => Matrix.blockTriangular_inv_of_blockTriangular hbt hik
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul] at h2

theorem flagMat_of_isFrameSecX : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (Y X Gs : Scheme.{0}) [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    Gs.fromSpecStalk (genericPoint Gs) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) →
    jG ≫ jB = j ≫ ρ ≫ π → jG ≫ πB = πG ≫ (O.Φ.C c).π → ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : IsVB M (O.S.Dw.mult σ)) (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB)
    (_ : IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t)
    (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ)) (r : ∀ i, ((F.root i).pull j).ι → Gs.functionFieldˣ),
    (∀ i, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB t π ρ F j φ jG i (r i)) →
    (∀ (V : Bs.Opens) (f : Fin (O.S.Dw.mult σ) → Γ(M, V)) (hf : IsFrame f)
      (hxV : ⊤ ≤ ((genPt Gs ≫ jG) ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin (O.S.Dw.mult σ)) (Fin (O.S.Dw.mult σ)) Gs.functionField),
      (∀ i, IsCombAtG O.s.T.Z.t (genPt Gs ≫ jG ≫ πB ≫ genι O.s.T.Z) (t V f hf Gs.functionField (genPt Gs ≫ jG) hxV) (d i)
        (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v σ i)) →
      haveI := hM.isQuasicoherent
      GlobalTheory.FlagCls.FlagMat (hM.pullback π) ρ F (hf.pullback π) (genPt Gs ≫ j) d) := by
  intro D O c Bs Bg jB πB Y X Gs _ _ π ρ j πG φ jG _ h1 _ σ M hM t ht F r hr V f hf hxV d hd
  have := hM.isQuasicoherent
  have hb := ht.1 V f hf Gs.functionField (genPt Gs ≫ jG) hxV
    (Spec.preimage ((genPt Gs ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom)).hom (Spec.map_preimage _).symm
  rw [Category.assoc _ jG (πB ≫ genι _)] at hb
  have hz : (genPt Gs ≫ jG) ≫ jB = ((genPt Gs ≫ j) ≫ ρ) ≫ π := by simp only [Category.assoc, h1]
  refine flagMat_of_lifts _ ρ F _ _ (by rw [hz] at hxV; exact hxV) d fun i ch W hW hWV s hs hy => ?_
  obtain ⟨w, cf, hw, hw', -, hcf⟩ := hr i (fun _ => ch) V f hf W hW hWV s hs hy hxV
  refine ⟨cf, hcf, ?_⟩
  have e1 := tanLinG _ (fun k => (hb.1 k).1) _ d.transpose cf w hd hw'
  rw [Matrix.mulVec_transpose] at e1
  exact GlobalTheory.FlagSec.indep_of_isEigBasis hb _ _ _ hw e1

end GlobalTheory.FlagCls

end
