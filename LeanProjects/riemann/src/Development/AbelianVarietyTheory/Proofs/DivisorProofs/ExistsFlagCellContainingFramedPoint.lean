import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLeadStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIsUnitOfNotMemMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenNbhdPointMemOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorsEqEigenFrameMulInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointImageAndFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesFramedPointOfUnitTriangularChartStatement

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cell_lies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (q : PrimeSpectrum S), ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P q
  classical
  obtain ⟨b, hb⟩ := A.cov ((frX P ≫ Y.j) q)
  obtain ⟨f₀, hf₀, hV⟩ := GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open S Y.X (frX P ≫ Y.j) (A.k b).V q hb
  let ι₀ : S →ₐ[c.F] Localization.Away f₀ := IsScalarTower.toAlgHom c.F S (Localization.Away f₀)
  obtain ⟨P₀, hP₀⟩ := exists_frMap ι₀ P
  have hx₀ : frX P₀ ≫ Y.j = spMap (algebraMap S (Localization.Away f₀)) ≫ frX P ≫ Y.j := by
    rw [← frX_frMap hP₀, Category.assoc]; rfl
  have h₀ : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₀]; exact hV
  choose T hTu hT using GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible E H Dw l Xo c Y p A b _ P₀ h₀
  have hq₀ : (Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q.asIdeal q.2
      ((Ideal.disjoint_powers_iff_notMem _ q.2.isRadical).2 hf₀)
  have hdet : ∀ σ, (T σ).det ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal :=
    fun σ h => hq₀.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem _ _ (T σ) _ hq₀ (hdet σ)
  obtain ⟨f, hf, φ, hφ⟩ := GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' S f₀ q.asIdeal q.2 hf₀ (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1))
    (fun i => (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det) (fun i => hw i.1 _ _)
  refine ⟨f, hf, ?_⟩
  let φ' : Localization.Away f₀ →ₐ[c.F] Localization.Away f := φ.restrictScalars c.F
  have hcomp : φ'.comp ι₀ = IsScalarTower.toAlgHom c.F S (Localization.Away f) :=
    AlgHom.ext fun s => φ.commutes s
  obtain ⟨P₁, hP₁⟩ := exists_frMap φ' P₀
  have hP₁' : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P₁ :=
    hcomp ▸ PullbackSections.frMap_trans ι₀ φ' hP₀ hP₁
  have hx₁ : frX P₁ ≫ Y.j = spMap φ'.toRingHom ≫ frX P₀ ≫ Y.j := by rw [← frX_frMap hP₁, Category.assoc]
  have h₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₁]; exact le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  have hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ), IsUnit ((((T σ).map φ').submatrix (w σ) id).submatrix
      (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro σ k hk
    have h := hφ ⟨σ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    have e : (((T σ).map φ').submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        (φ : Localization.Away f₀ →+* Localization.Away f).mapMatrix
          (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors (Localization.Away f) (Dw.mult σ)
    (((T σ).map φ').submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* Localization.Away f := ev (frX P₁ ≫ Y.j) _ h₁
  let xc : CellVar Dw.mult → Localization.Away f := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  refine ⟨spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w, fun P' hP' => ?_⟩
  obtain rfl := frMap_unique hP₁' hP'
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = frX P₁ ≫ Y.j :=
    hzπ.trans (spMap_ev _ (A.V b).2 h₁)
  refine GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart E H Dw l Xo c c.F (RingHom.id c.F) Y Z π (cellFrames hZ ht)
    (GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht) _ P₁ _ ((b, w) : A.B × Pm Dw.mult) hz hx U hU hUu ?_
  intro σ i
  rw [hT σ _ φ' P₁ hP₁ h₁ hM₁ i]
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * (T σ).map φ' =
      ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * (T σ).map φ') r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

end GlobalTheory.FlagMod.FieldFlag
