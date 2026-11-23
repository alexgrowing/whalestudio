import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSolutiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.TransvChoose

theorem exists_transversal : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro core F E _ _ _ _ _ σ B n r s X hB hX v w hw g hg
  obtain ⟨O, _, c, ι, P, Q, JL, hloc, hcc, h2, hcx, hinj, hAt, hsupp, hcι, hPQ, hQP, hP, hQ, hJh, hJu, hJ, hlat⟩ :=
    GlobalTheory.T.exists_local_dictionary_inertPlace F E σ B n r s X hB hX v w hw
  haveI := hloc
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := by
    simp [GlobalTheory.DblVac.matD]
  obtain ⟨G, G', hGG, hMG⟩ := GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice (AE F E) O ι n P Q (GlobalTheory.InertSph.latAt X v : Set (Fin n → AE F E)) hinj hPQ hQP hP hQ
    (fun z => hlat z) (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv (fun z h1 h2 => by
      obtain ⟨ha, hb⟩ := hg2 z ⟨h1, h2⟩
      exact ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have hgU : (GlobalTheory.DblVac.matD g)ᵀ * Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) * (GlobalTheory.DblVac.matD g).map (cA σ).toRingHom =
      Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) := g.2
  have hU := GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport (AE F E) O ι (cA σ).toRingHom c n P (incM F X.J) JL hinj hcι hJ (GlobalTheory.DblVac.matD g) G hgU hMG
  obtain ⟨ZL, hZL1, hZL2⟩ := GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner O c h2 (fun n J hJ hJd g hgd hgu => core O c hcc h2 hcx n J hJ hJd g hgd hgu)
    n JL G G' hJh hJu hGG hU
  exact GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution F E σ n X v O c ι P Q JL hAt hsupp hcι hPQ hQP hP hQ hJ hlat (GlobalTheory.DblVac.matD g) G ZL hg1 hMG hZL1 hZL2

end GlobalTheory.TransvChoose
