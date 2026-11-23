import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open GlobalTheory.ThK GlobalTheory.KSplit
noncomputable section
namespace GlobalTheory.LinWSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.LinWSplit
namespace GlobalTheory.LinWSplit
theorem exists_linearFunctional_at_split_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX := hP.herm.herm
  have hY := hP.skew.skew
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (W.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (W.J.map t).det = (t : E →+* Fv F v) W.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hat_add : ∀ x y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → At (evFin F v) y →
      At (evFin F v) (x + y) := fun x y hx hy r hr => by rw [smul_add, hx r hr, hy r hr, add_zero]
  have heq := fun (u u' : Matrix (Fin n) (Fin d) (AE F E)) => locCo_eq_of hcm X W hX hY M t u u'
  let P0 : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) := fun Y => b.1 * Y * c.1ᵀ
  let Q : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun z => -((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * z * (c⁻¹).1 * ((W.J.map t)ᵀ)⁻¹)
  have hP0 : ∀ P, P0 ((b⁻¹).1 * P * (c⁻¹).1ᵀ) = P := by
    intro P
    simp only [P0, ← Matrix.mul_assoc]
    rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hQ : ∀ P, Q (-(b.1ᵀ * X.J.map t * P * (W.J.map t)ᵀ * c.1)) = P := by
    intro P
    simp only [Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((b⁻¹).1ᵀ), show (b⁻¹).1ᵀ * b.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp,
      Matrix.one_mul, ← Matrix.mul_assoc (c.1), show c.1 * (c⁻¹).1 = 1 by simp, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hA]
  have hcoX0 : ∀ Y, GlobalTheory.FlipMatch.coX t b c (U (P0 Y) 0) = Y := by
    intro Y
    simp only [GlobalTheory.FlipMatch.coX, hU0, P0, ← Matrix.mul_assoc]
    rw [show (b⁻¹).1 * b.1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show c.1ᵀ * (c⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hcoY1 : ∀ z, GlobalTheory.FlipMatch.coY σ X W t b c (U 0 (Q z)) = z := by
    intro z
    simp only [GlobalTheory.FlipMatch.coY, hU1, Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      ← Matrix.mul_assoc (b.1ᵀ), show b.1ᵀ * (b⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.one_mul,
      show (c⁻¹).1 * c.1 = 1 by simp, Matrix.mul_one]
  have hcoY0 : ∀ P, GlobalTheory.FlipMatch.coY σ X W t b c (U P 0) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coY, hU1]
  have hcoX1 : ∀ P, GlobalTheory.FlipMatch.coX t b c (U 0 P) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coX, hU0]
  have hU00 : GlobalTheory.LatVac.locCo M.co v (U 0 0) = 0 :=
    locCo_eq_zero hcm X W hX hY M t _ (hUat 0 0) (hU0 0 0) (hU1 0 0)
  have hadd0 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U (P + P') 0) =
      GlobalTheory.LatVac.locCo M.co v (U P 0) + GlobalTheory.LatVac.locCo M.co v (U P' 0) := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1, add_zero]
  have hadd1 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U 0 (P + P')) =
      GlobalTheory.LatVac.locCo M.co v (U 0 P) + GlobalTheory.LatVac.locCo M.co v (U 0 P') := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0, add_zero]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1]
  let wT : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun Y => GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0)
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * 0 * c.1ᵀ) 0) = 0
        rw [Matrix.mul_zero, Matrix.zero_mul]; exact hU00
      map_add' := fun Y Y' => by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * (Y + Y') * c.1ᵀ) 0) = _
        rw [Matrix.mul_add, Matrix.add_mul]; exact hadd0 _ _ }
  let wM : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun z => GlobalTheory.LatVac.locCo M.co v (U 0 (Q z))
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q 0)) = 0
        have : Q 0 = 0 := by simp [Q]
        rw [this]; exact hU00
      map_add' := fun z z' => by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q (z + z'))) = _
        have : Q (z + z') = Q z + Q z' := by simp only [Q, Matrix.mul_add, Matrix.add_mul, neg_add]
        rw [this]; exact hadd1 _ _ }
  have hwT : ∀ Y, wT Y = GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0) := fun _ => rfl
  have hwM : ∀ z, wM z = GlobalTheory.LatVac.locCo M.co v (U 0 (Q z)) := fun _ => rfl
  have hform := fun (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) =>
    (locCo_form M.co v x u).trans (evFin_symp hcm X W hX hY t b c x u hx)
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v
  have hψne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_anyCharacter (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψne wT wM
    (fun Y Y' => by
      rw [hwT, hwT, hform _ _ (hUat _ _), hcoX0, hcoX0, hcoY0, hcoY0]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun z z' => by
      rw [hwM, hwM, hform _ _ (hUat _ _), hcoX1, hcoX1, hcoY1, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun Y z => by
      rw [hwT, hwM, hform _ _ (hUat _ _), hcoX0, hcoX1, hcoY0, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      refine ⟨GlobalTheory.FlipMatch.coX t b c u, GlobalTheory.FlipMatch.coY σ X W t b c u, ?_⟩
      rw [hwT, hwM, ← map_add]
      apply heq _ _ (hat_add _ _ (hUat _ _) (hUat _ _)) hu
      · rw [Matrix.map_add _ (map_add _), hU0, hU0, add_zero]
        exact hP0 _
      · rw [Matrix.map_add _ (map_add _), hU1, hU1, zero_add]
        exact hQ _)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wT (GlobalTheory.FlipMatch.coX t b c u) := by
      rw [hwT]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact (hP0 _).symm
      · rw [hU1]; exact hu0
    rw [e1, e2]
    exact congrFun (htr _ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wM (GlobalTheory.FlipMatch.coY σ X W t b c u) := by
      rw [hwM]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact hu1
      · rw [hU1]; exact (hQ _).symm
    have hcx : GlobalTheory.FlipMatch.coY σ X W t b c x = 0 := by simp [GlobalTheory.FlipMatch.coY, hx0]
    rw [e1, e2, congrFun (hmu _ φ hφ), GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp σ _ _ x u hx),
      evFin_symp hcm X W hX hY t b c x u hx, hcx, ← GlobalTheory.LatVac.psiAt_apply]
    simp [GlobalTheory.FlipMatch.pairM, GlobalTheory.FlipMatch.coX]
end GlobalTheory.LinWSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_linearFunctional_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  first | exact @_root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | exact _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | (intros; apply _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place <;> assumption)
end
