import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdelicNormVecMulLeMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizationPureIntegrand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerUnipotentCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentralCharacterHypothesis
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalWhittakerNorm

variable {K : Type} [Field K] [NumberField K]

theorem isUnit1_localChar' (c : HeckeCharacter K) (w : PlK K) : IsUnit1 (localChar c w) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem isUnit1_cAt' (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    IsUnit1 (cAt c v w) :=
  ⟨(isUnit1_localChar' c w).1.comp (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))),
    fun x => (isUnit1_localChar' c w).2 _⟩

theorem norm_nsg (F E : Type) [Field F] [CommRing E] [Algebra F E] (a : F) :
    ‖GL2LocalData.nsg (F := F) E a‖ = 1 := by
  unfold GL2LocalData.nsg
  split_ifs <;> simp

theorem norm_W_central (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl} (m : LM c v)
    (hok : m.ok) (z : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)) :
    ‖m.W (dg2 z z * g)‖ = ‖m.W g‖ := by
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    have h := GlobalTheory.CompanionTheory.SplitCentre.sCen (Qv v) _ hχc hχ1 _ _ (isUnit1_cAt' c v w₁) (isUnit1_cAt' c v w₂)
      Φ ⟨hok.2.1, hok.2.2⟩ z g
    show ‖GL2LocalData.WcS _ _ _ _ _‖ = ‖GL2LocalData.WcS _ _ _ _ _‖
    rw [h, norm_mul, Units.val_mul, norm_mul, (isUnit1_cAt' c v w₁).2, (isUnit1_cAt' c v w₂).2]
    simp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, hΦ⟩ := hok
    have h := GlobalTheory.CompanionTheory.WeilCentral.wCen (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη (localChar c w) Φ hΦ z g
    have hn : ‖(((GL2LocalData.resF (F := Qv v) (localChar c w) * η) z : ℂˣ) : ℂ)‖ = 1 := by
      rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hη, norm_nsg, mul_one]
      exact (isUnit1_localChar' c w).2 _
    show ‖GL2LocalData.WcE _ _ _ _ _ Φ _‖ = ‖GL2LocalData.WcE _ _ _ _ _ Φ _‖
    rw [h, norm_mul, hn, one_mul]

theorem main : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok →
  ∀ (x : Qv v) (y z : (Qv v)ˣ) (k : GL (Fin 2) (Qv v)),
    ‖m.W (uni2 x * dg2 y 1 * dg2 z z * k)‖ = ‖m.W (dg2 y 1 * k)‖ := by
  intro K _ _ h2 c v m hok x y z k
  have e : uni2 x * dg2 y 1 * dg2 z z * k = uni2 x * (dg2 z z * (dg2 y 1 * k)) := by
    rw [mul_assoc (uni2 x), GlobalTheory.CompanionTheory.GL2Factorization.PT.diagonal_mul_diagonal_alt, mul_assoc (uni2 x), ← mul_assoc (dg2 z z),
      GlobalTheory.CompanionTheory.GL2Factorization.PT.diagonal_mul_diagonal_alt]
    simp [mul_comm]
  rw [e, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.local_whittaker_unipotent_character h2 m hok, norm_mul, Circle.norm_coe, one_mul]
  exact norm_W_central h2 m hok z _

end GlobalTheory.CompanionTheory.LocalWhittakerNorm
