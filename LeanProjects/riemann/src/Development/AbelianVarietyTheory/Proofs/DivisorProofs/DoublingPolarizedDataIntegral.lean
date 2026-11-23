import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairGlobalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

namespace GlobalTheory.DblDatum

theorem exists_doubled_datum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ →
    ∃ Φ ∈ schA F (Fin n × Fin (d + d)),
      FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K₂, Ψ = om₂ (1, k) Φ}) ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ x h h', theta om Φ₁ x h * starRingEnd ℂ (theta om Φ₂ x h') =
        c * (theta om₂ Φ x (i (h, h')) * chiInv χX h') := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP Φ₁ hΦ₁ Φ₂ hΦ₂ W₂ hJ hL hθ i hi co hrat hdiag hanti om₂ hom₂ K₂ hK₂
  obtain ⟨e, c, hc, hbij, hadm, hheis, hth⟩ := GlobalTheory.T.doubled_darboux_coordinates F E σ B hP.base n d Xs.J W.J W₂.J hJ M.co hP.good.rat co hrat
  have hpres : ∀ p, ∀ φ ∈ schA F (Fin n × Fin d), om p φ ∈ schA F (Fin n × Fin d) :=
    (IsUWeilPair.isUSplitting hP.weil).pres
  have hsch : ∀ Φ ∈ PolData B M, Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ =>
    GlobalTheory.ThKRatInv.polData_le_schA B M hP.good hΦ
  have hstar : ∀ C ∈ schA F (Fin n × Fin d), (fun x => star (C x)) ∈ schA F (Fin n × Fin d) :=
    fun C hC => GlobalTheory.ConjSch.star_mem_schA _ C hC
  have hbox : ∀ A ∈ schA F (Fin n × Fin d), ∀ C ∈ schA F (Fin n × Fin d),
      boxC A C ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d) := fun A hA C hC =>
    GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F _ _ A hA _ (hstar C hC)
  have hthbox : ∀ A ∈ schA F (Fin n × Fin d), ∀ C ∈ schA F (Fin n × Fin d),
      thetaSum F (boxC A C) = thetaSum F A * star (thetaSum F C) := fun A hA C hC => by
    rw [boxC, GlobalTheory.ThetaBox.thetaSum_boxFun F _ _ A hA _ (hstar C hC)]
    congr 1
    unfold thetaSum
    exact tsum_star.symm
  have hS₁ := hsch Φ₁ hΦ₁
  have hS₂ := hsch Φ₂ hΦ₂
  have hA := GlobalTheory.T.doubling_pair_lattice_theta F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co hrat hdiag hanti om₂ hom₂ e hbij hadm hheis
  have hB := GlobalTheory.T.doubling_pair_lattice_measure F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co hrat hdiag hanti om₂ hom₂ e hbij hadm hheis
  have hC := GlobalTheory.T.doubling_pair_local_integral F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co hrat hdiag hanti om₂ hom₂ e hbij hadm hheis
  have hD := GlobalTheory.T.doubling_pair_global_integral F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ hL hθ i hi co hrat hdiag hanti om₂ hom₂ e hbij hadm hheis
  refine ⟨e (boxC Φ₁ Φ₂), hbij.mapsTo (hbox _ hS₁ _ hS₂), hD K₂ hK₂ Φ₁ hΦ₁ Φ₂ hΦ₂, c⁻¹, inv_ne_zero hc, fun x h h' => ?_⟩
  set α : ℂ := ((χX (Matrix.GeneralLinearGroup.det h'.1) : Circle) : ℂ) with hαdef
  have hα : α ≠ 0 := Circle.coe_ne_zero _
  have homx : ∀ (g : UA σ W.J) (φ : (Fin n × Fin d → AF F) → ℂ), om (x, 1) (om (1, g) φ) = om (x, g) φ := by
    intro g φ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hkey : om₂ (x, i (h, h')) (e (boxC Φ₁ Φ₂)) = α • e (boxC (om (x, h) Φ₁) (om (x, h') Φ₂)) := by
    have hsplit : ((x, i (h, h')) : UA σ Xs.J × UA σ W₂.J) = (x, 1) * ((1, i (h, 1)) * (1, i (1, h'))) := by
      rw [Prod.mk_mul_mk, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk]
      simp
    rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hC h' Φ₁ hS₁ Φ₂ hS₂, map_smul, map_smul,
      hB h Φ₁ hS₁ _ (hpres _ _ hS₂), hA x _ (hpres _ _ hS₁) _ (hpres _ _ hS₂), homx, homx]
  have hth₂ : theta om₂ (e (boxC Φ₁ Φ₂)) x (i (h, h')) = α * (c * thetaSum F (boxC (om (x, h) Φ₁) (om (x, h') Φ₂))) := by
    rw [theta, hkey, GlobalTheory.WeilM.thetaSum_smul, hth _ (hbox _ (hpres _ _ hS₁) _ (hpres _ _ hS₂))]
  have hchi : chiInv χX h' = α⁻¹ := by
    simp only [chiInv, hαdef, Circle.coe_inv]
  rw [hth₂, hchi, theta, theta, starRingEnd_apply, ← hthbox _ (hpres _ _ hS₁) _ (hpres _ _ hS₂)]
  field_simp

end GlobalTheory.DblDatum
