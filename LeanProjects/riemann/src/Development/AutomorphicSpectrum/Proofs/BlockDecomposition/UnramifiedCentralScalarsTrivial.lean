import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSphericalNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedUnramifiedHypothesis
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem mem_unitFiltrationUnits_zero_of_mem_unQ {v : Pl} {a : (Qv v)ˣ} (ha : a ∈ unQ v) :
    a ∈ unitFiltrationUnits (Qv v) 0 := by
  rw [mem_unitFiltrationUnits_zero_iff]
  obtain ⟨h1, h2⟩ := ha
  have h1' : ValuativeRel.valuation (Qv v) (a : Qv v) ≤ 1 := h1
  have h2' : ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) ≤ 1 := h2
  refine le_antisymm h1' ?_
  have h3 : ValuativeRel.valuation (Qv v) (a : Qv v) *
      ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) = 1 := by
    rw [← map_mul]; simp
  calc (1 : _) = ValuativeRel.valuation (Qv v) (a : Qv v) *
        ValuativeRel.valuation (Qv v) ((a⁻¹ : (Qv v)ˣ) : Qv v) := h3.symm
    _ ≤ ValuativeRel.valuation (Qv v) (a : Qv v) * 1 := by gcongr
    _ = _ := mul_one _

theorem central_scalars_trivial_on_units : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), Unr c v → m.ok →
      ∀ a ∈ unQ v, omW m a = 1 ∧ om0 m a = 1 := by
  intro K _ _ h2 c v m hU hok a ha
  have hu0 := mem_unitFiltrationUnits_zero_of_mem_unQ ha
  rcases m with @⟨w₁, w₂, i₁, i₂, Φ⟩ | @⟨w, i, σ, η, Φ⟩
  · haveI := i₁
    haveI := i₂
    have r₁ : cAt c v w₁ a = 1 := MonoidHom.mem_ker.1
      (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1 hu0)
    have r₂ : cAt c v w₂ a = 1 := MonoidHom.mem_ker.1
      (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1 hu0)
    simp [omW, om0, r₁, r₂]
  · haveI := i
    obtain ⟨hu, hσ, hη, -⟩ := hok
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, hχ0⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K h2 v (fun w _ => (hU w).2) with
      ⟨x, y, hx, hy, hxy⟩ | ⟨w', hw', -, hf, hord⟩
    · exact absurd ((hu x hx).trans (hu y hy).symm) hxy
    obtain rfl : w' = w := hu w' hw'
    have hres : residueCard (Kv K w') = residueCard (Qv v) ^ 2 := GlobalTheory.CompanionTheory.NormGauss.card_E hf hord
    have hcont : Continuous (algebraMap (Qv v) (Kv K w')) := continuous_adicCompletionMap v w'
    obtain ⟨t, ht⟩ := GlobalTheory.CompanionTheory.UnitNormUnr.normU (Qv v) _ hχc hχ1 (Kv K w') hf hcont σ hσ η hη hres
      a ha.1 ha.2
    have hna : GL2LocalData.nsg (Kv K w') (a : Qv v) = 1 := if_pos ⟨t, ht⟩
    have hη1 : η a = 1 := Units.ext (by rw [hη a, hna]; rfl)
    have hr : GL2LocalData.resF (F := Qv v) (localChar c w') a = 1 := MonoidHom.mem_ker.1
      (GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w') (localChar c w') (hU w').1 hu0)
    simp [omW, om0, hη1, hr]

end GlobalTheory.CompanionTheory.CenTheta
