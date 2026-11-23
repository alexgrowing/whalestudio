import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocal
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem modelzero_upper : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ g hg u
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 := by
    rw [Matrix.det_fin_two, hg]; ring
  have hdet0 : (g.val).det ≠ 0 := by
    have := g.isUnit.map (Matrix.detMonoidHom (n := Fin 2) (R := F))
    exact this.ne_zero
  have hA : g.val 0 0 ≠ 0 := fun h => hdet0 (by rw [hdet, h, zero_mul])
  have hD : g.val 1 1 ≠ 0 := fun h => hdet0 (by rw [hdet, h, mul_zero])
  have hu : (u : F) ≠ 0 := u.ne_zero
  set A := g.val 0 0 with hAdef
  set B := g.val 0 1 with hBdef
  set D := g.val 1 1 with hDdef
  have hc : (u : F) * D ≠ 0 := mul_ne_zero hu hD

  have hinn : GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u =
      ((modulus ((u : F) * D) : ℝ))⁻¹ * ((χ (B / D) : ℂ) * Φ ((u : F) * A, ((u : F) * D)⁻¹)) := by
    set G : F → ℂ := fun y' => GlobalTheory.CompanionTheory.WS.pF χ Φ ((u : F) * A, y') * (χ (-(y' / ((u : F) * D)) + B / D) : ℂ) with hG
    have h1 : GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u =
        ∫ y, (fun y => G (((u : F) * D) * y)) (y + B / D) ∂selfDualMeasure χ := by
      unfold GlobalTheory.CompanionTheory.WS.inn
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [Function.comp, GlobalTheory.CompanionTheory.WS.rowAct, hG, hg]
      have e1 : (u : F) * A + (u : F) * y * 0 = (u : F) * A := by ring
      have e2 : (u : F) * B + (u : F) * y * D = (u : F) * D * (y + B / D) := by
        field_simp
        ring
      have e3 : -((u : F) * D * (y + B / D) / ((u : F) * D)) + B / D = -y := by
        field_simp
        ring
      rw [e1, e2, e3]
    rw [h1, integral_add_right_eq_self (fun y => G (((u : F) * D) * y)) (B / D),
      GroundTheory.LocalField.integral_comp_mul_left _ hc G]
    have h2 : ∫ y, G y ∂selfDualMeasure χ = (χ (B / D) : ℂ) * Φ ((u : F) * A, ((u : F) * D)⁻¹) := by
      have h3 := GlobalTheory.CompanionTheory.WcSplit.integral_phiW hχ hΦ.1 hΦ.2 ((u : F) * A) (((u : F) * D)⁻¹)
      rw [← h3, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hG]
      have e4 : -(y / ((u : F) * D)) + B / D = B / D + -(y * ((u : F) * D)⁻¹) := by
        rw [div_eq_mul_inv y]; ring
      rw [e4, AddChar.map_add_eq_mul, Circle.coe_mul]
      have e7 : GlobalTheory.CompanionTheory.WS.pF χ Φ ((u : F) * A, y) = GlobalTheory.CompanionTheory.WcSplit.phiW χ Φ ![(u : F) * A, y] := by
        rw [GlobalTheory.CompanionTheory.WcSplit.phiW_pair]
        unfold GlobalTheory.CompanionTheory.WS.pF localFourier
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [mul_comm y t]
      rw [e7]
      ring
    rw [h2]
    simp [Complex.real_smul]
  rw [hinn]
  have hmod : ((modulus ((u : F) * D) : ℝ)) = (modulus (u : F) : ℝ) * (modulus D : ℝ) := by
    rw [modulus_mul]; push_cast; rfl
  have hmu : (modulus (u : F) : ℝ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hu
  have hmD : (modulus D : ℝ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hD
  have ha' : A / (g.val).det = D⁻¹ := by
    rw [hdet]; field_simp
  have hz : (0 : F) / (g.val).det = 0 := zero_div _
  unfold GL2LocalData.rW
  rw [hg, hz, if_pos rfl, ha', GlobalTheory.CompanionTheory.WcSplit.nsg_pair (inv_ne_zero hD), GlobalTheory.CompanionTheory.WcSplit.norm_pair]
  have e5 : D⁻¹ * B * ((u : F) * ((u⁻¹ : Fˣ) : F)) = B / D := by
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have e6 : (algebraMap F (F × F) D⁻¹ * ((u : F), ((u⁻¹ : Fˣ) : F))) * ((g.val).det, 1) =
      ((u : F) * A, ((u : F) * D)⁻¹) := by
    rw [hdet]
    ext
    · simp
      field_simp
    · simp
  simp only [e5, e6]
  have hmp : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by
    simp [mp]
  rw [hmp, hmod, modulus_inv]
  have hmuC : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmu
  have hmDC : ((modulus D : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmD
  push_cast
  field_simp

end GlobalTheory.CompanionTheory.WS
