import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAveragePreservesType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAveragePreservesTypeStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
namespace GlobalTheory.AvgSamePlace
theorem isTypeAt_average_same_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  intro D θ hθ hPr N τ ψ _ hT e he
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  haveI : CompleteSpace H := hD.1
  have hfr : IsUnit (N.M.fr τ) := N.M.fr_unit τ
  have hfrJ := N.M.fr_gram τ
  have dfr := (isUnit_iff_isUnit_det _).1 hfr
  have dP := (isUnit_iff_isUnit_det _).1 hP
  have fr1 : (N.M.fr τ)⁻¹ * N.M.fr τ = 1 := Matrix.nonsing_inv_mul _ dfr
  have fr2 : N.M.fr τ * (N.M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ dfr
  have P1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ dP
  have P2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ dP
  set fr := N.M.fr τ with hfrdef
  set h := P * fr⁻¹ with hh
  set hi := fr * P⁻¹ with hhi
  have hih : hi * h = 1 := by
    calc hi * h = fr * (P⁻¹ * P) * fr⁻¹ := by simp only [hh, hhi, Matrix.mul_assoc]
      _ = 1 := by rw [P1, Matrix.mul_one, fr2]
  have hU : h ∈ UJset (N.M.ε τ) := by
    show hᴴ * Jm (N.M.ε τ) * h = Jm (N.M.ε τ)
    calc hᴴ * Jm (N.M.ε τ) * h = (fr⁻¹)ᴴ * (Pᴴ * Jm (N.M.ε τ) * P) * fr⁻¹ := by
          simp only [hh, conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          rw [hJ, ← hfrJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hiU : hi ∈ UJset (N.M.ε τ) := by
    show hiᴴ * Jm (N.M.ε τ) * hi = Jm (N.M.ε τ)
    calc hiᴴ * Jm (N.M.ε τ) * hi = (P⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * P⁻¹ := by
          simp only [hhi, conjTranspose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᴴ * Jm (N.M.ε τ) * (P * P⁻¹) := by
          rw [hfrJ, ← hJ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [P2]; simp
  set σ₂ : Mx N.V.rank → (H →L[ℂ] H) := fun y => σ (h * y * hi) with hσ₂def
  have hD₂ : IsDS (N.M.ε τ) (N.M.lam τ) σ₂ := GlobalTheory.CayleyChoice.isDS_conj hD hiU hU hih
  have hσ₂ : Std (N.M.ε τ) σ₂ := std_of_isDS hPr.harishChandraModules hD₂
  have e1 : ∀ g, σ (P * g * P⁻¹) = σ₂ (fr * g * fr⁻¹) := by
    intro g
    show σ (P * g * P⁻¹) = σ (h * (fr * g * fr⁻¹) * hi)
    congr 1
    calc P * g * P⁻¹ = P * (fr⁻¹ * fr) * g * (fr⁻¹ * fr) * P⁻¹ := by rw [fr1]; simp
      _ = _ := by simp only [hh, hhi, Matrix.mul_assoc]
  simp only [e1] at hx
  refine ⟨H, i1, i2, σ₂, N.M.lam τ, N.M.ε τ, fr, N.M.enum τ, hD₂, hfr, hfrJ, fun x => ?_⟩
  have hx' : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂ (GlobalTheory.SeriesToClosure.res θ N.V τ fr ψ x) :=
    hasTypeAll_transport _ H H _ σ₂ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr (GlobalTheory.LowTypeDetermined.isUnit_gram hfr hfrJ)
      hfr hfrJ (LinearIsometryEquiv.refl ℂ H) (fun _ _ _ => rfl) (fun g => ψ (x * atTau θ N.V τ g))
      (hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hW, hc, v, ℓ, C, hex⟩ := hx'
  have hmv := GlobalTheory.SeriesToClosure.moves_avg hθ hfr hfrJ hσ₂ he ψ x S v ℓ C hW hc hex
  have hy : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ₂
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x) :=
    ⟨S, hW, hc, _, ℓ, C, hmv⟩
  have hJ' : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfrJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [fr2]; simp
  have hfri : IsUnit fr⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hfr
  have hii : fr⁻¹⁻¹ = fr := Matrix.nonsing_inv_nonsing_inv _ dfr
  have hb := hasTypeAll_transport _ H H σ₂ (fun g => σ₂ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfri hJ' (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ₂ g w = σ₂ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [hii]
      congr 2
      calc g = (fr * fr⁻¹) * g * (fr * fr⁻¹) := by rw [fr2]; simp
        _ = _ := by simp only [Matrix.mul_assoc]) _ hy
  have ef : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ) x
      (fr⁻¹⁻¹ * y * fr⁻¹)) = fun g => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) fr e ψ (x * atTau θ N.V τ g) := by
    funext y
    simp only [GlobalTheory.SeriesToClosure.res]
    congr 3
    rw [hii]
    calc fr⁻¹ * (fr * y * fr⁻¹) * fr = (fr⁻¹ * fr) * y * (fr⁻¹ * fr) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [fr1]; simp
  rw [ef] at hb
  exact hasTypeAll_iff.1 hb
end GlobalTheory.AvgSamePlace
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_isTypeAt_same_place_twist : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @_root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | exact _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place | (intros; apply _root_.GlobalTheory.AvgSamePlace.isTypeAt_average_same_place <;> assumption)
end
