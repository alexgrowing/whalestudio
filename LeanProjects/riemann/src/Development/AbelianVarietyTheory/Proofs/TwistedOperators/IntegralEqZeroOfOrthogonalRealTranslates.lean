import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapRealTranslateEqRightTranslationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodIntegrableBoundedByProductOfNormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransOrth

theorem integral_eq_zero_of_translates : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D),
    IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) →
    ∀ w : SmT M, w ≠ 0 → (∀ h ∈ GinfC V, ∫ g in v.𝓕, F g * t w (g * h) ∂v.μ = 0) →
    ∀ w' : SmT M, ∫ g in v.𝓕, F g * t w' g ∂v.μ = 0 := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb w hw hh w'
  classical
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  obtain ⟨hint, K, hK⟩ := GlobalTheory.T.period_integrable_bounded_by_product_of_norms hP hV D θ hθ V S M J χ t ht v F hF hFb
  let ℓ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∫ g in v.𝓕, F g * t x g ∂v.μ
      map_add' := fun x y => by
        simp only [map_add, Pi.add_apply, mul_add]
        exact integral_add (hint x) (hint y)
      map_smul' := fun r x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext g
        ring }
  have hℓ : ∀ x, ℓ x = ∫ g in v.𝓕, F g * t x g ∂v.μ := fun x => rfl
  let L : MultilinearMap ℂ (fun τ => M.sm τ) ℂ := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hL : ∀ u, L u = ℓ (PiTensorProduct.tprod ℂ u) := fun u => rfl
  have hx : w ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := fun τ => M.sm τ))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, c, gg, hg⟩ := Submodule.mem_span_set'.1 hx
  choose vv hvv using fun j => (gg j).2
  have hw' : w = ∑ j, c j • PiTensorProduct.tprod ℂ (vv j) := by
    rw [← hg]; simp [hvv]
  obtain ⟨φ, hφ⟩ : ∃ φ : M.Vec, GlobalTheory.tprodInnerFun φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (GlobalTheory.eq_zero_of_tprodInnerFun w hcon)
  have hφ' : (∑ j, c j * ∏ τ, ⟪((φ τ : M.sm τ) : M.H τ), (vv j τ : M.H τ)⟫_ℂ) ≠ 0 := by
    rw [hw'] at hφ
    simpa [map_sum, GlobalTheory.tprodInnerFun_tprod, Submodule.coe_inner] using hφ
  have hinv : ∀ τ (g : Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ), ∀ x ∈ M.sm τ, Formalism.IndefR.SchurOrthogonalityAlt.piR M τ g x ∈ M.sm τ :=
    fun τ g x hx => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem g) x hx
  have htv : ∀ (u : M.Vec) x, (PiTensorProduct.lift.symm t : MMap M) u x = t (PiTensorProduct.tprod ℂ u) x := by
    intro u x; simp [PiTensorProduct.lift_symm]
  have hT : ∀ gs : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ,
      ∑ j, c j * L (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩) = 0 := by
    intro gs
    obtain ⟨P, hPm, hPe⟩ := GlobalTheory.T.multiplicityMap_realTranslate_eq_rightTranslation θ M J χ (PiTensorProduct.lift.symm t) ((mem_multT θ M J χ t).1 ht) gs
    have h0 := hh P hPm
    have e : ∀ x, F x * t w (x * P) = ∑ j, c j * (F x * t (PiTensorProduct.tprod ℂ
        (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩)) x) := by
      intro x
      rw [hw']
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := hPe (vv j) x
      rw [htv, htv] at e1
      simp only [Formalism.IndefR.SchurOrthogonalityAlt.piR_apply]
      rw [← e1]
      ring
    simp_rw [e] at h0
    rw [integral_finset_sum _ (fun j _ => (hint _).const_mul (c j))] at h0
    simp_rw [integral_const_mul] at h0
    exact h0
  have hB := GlobalTheory.T.multilinear_zero_of_kills_translates_tensor D.what₂.Tau (fun τ => M.H τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.piR M τ) (Formalism.IndefR.SchurOrthogonalityAlt.piR_norm M)
    (Formalism.IndefR.SchurOrthogonalityAlt.commutant_scalar M) (fun τ => M.sm τ) (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M) hinv L K
    (fun u => by rw [hL, hℓ]; exact hK u) n c vv hT (fun τ => (φ τ : M.H τ))
  have hL0 : ∀ u, L u = 0 := fun u => (mul_eq_zero.1 (hB u)).resolve_left hφ'
  have hℓ0 : ℓ w' = 0 := by
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod r u => rw [map_smul, ← hL, hL0, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  rw [← hℓ]; exact hℓ0

end GlobalTheory.TransOrth
