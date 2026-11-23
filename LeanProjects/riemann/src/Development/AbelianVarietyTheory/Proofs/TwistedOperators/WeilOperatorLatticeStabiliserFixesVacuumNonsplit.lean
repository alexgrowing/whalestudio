import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInvInert

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem idem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβα : ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → β * α = α := by
    intro α hα
    apply RestrictedProduct.ext
    intro w
    show β w * α w = α w
    by_cases hw : w = v
    · subst hw
      have : β w = 1 := h1
      rw [this, one_mul]
    · have : α w = 0 := hα w hw
      rw [this, mul_zero]
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
      obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
      funext i j
      show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * _ = _
      rw [Algebra.TensorProduct.algebraMap_apply]
      simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      show ((0 * 0, β * α) : AF D.host.F) = (0, α)
      rw [mul_zero, hβα α hα]
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

theorem mem_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u := by
  constructor
  · intro hu
    exact ⟨GlobalTheory.PlaceModel.latO_le_top _ hu, idem_smul_eq hε hu⟩
  · rintro ⟨hu, he⟩
    have := GlobalTheory.PlaceModel.placeIdem_smul_mem hε hu
    rwa [he] at this

theorem act_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) := by
  intro x y hxy
  unfold actO at hxy
  have hT : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  have hS : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one]
  calc x = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * x * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * x * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.L2.Theta.mt T h⁻¹ * (Formalism.L2.Theta.mt T h * y * Formalism.L2.Theta.mt S g⁻¹) * Formalism.L2.Theta.mt S g := by
        rw [hxy]
    _ = (Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h) * y * (Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g) := by
        simp only [Matrix.mul_assoc]
    _ = y := by
        rw [hT, hS, Matrix.one_mul, Matrix.mul_one]

theorem om_fixes_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT hη v ε hns hχS hχT g h hg hh hlat f hf hvac
  have hε : IsPlaceIdem D v ε := hns.1
  have key := GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T ΛS ΛT hS hT χS χT om hη hW v ε hns hχS hχT
  have hc : ∀ (c : AE D) (x : WO S T), actO S T g h (c • x) = c • actO S T g h x := by
    intro c x
    unfold actO
    rw [Matrix.mul_smul, Matrix.smul_mul]
  refine key g h hg hh ?_ f hf ?_
  · intro u
    rw [mem_place_iff hε, mem_place_iff hε]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hlat u).1 h1, by rw [← hc, h2]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(hlat u).2 h1, ?_⟩
      apply act_injective g h
      rw [hc]
      exact h2
  · intro u hu
    obtain ⟨a, ha, h2a⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hns
    have hu' := (mem_place_iff hε u).1 hu
    have hau := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu'.1
    have e2 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, h2a]
      exact hu'.2
    have := hvac.1 (a • u) hau
    rwa [e2] at this

end GlobalTheory.VecInvInert

end
