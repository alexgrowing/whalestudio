import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem det_mem_Uo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {g : Matrix.GeneralLinearGroup Unit k} (hg : g ∈ KO k Unit) :
    Matrix.GeneralLinearGroup.det g ∈ UpperTheory.V.Hi.Uo k := by
  obtain ⟨h, rfl⟩ := hg
  show valuation k ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h) : kˣ) : k) = 1
  rw [Matrix.GeneralLinearGroup.map_det]
  exact (Valuation.integer.integers (valuation k)).valuation_unit _

theorem UpperTheory.V.Z.Sym.Al.locSph :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) → ∃ v, v ≠ 0 ∧ ∀ u ∈ KO k (Fin n), prinSeries ψ u v = v := by
  intro k _ _ _ _ n ψ hψ
  have key : ∀ g : Levi k (fun _ : Fin n => Unit), (∀ a, g a ∈ KO k Unit) →
      (MonoidHom.comp (ofChar (torusChar ψ)) (leviTorus k (Fin n)).symm.toMonoidHom) g (1 : ℂ) = 1 := by
    intro g hg
    have hs : (leviTorus k (Fin n)).symm g = fun i => Matrix.GeneralLinearGroup.det (g i) := rfl
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofChar_apply, hs, torusChar_apply]
    rw [Finset.prod_eq_one fun i _ => hψ i _ (det_mem_Uo k (hg i))]
    simp
  obtain ⟨f, hf, h1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (points (Fin n)) key
  refine ⟨f, ?_, fun u hu => GlobalTheory.LGrp.mem_fixed.mp hf u hu⟩
  rintro rfl
  simp at h1
