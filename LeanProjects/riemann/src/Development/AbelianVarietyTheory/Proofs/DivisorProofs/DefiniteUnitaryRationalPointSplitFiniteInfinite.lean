import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatSplit

theorem ratU_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n,
    ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧
      ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  intro E _ _ _ n γ hγ
  obtain ⟨g0, hg0⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈ (ratGL E n).range)
  have hval : γ.1.val = g0.val.map (algebraMap E (Ad E)) := by rw [← hg0]; rfl

  have hU : g0 ∈ UE E n := by
    have h2 : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
    show cT (IsCMField.complexConj E).toRingEquiv.toRingHom g0.val * 1 * g0.val = 1
    have hinj : Function.Injective (algebraMap E (Ad E)) := by
      intro x y hxy
      have τ := (Classical.arbitrary (InfinitePlace E)).embedding
      exact τ.injective (by rw [← coord_algebraMap τ x, ← coord_algebraMap τ y, hxy])
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul,
      FinPtLoc.map_cT (algebraMap E (Ad E)) _ (conjAd E) (fun x => (conjAd_algebraMap x).symm),
      Matrix.map_one _ (map_zero _) (map_one _), ← hval, h2]
  refine ⟨⟨g0, hU⟩, ?_, ?_⟩
  · set a : finU E n := finPt ⟨g0, hU⟩ with ha
    have haval : ((a : UA E n) : GA E n) = finGL E n (ratF E n g0) := by
      rw [ha, FinPtLoc.finPt_eq]
    have hb : (a : UA E n)⁻¹ * γ ∈ infU E n := by
      show GeneralLinearGroup.map (pFin E) (((a : UA E n)⁻¹ * γ : UA E n) : GA E n) = 1
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, haval, pFin_finGL, ← hg0]
      have : GeneralLinearGroup.map (pFin E) (ratGL E n g0) = ratF E n g0 := by
        apply Units.ext; ext i j; rfl
      rw [this, inv_mul_cancel]
    have hγs : γ = (a : UA E n) * ((⟨_, hb⟩ : infU E n) : UA E n) := by
      simp
    rw [hγs, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (γ.1.val i j)) = v.embedding (g0.val i j)
    rw [hval, Matrix.map_apply, coord_algebraMap]

end GlobalTheory.BCT.RatSplit
