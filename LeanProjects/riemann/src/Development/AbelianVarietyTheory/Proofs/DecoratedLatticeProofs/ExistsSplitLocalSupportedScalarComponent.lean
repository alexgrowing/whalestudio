import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocScalar

theorem place_ι_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have hx : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]
  have := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at this
  rw [this, ← mul_assoc, hx]

theorem place_ι_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have := p.ι_π 1
  rwa [map_one, mul_one] at this

theorem place_π_e {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  rw [← place_ι_one, p.π_ι]

theorem exists_isLoc_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  intro D k _ _ _ _ p V Z _ _ F c zk hzk
  have he := p.split
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv V)
    (GlobalTheory.SplitOnto.gram_conj V) he.1 he.2.1 (p.ι (c : k) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (p.ι ((c⁻¹ : kˣ) : k) • 1) (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul (p.ι _), ← place_ι_mul, Units.inv_mul, place_ι_one, smul_smul, he.1])
  let z : GA D V := ⟨g, h1⟩
  refine ⟨z, fun i j => congrFun (congrFun h2 i) j, ?_⟩
  rw [hzk, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, F.βγ]
  ext i j
  have := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  change p.π (g.1 i j) = _
  rw [← one_mul (p.π (g.1 i j)), ← place_π_e p, ← map_mul, this, map_mul, place_π_e, one_mul]
  by_cases hij : i = j
  · subst hij; simp [p.π_ι]
  · simp [hij]

end GlobalTheory.LocScalar
