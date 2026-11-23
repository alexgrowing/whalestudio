import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizerStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem inf_subgroupOf_of_le' {G : Type} [Group G] {Γ P H : Subgroup G} (h : H ≤ P) :
    (Γ ⊓ P).subgroupOf H = Γ.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩

theorem semiLat_frameGrp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 →
      ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})),
        SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤)
          ν π DN DM := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW ν DN hν hDN h1
  obtain ⟨π, DM, hπ, hDM⟩ := GlobalTheory.StdPar.exists_haar_leviOne (X := X) (Y := Y) {Fin.last r} h hJ hW
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y h hJ hW
  have hN : unipRad σ J X ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun u hu => ⟨1, trivial, f3 u hu⟩
  have hM : GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun m hm => by
    obtain ⟨β, e, -⟩ := f4 m hm
    exact ⟨β, trivial, e⟩
  refine ⟨π, DM,
    { closedN := (GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one F E σ n J r X Y h hJ hW).1
      closedM := f7
      norm := fun m hm => f1 m (f6 hm)
      disj := fun g hg hg' => f2 g hg (f6 hg')
      dec := ?_
      haarN := hν
      haarM := hπ
      domN := by rw [inf_subgroupOf_of_le' hN]; exact hDN
      domM := by rw [inf_subgroupOf_of_le' hM]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer F E σ n J r X Y h hJ hW π DM hπ hDM }⟩
  rintro γ ⟨hγ, β, -, e⟩
  obtain ⟨u, hu, m, -, hp, -, hr, ho⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y h hJ hW γ β e
  have hm := ho (f5 γ hγ β e)
  refine ⟨u, hu, m, hm, ⟨?_, hN hu⟩, ⟨hr hγ, hM hm⟩, hp⟩
  have : u = γ * m⁻¹ := by rw [hp, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.ResidueEisenstein
