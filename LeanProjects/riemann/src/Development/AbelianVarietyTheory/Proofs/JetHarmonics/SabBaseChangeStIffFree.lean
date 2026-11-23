import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.PullbackGroupAction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabPullCompare

variable {S S' : Scheme.{0}}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def FreeConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L)),
    Nonempty (SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f)

def PinnedConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L))
    (m : SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f),
    m.φ = pullback.fst t.G.hom f

theorem lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

end GlobalTheory.SabPullCompare
