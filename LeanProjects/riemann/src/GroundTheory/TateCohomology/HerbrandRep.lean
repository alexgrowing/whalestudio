import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom

theorem repSubOne_apply (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl

variable [Fintype G]

def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom

noncomputable def repHerbrandQuotient (A : Rep.{w} k G) (σ : G) : ℚ :=
  herbrandQuotient (repSubOne A σ) (repNorm A)

def RepHasHerbrandQuotient (A : Rep.{w} k G) (σ : G) : Prop :=
  HasHerbrandQuotient (repSubOne A σ) (repNorm A)

end GroundTheory.GroupCoh
