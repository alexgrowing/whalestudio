import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import GroundTheory.AutomorphicForms.AdelicGLn
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory

theorem isOfFinOrder_of_conj_mem_ratU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)),
    IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  intro E _ _ _ n D hD g c hc hgc
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hcl : IsClosed (((ratGL E n).range : Subgroup (GA E n)) : Set (GA E n)) := Subgroup.isClosed_of_discrete
  let K : Set (GA E n) := (fun x : UA E n => ((g * x * g⁻¹ : UA E n) : GA E n)) '' (D : Set (UA E n))
  have hK : IsCompact K := hD.image (continuous_subtype_val.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hKG : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right hcl
  let t : Set (ratGL E n).range := {x | (x : GA E n) ∈ K}
  have himg : Subtype.val '' t = K ∩ ((ratGL E n).range : Set (GA E n)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
  have ht : IsCompact t := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
  have hfin : (K ∩ ((ratGL E n).range : Set (GA E n))).Finite := by
    rw [← himg]; exact (ht.finite_of_discrete).image _
  by_contra hno
  have hinj := (injective_pow_iff_not_isOfFinOrder).2 hno
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((g * c ^ k * g⁻¹ : UA E n) : GA E n)) ?_ ?_ hfin
  · intro i j hij
    apply hinj
    have h1 : g * c ^ i * g⁻¹ = g * c ^ j * g⁻¹ := Subtype.ext hij
    simpa using h1
  · intro k
    refine ⟨⟨c ^ k, D.pow_mem hc k, rfl⟩, ?_⟩
    have hk : g * c ^ k * g⁻¹ ∈ ratU E n := by
      have := (ratU E n).pow_mem hgc k
      simpa [conj_pow] using this
    exact (Subgroup.mem_subgroupOf).1 hk

end GlobalTheory
