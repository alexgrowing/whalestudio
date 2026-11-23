import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsFnDegRelDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

section Relabel

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}

def blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) : Σ k, ι' (κ k) :=
  ⟨p.1, cast (congrArg ι' (hb.2.2.1 p)) (v p).2⟩

theorem blockIncl_blockVar (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    blockIncl ⟨κ, hb.1⟩ ι' (blockVar hb p) = v p := by
  refine Sigma.ext (hb.2.2.1 p).symm ?_
  exact (cast_heq _ _)

def blockVarEquiv (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (κ k)) :=
  Equiv.ofBijective (blockVar hb) (by
    have hI : Function.Injective (blockIncl ⟨κ, hb.1⟩ ι') := by
      rintro ⟨a, x⟩ ⟨b, y⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
      cases hb.1 h1
      cases eq_of_heq h2
      rfl
    refine ⟨fun p q h => hb.2.1 ?_, fun ⟨k, a⟩ => ?_⟩
    · rw [← blockIncl_blockVar hb p, ← blockIncl_blockVar hb q, h]
    · obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
      exact ⟨p, hI ((blockIncl_blockVar hb p).trans hp)⟩)

theorem imageVar_eq_comap {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by
  ext f
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar contractPrime
  simp only [Ideal.mem_comap]
  have hfun : (blockIncl ⟨κ, hb.1⟩ ι' ∘ blockVarEquiv hb) = v := funext (blockIncl_blockVar hb)
  have e : rename (blockIncl ⟨κ, hb.1⟩ ι') (rename (blockVarEquiv hb) f) = rename v f := by
    rw [rename_rename, hfun]
  exact iff_of_eq (congrArg (· ∈ V') e.symm)

end Relabel

theorem ProjDeg.of_found (hPF : ProjectionFormulaDegree.Statement.{u})
    (hFn : FnDegRelDeg.Statement.{u}) {K K' : Type} [Fintype K] [Fintype K'] (F : Type u) [Field F]
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι' := by
  classical
  intro I I' hI hI' κ v V' e L i' hb hV' hV hc
  have hA' := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I' hI' V' e (fun j => ReciprocityTheory.ChartRestriction.G.AI.I1.pullDeg κ (L j)) hV'
  have hA := Numbers.agree_of IntNumBase.full CutRational.full ExistsForm.full
    DivCycleSupport.full I hI _ e L hV
  rw [hA', hA]
  set j : K ↪ K' := ⟨κ, hb.1⟩
  have hP' : IsMultiProjPrime V' := (Objects.isMultiProjPrime_iff V').mpr hV'.1
  have := hP'.isPrime
  have himg := imageVar_eq_comap (F := F) hb V'

  have hRen := RenameIntNum.full F K K (fun k => ι k) (fun k => ι' (κ k)) (Equiv.refl K)
    (blockVarEquiv hb) (fun _ => rfl) (contractPrime j V') e L
  have hdimP : relDim (contractPrime j V') = (e : WithBot (WithTop ℤ)) := by
    refine relDim_eq_of_ringKrullDim _ e ?_
    have eq : MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb)) ≃+*
        MRing (fun k => ι' (κ k)) F ⧸ contractPrime j V' :=
      Ideal.quotientEquiv _ _ (renameEquiv F (blockVarEquiv hb)).toRingEquiv
        (Ideal.map_comap_of_surjective _ (renameEquiv F (blockVarEquiv hb)).surjective _).symm
    have h2 : ringKrullDim (MRing ι F ⧸ (contractPrime j V').comap (rename (blockVarEquiv hb))) =
        ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← himg]
      exact hV.2
    exact (ringKrullDim_eq_of_ringEquiv eq).symm.trans h2
  obtain ⟨-, hPFe⟩ := hPF F K K' j ι' V' hP' e (relDim_eq_of_ringKrullDim V' e hV'.2) hdimP L
  have hfn := hFn F K K' ι ι' κ v hb V' hP' i' hc
  rw [himg, hRen, hfn]
  exact hPFe

end

end GroundTheory.Heights₂.Heights.Targets
