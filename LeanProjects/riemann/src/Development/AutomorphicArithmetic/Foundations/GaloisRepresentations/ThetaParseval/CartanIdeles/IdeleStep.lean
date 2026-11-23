import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.ideleStep :
    UpperTheory.Gal.TP.Skew.ConjAut → UpperTheory.Gal.TP.Skew.IdeleStep := by
  intro hconj F E _ _ _ _ _ σ hcm a
  obtain ⟨hgal, s, -, -, hss, hall, -⟩ := hconj F E σ hcm
  haveI := hgal
  haveI hcomm : IsMulCommutative Gal(E/F) := ⟨⟨fun g h => by
    rcases hall g with rfl | rfl <;> rcases hall h with rfl | rfl <;> simp⟩⟩
  obtain ⟨hFr, hEc, -, -⟩ := hcm
  let v : InfinitePlace F := Classical.arbitrary _
  have hram : infiniteLocalSymbol E v ≠ 1 := by
    rw [Ne, infiniteLocalSymbol_eq_one_iff]
    intro hun
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
    have hw' : w.comap (algebraMap F E) = v := hw
    refine InfinitePlace.not_isUnramified_iff.mpr ⟨hEc.isComplex w, ?_⟩ (hun w hw')
    rw [hw']
    exact hFr.isReal v
  obtain ⟨c, hc⟩ : ∃ c, infiniteLocalSymbol E v c ≠ 1 := by
    by_contra h
    push_neg at h
    exact hram (MonoidHom.ext h)
  have hc' : infiniteLocalSymbol E v c = s := (hall _).resolve_left hc
  have key : ∀ a' : IdeleGroup F, ideleSymbol F E a' = 1 →
      ∃ x b, ∀ w, ord w a' = ord w (diagonal F x) + ord w (ideleNorm F E b) := by
    intro a' ha'
    have hmem : a' ∈ (ideleSymbol F E).ker := ha'
    rw [ker_ideleSymbol, Subgroup.mem_sup] at hmem
    obtain ⟨y, ⟨x, rfl⟩, z, ⟨b, rfl⟩, rfl⟩ := hmem
    exact ⟨x, b, fun w => ord_mul w _ _⟩
  by_cases ha : ideleSymbol F E a = 1
  · exact key a ha
  · obtain ⟨x, b, hxb⟩ := key (a * infiniteEmbedding v c) (by
      rw [map_mul, (hall _).resolve_left ha, ideleSymbol_infiniteEmbedding, hc', hss])
    refine ⟨x, b, fun w => ?_⟩
    rw [← hxb w, ord_mul,
      mem_standardOpenSubgroup_iff_ord.mp (infiniteEmbedding_mem_standardOpenSubgroup v c) w,
      add_zero]
