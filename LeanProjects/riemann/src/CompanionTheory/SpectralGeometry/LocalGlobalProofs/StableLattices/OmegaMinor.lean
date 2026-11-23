import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEqualityStatement

open Finset

namespace GlobalTheory.CompanionTheory.HeckeCapelli

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)

theorem capelli_entry_apply {n : ℕ} (X : GMod n) (x : ℂ) (d b : Fin n) (v : X.V) :
    capEntry X.E x d b v = X.E d b v + if d = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem capelli_component {m : ℕ} (X : GMod (m + 1)) (x : ℂ) (f : Fin (m + 1) → X.V) (b : Fin (m + 1)) :
    ∑ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) = capelliC X.E x (f b) := by
  have key := (capelliExpand (Module.End ℂ X.V) m X.E x X.gl).1 b
  have h : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) =
      if b = c then capelliC X.E x (f c) else 0 := by
    intro c
    have := LinearMap.congr_fun (key c) (f c)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    rw [this]
    split_ifs <;> simp
  simp only [h]
  simp

theorem omMinor : OmMinor := by
  intro m X x
  rw [GlobalTheory.T.QuantumDeterminantEquality (m + 1) X.V X.E x]
  refine LinearMap.ext fun f => funext fun b => ?_
  have h := capelli_component X x f b
  simp only [capelli_entry_apply, smul_add, sum_add_distrib] at h
  simp only [LinearMap.compLeft_apply, Function.comp_apply, ← h]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.add_apply, Pi.smul_apply, om_apply]
  simp only [minorOp, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  refine (add_comm _ _).trans ?_
  congr 1
  · exact sum_comm
  · rw [sum_comm]
    simp [smul_sum, smul_comm x]

end GlobalTheory.CompanionTheory.HeckeCapelli
