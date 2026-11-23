import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem not_keyOn_of_sec_zero : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)), KeyOn (RingHom.id K) x G L σ y →
    (∀ i, σ.f i = 0) → False := by
  intro K _ G _ _ L σ x y hK hσ
  obtain ⟨φ, -, ψ, -, -, -, -, hsec, -⟩ := hK
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint K)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hzi : z ∈ x.P.L.U i := x.P.A.left.basicOpen_le _ hi
  have hc : φ z ∈ (⨆ a, L.L.U a) := by rw [L.isLB.cover]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  let j : (L.L.pull φ).ι := fun _ => a
  have hzj : z ∈ (L.L.pull φ).U j := Set.mem_iInter.2 fun _ => ha
  have h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    inf_le_left.trans (LB.wchart_le L.L (fun _ => φ) j PUnit.unit)
  have e := hsec j i h
  rw [hσ, map_zero] at e
  have e0 : resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i) = 0 := by
    have u := (ψ.s (j, i)).isUnit
    exact (u.mul_right_eq_zero).1 e.symm
  have hb : z ∈ x.P.A.left.basicOpen
      (resG x.P.A.left (inf_le_right : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ x.P.L.U i) (x.th.f i)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hzj, hzi⟩, hi⟩
  rw [e0, Scheme.basicOpen_zero] at hb
  exact hb

end GlobalTheory.KeyEven
