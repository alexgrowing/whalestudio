import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.CuspRep.ParLaws GlobalTheory.SatakeFlip

namespace GlobalTheory.BorelSphExist

section Char

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable (k) in

def unrBorel (α : Fin N → ℂˣ) : borel k (Fin N) →* ℂˣ :=
  ((torusChar fun i => SmGL.unrChar k (α i)).comp (leviTorus k (Fin N)).symm.toMonoidHom).comp
    (leviProj k (points (Fin N)))

theorem unrBorel_apply (α : Fin N → ℂˣ) (b : borel k (Fin N)) :
    unrBorel k α b = ∏ i : Fin N, α i ^ ord k (diagU b i) :=
  torusChar_apply _ _

theorem unrBorel_eq_one (α : Fin N → ℂˣ) (b : borel k (Fin N)) (hb : b.1 ∈ KO k (Fin N)) :
    unrBorel k α b = 1 := by
  rw [unrBorel_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hb
  have h3 := congrArg (valuation k) (inv_diag_mul b.2 i)
  rw [map_mul, map_one] at h3
  have a1 : valuation k (b.1.val i i) ≤ 1 := h1 i i
  have a2 : valuation k ((b.1⁻¹).val i i) ≤ 1 := h2 i i
  have h : valuation k (diagU b i : k) = 1 := by
    rw [val_diagU]
    exact le_antisymm a1 (h3.ge.trans (mul_le_of_le_one_left' a2))
  rw [ord_eq_zero h, zpow_zero]

end Char

theorem exists_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) →
    ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  intro k _ _ _ _ N γ hγ
  let α : Fin N → ℂˣ := fun i => Units.mk0 (γ i) (hγ i)
  obtain ⟨φ, h1, h2, h3⟩ := exists_fun (borel k (Fin N)) (KO k (Fin N)) (unrBorel k α) (fun g => by
    obtain ⟨b, hb, x, hx, e⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
    exact ⟨⟨b, (mem_borel _).2 hb⟩, x, hx, e⟩) (unrBorel_eq_one α)
  refine ⟨φ, fun g x hx => h3 g x hx, fun b hb t ht => ?_⟩
  have hφ := h2 ⟨b, hb⟩ 1
  rw [mul_one, h1, mul_one] at hφ
  rw [hφ, unrBorel_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : diagU ⟨b, hb⟩ i = t i := Units.ext ((val_diagU _ i).trans (ht i))
  rw [hd, Units.val_zpow_eq_zpow_val]
  rfl

end GlobalTheory.BorelSphExist

end
