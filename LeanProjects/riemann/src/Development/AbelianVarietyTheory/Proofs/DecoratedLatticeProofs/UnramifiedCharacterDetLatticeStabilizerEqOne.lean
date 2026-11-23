import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
open scoped Pointwise

namespace GlobalTheory.LatPair.Det

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem det_mem_of_mem_latStab_std {g : GL n k} (hg : g ∈ latStab (stdLat k n)) : g.val.det ∈ 𝒪[k] := by
  rw [MulAction.mem_stabilizer_iff] at hg
  have t2 : ∀ v : n → k, v ∈ stdLat k n ↔ ∀ i, v i ∈ 𝒪[k] := by
    intro v
    simp only [stdLat, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ i
      exact (y i).2
    · intro h
      exact ⟨fun i => ⟨v i, h i⟩, rfl⟩
  have hent : ∀ i j, (g : Matrix n n k) i j ∈ 𝒪[k] := by
    intro i j
    have hs : Pi.single j (1 : k) ∈ stdLat k n := by
      rw [t2]
      intro i'
      by_cases h : i' = j
      · subst h
        simp only [Pi.single_eq_same]
        exact one_mem _
      · simp only [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h1 : g • Pi.single j (1 : k) ∈ stdLat k n := by
      rw [← hg]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hs
    rw [t2] at h1
    have h2 := h1 i
    change ((g : Matrix n n k) *ᵥ Pi.single j 1) i ∈ 𝒪[k] at h2
    simpa [Matrix.mulVec_single] using h2
  let A : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨(g : Matrix n n k) i j, hent i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (g : Matrix n n k) := by
    ext i j
    rfl
  rw [← hA, ← RingHom.map_det]
  exact (A.det).2

theorem exists_smul_stdLat_eq (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : ∃ h : GL n k, h • stdLat k n = L := by
  let b := Module.Free.chooseBasis 𝒪[k] L
  let B := b.extendOfIsLattice k
  have hc : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[k] L) = Fintype.card n := by
    have := Module.finrank_eq_card_basis B
    simpa using this.symm
  let e := Fintype.equivOfCardEq hc
  let B' := B.reindex e
  let P := (Pi.basisFun k n).toMatrix B'
  let Q := B'.toMatrix (Pi.basisFun k n)
  let h : GL n k := ⟨P, Q, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have hB' : ∀ j, B' j = (b (e.symm j) : n → k) := by
    intro j
    simp [B', B]
  have key : ∀ y : n → k, h • y = ∑ j, y j • B' j := by
    intro y
    change P *ᵥ y = _
    ext i
    simp [P, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
  refine ⟨h, ?_⟩
  ext x
  simp only [HSMul.hSMul, SMul.smul]
  rw [Submodule.mem_map]
  simp only [DistribSMul.toLinearMap_apply]
  change (∃ y ∈ stdLat k n, h • y = x) ↔ x ∈ L
  simp only [key]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine L.sum_mem fun j _ => ?_
    rw [hB']
    change algebraMap 𝒪[k] k (c j) • (b (e.symm j) : n → k) ∈ L
    rw [algebraMap_smul]
    exact L.smul_mem (c j) (b (e.symm j)).2
  · intro hx
    let c := b.repr ⟨x, hx⟩
    refine ⟨fun j => (c (e.symm j) : k), ⟨fun j => c (e.symm j), rfl⟩, ?_⟩
    simp_rw [hB']
    have hsum := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at hsum
    rw [Equiv.sum_comp e.symm (fun i => ((c i : 𝒪[k]) : k) • (b i : n → k))]
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact algebraMap_smul k (c i) _

theorem det_mem_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) ∈ 𝒪[k] := by
  obtain ⟨h, rfl⟩ := exists_smul_stdLat_eq L
  have hs : h⁻¹ * g * h ∈ latStab (stdLat k n) := by
    simp only [latStab, MulAction.mem_stabilizer_iff] at hg ⊢
    rw [mul_smul, mul_smul, hg, inv_smul_smul]
  have h1 := det_mem_of_mem_latStab_std hs
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at h1
  have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * g * h) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [hdet] at h1

theorem valuation_det_of_mem_latStab {L : Submodule 𝒪[k] (n → k)} [L.IsLattice k] {g : GL n k} (hg : g ∈ latStab L) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 := det_mem_of_mem_latStab hg
  have h2 := det_mem_of_mem_latStab (inv_mem hg)
  rw [map_inv, Units.val_inv_eq_inv_val] at h2
  set d : k := ((Matrix.GeneralLinearGroup.det g : kˣ) : k) with hd
  have hd0 : d ≠ 0 := Units.ne_zero _
  have hu : IsUnit (⟨d, h1⟩ : 𝒪[k]) :=
    ⟨⟨⟨d, h1⟩, ⟨d⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hd0), Subtype.ext (inv_mul_cancel₀ hd0)⟩, rfl⟩
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).1 hu

end

theorem isUnram_det_latStab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  exact hμ _ (valuation_det_of_mem_latStab hg)

end GlobalTheory.LatPair.Det
