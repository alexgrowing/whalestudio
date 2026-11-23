import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDiagOfLower

open Polynomial ValuativeRel

namespace GlobalTheory.IwahoriRegular

theorem regular_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits := by
  intro k _ _ _ _ N ϖ hϖ ν hν x hx y hy
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let w : 𝒪[k] := ⟨ϖ, hlt.le⟩
  have hw : Irreducible w := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have low : ∀ h : GL (Fin N) 𝒪[k], h ∈ (GlobalTheory.SmGL.borel 𝓀[k] (Fin N)).comap
      (Matrix.GeneralLinearGroup.map (n := Fin N) (IsLocalRing.residue 𝒪[k])) →
      ∀ i j, j < i → (h : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro h hh i j hij
    have := (GlobalTheory.SmGL.mem_borel _).1 hh i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  obtain ⟨r, hr, hchar⟩ := GlobalTheory.IwahoriRoots.iwahori_roots 𝒪[k] k w hw N ν hν x' y' (low x' hx') (low y' hy')
  have hinj : Function.Injective r := fun i j h => hν.injective (by rw [← (hr i).2, ← (hr j).2, h])
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x' * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν *
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (x' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) *
        Matrix.diagonal (fun i => algebraMap 𝒪[k] k w ^ ν i) *
        (y' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    rfl
  show Separable (Matrix.charpoly _) ∧ Splits (Matrix.charpoly _)
  rw [e, hchar]
  exact ⟨separable_prod_X_sub_C_iff.2 hinj, Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _⟩

end GlobalTheory.IwahoriRegular
