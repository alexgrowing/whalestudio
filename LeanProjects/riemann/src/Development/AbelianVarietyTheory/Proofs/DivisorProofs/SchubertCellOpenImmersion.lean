import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLuDecompositionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellPointImmersionStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory

def rowPermGL (A : Type) [CommRing A] {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) A :=
  GeneralLinearGroup.mk'' ((1 : Matrix (Fin N) (Fin N) A).submatrix σ id) (by
    rw [det_permute, det_one, mul_one]
    exact (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom _))

theorem rowPermGL_mul_apply {A : Type} [CommRing A] {N : ℕ} (σ : Equiv.Perm (Fin N)) (g : GL (Fin N) A) (i j : Fin N) :
    (rowPermGL A σ * g).1 i j = g.1 (σ i) j := by
  change ∑ k, (1 : Matrix (Fin N) (Fin N) A) (σ i) k * g.1 k j = _
  rw [← mul_apply, one_mul]

theorem leading_minor_univGL_ne_zero {ι : Type} [Fintype ι] {N : ℕ} (σ : Equiv.Perm (Fin N)) (τ : ι) (k : ℕ)
    (hk : k ≤ N) :
    ((rowPermGL _ σ.symm * univGL ι N τ).1.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := fun h => by
  have e := congrArg (evalGL fun _ : ι => rowPermGL ℤ σ) h
  rw [map_zero, RingHom.map_det] at e
  have e' : (evalGL fun _ : ι => rowPermGL ℤ σ).mapMatrix
      ((rowPermGL _ σ.symm * univGL ι N τ).1.submatrix (Fin.castLE hk) (Fin.castLE hk)) = 1 := by
    rw [← submatrix_one (α := ℤ) _ (Fin.castLE_injective hk)]
    ext i j
    rw [RingHom.mapMatrix_apply, map_apply, submatrix_apply, submatrix_apply, rowPermGL_mul_apply, univGL_apply,
      evalGL_X]
    change (1 : Matrix (Fin N) (Fin N) ℤ) (σ (σ.symm _)) _ = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [e', det_one] at e
  exact one_ne_zero e

theorem exists_generic_comp_orbit_eq_comp_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) :
    ∃ s : Sp (FractionRing (GLRing ι N)) ⟶ Sp (CellRing a l),
      spMap (algebraMap (GLRing ι N) (FractionRing (GLRing ι N))) ≫ orbit a l = s ≫ cell a l w := by
  set K := FractionRing (GLRing ι N)
  set φ := algebraMap (GLRing ι N) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have h (τ : ι) := exists_blockLower_mul_blockUpper K N {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}
    (GeneralLinearGroup.map φ (rowPermGL _ (w τ).symm * univGL ι N τ)) fun k hk => by
      refine Ne.isUnit fun h => leading_minor_univGL_ne_zero (w τ) τ k hk (hφ ?_)
      rw [map_zero, RingHom.map_det]
      exact h
  choose L b hLb hL hb using h
  have hB (τ : ι) (i j : Fin N) : Below a l τ i j ↔
      ∃ s ∈ {s | ∃ k, a k = τ ∧ (l k : ℕ) = s}, (j : ℕ) < s ∧ s ≤ (i : ℕ) :=
    ⟨fun ⟨k, h₁, h₂⟩ => ⟨_, ⟨k, h₁, rfl⟩, h₂⟩, fun ⟨_, ⟨k, h₁, h₂⟩, h₃⟩ => ⟨k, h₁, h₂ ▸ h₃⟩⟩
  refine ⟨_, Eq.trans ?_ (flagPt_eq_comp_cell a l w (fun τ => rowPermGL K (w τ) * L τ) b
    (fun τ i j hij => by rw [rowPermGL_mul_apply]; exact hL τ _ _ (mt (hB _ _ _).2 hij))
    fun τ i j hij => hb τ i j ((hB _ _ _).1 hij))⟩
  rw [← flagPt_univGL, spMap_flagPt]
  congr 1
  funext τ
  rw [Pi.mul_apply, mul_assoc, ← hLb]
  ext i j
  rw [rowPermGL_mul_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, rowPermGL_mul_apply,
    Equiv.symm_apply_apply]

theorem schemeDominant_cell {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι)
    (l : κ → Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) : IsSchemeTheoreticallyDominant (cell a l w) := by
  obtain ⟨s, hs⟩ := exists_generic_comp_orbit_eq_comp_cell a l w
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap (GLRing ι N) (FractionRing (GLRing ι N)))) :=
    (schemeDominant_specMap_iff (CommRingCat.ofHom _)).2 (IsFractionRing.injective _ _)
  have : IsSchemeTheoreticallyDominant (s ≫ cell a l w) :=
    ⟨by rw [← hs, ker_comp_of_schemeDominant, Scheme.Hom.ker_eq_bot]⟩
  exact schemeDominant_of_comp s _

theorem isOpenImmersion_cell (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)) : IsOpenImmersion (cell a l w) := by
  have : IsImmersion (cell a l w ≫ plEmb a l) := by
    rw [cell, flagPt_plEmb]
    exact GlobalTheory.T.schubert_cell_point_immersion ι κ N a l w
  have : IsImmersion (cell a l w) := IsImmersion.of_comp _ (plEmb a l)
  have : QuasiCompact (cell a l w) := quasiCompact_of_noetherianSpace_source _
  have : IsIso (cell a l w).imageι := (isIso_imageι_iff _).2 (schemeDominant_cell a l w)
  have := isOpenImmersion_toImage (cell a l w)
  rw [← (cell a l w).toImage_imageι]
  infer_instance

end GlobalTheory
