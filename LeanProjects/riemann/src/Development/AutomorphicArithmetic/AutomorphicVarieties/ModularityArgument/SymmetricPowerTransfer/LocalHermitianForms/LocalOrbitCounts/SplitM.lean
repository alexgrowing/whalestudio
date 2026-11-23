import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.SplitS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem splitM_lemma {K : Type} [Field K] {Δ τ : K} (c k : K) (m : EL Δ τ) (x y : Sp Δ τ) :
    herm c (k • m) x y = herm c m (x.1, 0) y + algebraMap K (Lsq K Δ) k * herm c m (0, x.2) y := by
  rw [← algebraMap_smul (Lsq K Δ) k m]
  simp only [herm, smul_mul_assoc, map_smul, smul_eq_mul, mul_zero, zero_mul, map_zero, add_zero, zero_add]

private theorem splitM_lemma_3 {K : Type} [Field K] {Δ τ : K} (c : K) (m : EL Δ τ) (y : Sp Δ τ) :
    herm c m (0, 0) y = 0 := by
  simp [herm]

private theorem splitM_lemma_2 (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] (Δ τ : K) (hl : IsLoc O Δ) (c : K) (d m : EL Δ τ) (hd : IsDat c d m)
    (hτ : τ ∈ (algebraMap O K).range) (hu : ∃ u : Oˣ, algebraMap O K u = 2 - τ) (ε : Oˣ)
    (S : Set (Sp Δ τ)) (hS : IsFix O c d m S) : IsFix O c d (algebraMap O K ε • m) S := by
  obtain ⟨-, -, h1, h2⟩ := One.splitS O K Δ τ hl hτ hu c d m hd S hS
  have h2' : ∀ x ∈ S, ((0 : Lsq K Δ), x.2) ∈ S := fun x hx => by
    simpa [ofE_one] using h2 x hx 1 (by simp) (by simp)
  have e : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ε)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have ei : IsIntegral O (algebraMap K (Lsq K Δ) (algebraMap O K ↑ε⁻¹)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  refine ⟨hS.fg, fun y => ?_, hS.stab⟩
  rw [hS.dual y]
  constructor
  · intro hy x hx
    rw [splitM_lemma]
    exact (hy _ (h1 x hx)).add (e.mul (hy _ (h2' x hx)))
  · intro hy x hx
    have a := hy _ (h1 x hx)
    have b := hy _ (h2' x hx)
    rw [splitM_lemma] at a b
    simp only [splitM_lemma_3, mul_zero, add_zero, zero_add] at a b
    have hm' := splitM_lemma c 1 m x y
    rw [one_smul, map_one, one_mul] at hm'
    show IsIntegral O (herm c m x y)
    rw [hm']
    refine a.add ?_
    have := ei.mul b
    rwa [← mul_assoc, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, one_mul] at this

theorem UpperTheory.V.Z.Sym.Loc.splitM : UpperTheory.V.Z.Sym.Loc.SplitM := by
  intro O K _ _ _ _ _ Δ τ hl c d m hd hτ hu ε
  have hd' : IsDat c d (algebraMap O K ε • m) := by
    simpa using datSmul K Δ τ c d m hd (Units.map (algebraMap O K).toMonoidHom ε)
  have key : ∀ S, IsFix O c d (algebraMap O K ε • m) S ↔ IsFix O c d m S := by
    intro S
    constructor
    · intro h
      have := splitM_lemma_2 O K Δ τ hl c d _ hd' hτ hu ε⁻¹ S h
      rwa [smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul] at this
    · exact splitM_lemma_2 O K Δ τ hl c d m hd hτ hu ε S
  unfold lcount
  congr 1
  funext S
  by_cases h : IsFix O c d m S
  · rw [if_pos ((key S).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((key S).1 h')), if_neg h]
