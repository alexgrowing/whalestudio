import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.FilteredPoleLength.LocalDescentLevels.FilIntegerStep
import Formalism.FilteredPoleLength.LocalDescentLevels.BCount

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem localStep : LocalStep := by
  intro O K V W _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' X NK
    hMl hΘl hNΘ hthM hthΘ hker hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁' hAA hf1 hf2 hf3 V'
  have hp0 : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  have hsm : ∀ v : V, (algebraMap O K ϖ) ^ e • v = ϖ ^ e • v := by
    intro v
    rw [← map_pow, algebraMap_smul]

  have hIdx := Formalism.IncomingBounds.index_last_reduction_holds O K V ϖ hϖ (e : ℤ) M Θ hMl hΘl V'
  have hbridge : M.map ((((algebraMap O K ϖ) ^ (e : ℤ)) • LinearMap.id : V →ₗ[K] V).restrictScalars O)
      = X := by
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, zpow_natCast, X, LinearMap.smul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hsm y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hsm y⟩
  rw [hbridge] at hIdx

  have hLA := localAssembly O K V W ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a'
    hNΘ hthM hthΘ hker hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁' hAA

  have hthX : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [hsm]
    exact ⟨th j, hthM j, rfl⟩
  have hcX : ∀ x ∈ X, ∀ i, ∃ u : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K u := by
    rintro _ ⟨y, hy, rfl⟩ i
    obtain ⟨u, hu⟩ := hcM y hy i
    refine ⟨u, ?_⟩
    show c (ϖ ^ e • y) i = _
    rw [← hsm, map_smul, Pi.smul_apply, hu, smul_eq_mul, ← mul_assoc, sub_eq_add_neg,
      zpow_add₀ hp0, zpow_natCast]
  obtain ⟨m, -, hmle⟩ := quotientLength O K V ϖ hϖ n c _ hker X e be th hcX hthX a a' ha ha' hdet
  set q : ℤ := ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
      ((IsDiscreteValuationRing.addVal O a').toNat : ℤ) + (n : ℤ) * (be : ℤ) with hqdef
  have hq : 0 ≤ q := le_trans (Int.natCast_nonneg m) hmle

  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((q.toNat : ℕ) : ℕ∞) := hLA
  have hsum : L1 + L2 + L3 + ((q.toNat : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + q.toNat : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + q.toNat := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have hqt : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
  have : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + q := by
    rw [← hqt]; exact_mod_cast hLt
  linarith

theorem levelsChain : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith

end Formalism.LatticeBaseChangeAlt
