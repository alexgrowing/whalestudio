import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfCompEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidLatticeSurjectiveProjectionStatement
open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat.FirstLattice

theorem isSMulRegular_of_isReflexive {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M]
    {a : R} (ha : IsSMulRegular R a) : IsSMulRegular M a := by
  intro x y h
  refine (Module.bijective_dual_eval R M).1 (LinearMap.ext fun f => ha ?_)
  have h' : f (a • x) = f (a • y) := congrArg f h
  rw [map_smul, map_smul] at h'
  exact h'

theorem exact_seq : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R) (c : ConstTate (eps S) G), Module.IsReflexive S.R G.dual.omega → (zeta S.ε 1 - 1) • c.W ≤ LinearMap.range c.alDual ∧ LinearMap.range c.alDual ≤ c.W ∧ LinearMap.range c.alDual ≤ H D c 0 ∧ LinearMap.range c.alDual ⊓ base S G.height = (zeta S.ε 1 - 1) • c.W ∧ (∀ y : G.dual.omega, (zeta S.ε 1 - 1) • y ∈ LinearMap.range c.al) ∧ ∀ pr : H D c 0 →ₗ[S.R] G.dual.omega, (∀ x : H D c 0, (zeta S.ε 1 - 1) • pr x = c.al (x : Fin G.height → S.R)) → ((base S G.height).comap (H D c 0).subtype).map pr = LinearMap.range c.al := by
  intro p _ D S G c hrefl
  obtain ⟨u, hu⟩ := GlobalTheory.PerfdLat.b_eq_unit_smul_alDual p D S
  obtain ⟨hb, -⟩ := hu G c
  obtain ⟨pr, hsurj, hpr, hker⟩ := GlobalTheory.T.perfectoid_lattice_surjective_projection p D S G c hrefl
  have htor : IsSMulRegular G.dual.omega (zeta S.ε 1 - 1) := isSMulRegular_of_isReflexive (isSMulRegular_zeta_sub_one S 0)
  have hH : LinearMap.range c.alDual ≤ H D c 0 := by
    rintro x ⟨y, rfl⟩
    obtain ⟨m, rfl⟩ := D.toLie_surjective G y
    have hx : c.alDual (D.toLie G m) = ((u⁻¹ : (S.R)ˣ) : S.R) • b D c m := by
      rw [hb, smul_smul, Units.inv_mul, one_smul]
    rw [hx, H_zero]
    refine Submodule.smul_mem _ _ (Submodule.map_mono (K_le_succ D c 0) ?_)
    exact ⟨coord D c m, ⟨m, rfl⟩, rfl⟩
  have hW : LinearMap.range c.alDual ≤ c.W := by
    intro x hx
    rw [ConstTate.mem_W, ← hpr ⟨x, hH hx⟩, (hker ⟨x, hH hx⟩).2 hx, smul_zero]
  have h1 : (zeta S.ε 1 - 1) • c.W ≤ LinearMap.range c.alDual := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hx
    have hb' : (zeta S.ε 1 - 1) • w ∈ H D c 0 := base_le_H D c 0 ((mem_base S _).2 ⟨w, rfl⟩)
    refine (hker ⟨_, hb'⟩).1 (htor ?_)
    show (zeta S.ε 1 - 1) • _ = (zeta S.ε 1 - 1) • _
    rw [hpr, smul_zero, map_smul, (ConstTate.mem_W c w).1 hw, smul_zero]
  refine ⟨h1, hW, hH, le_antisymm ?_ (le_inf h1 ?_), fun y => ?_, fun pr' hpr' => ?_⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨y, rfl⟩ := (mem_base S x).1 hx'
    refine Submodule.smul_mem_pointwise_smul _ _ _ ((ConstTate.mem_W c y).2 (htor ?_))
    show (zeta S.ε 1 - 1) • _ = (zeta S.ε 1 - 1) • _
    rw [← map_smul, smul_zero]
    exact (ConstTate.mem_W c _).1 (hW hx)
  · intro x hx
    obtain ⟨w, -, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hx
    exact (mem_base S _).2 ⟨w, rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨_, (hpr x).symm⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv⟩ := (mem_base S _).1 (Submodule.mem_comap.1 hx)
      refine ⟨v, htor ?_⟩
      show (zeta S.ε 1 - 1) • _ = (zeta S.ε 1 - 1) • _
      rw [hpr', ← map_smul, hv]
      rfl
    · rintro ⟨v, rfl⟩
      have hv : (zeta S.ε 1 - 1) • v ∈ H D c 0 := base_le_H D c 0 ((mem_base S _).2 ⟨v, rfl⟩)
      refine ⟨⟨_, hv⟩, (mem_base S _).2 ⟨v, rfl⟩, htor ?_⟩
      show (zeta S.ε 1 - 1) • _ = (zeta S.ε 1 - 1) • _
      rw [hpr', map_smul]

end GlobalTheory.PerfdLat.FirstLattice
