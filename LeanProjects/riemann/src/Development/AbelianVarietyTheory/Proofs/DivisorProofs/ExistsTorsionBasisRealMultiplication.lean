import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankTwoBasisModNStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPoints

theorem exists_torsion_basis : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A]
    (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F))
    (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) →
    ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  intro F _ _ A _ _ rm L u Fa hFa N hN
  have hst : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ → Fa a l ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hFa, (u.ker l).2 hl, Hom.one_def, Category.assoc, (rm.hom a).one_hom]
  letI : Module (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) := Module.compHom _ Fa
  have hsmul : ∀ (a : 𝓞 F) (v : Fin (Module.finrank ℚ F) → ℂ), a • v = Fa a v := fun _ _ => rfl
  let Λ' : Submodule (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) :=
    { carrier := u.Λ
      add_mem' := fun ha hb => u.Λ.add_mem ha hb
      zero_mem' := u.Λ.zero_mem
      smul_mem' := fun a l hl => hst a l hl }
  let e : u.Λ ≃+ Λ' :=
    { toFun := fun l => ⟨l.1, l.2⟩, invFun := fun l => ⟨l.1, l.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  haveI : Module.Finite ℤ Λ' := Module.Finite.equiv e.toIntLinearEquiv
  haveI : IsAddTorsionFree Λ' := ⟨fun n hn a b h => by
    apply Subtype.ext
    have h' : n • (a : Fin (Module.finrank ℚ F) → ℂ) = n • (b : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val h
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ n] at h'
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hn) h'⟩
  have hrank : Module.finrank ℤ Λ' = 2 * Module.finrank ℚ F := by
    rw [← e.toIntLinearEquiv.finrank_eq, ZLattice.rank ℝ u.Λ]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  obtain ⟨x, hgen, hfree⟩ := GlobalTheory.T.exists_rank_two_basis_mod_N F Λ' hrank N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpow : ∀ (z : Fin (Module.finrank ℚ F) → ℂ) (k : ℕ), u.ex (k • z) = u.ex z ^ k := by
    intro z k
    induction k with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hcancel : ∀ v : Fin (Module.finrank ℚ F) → ℂ, N • ((N : ℂ)⁻¹ • v) = v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have key : ∀ a b : 𝓞 F, (u.ex ((N : ℂ)⁻¹ • (x 0 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act a) *
      (u.ex ((N : ℂ)⁻¹ • (x 1 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act b) =
      u.ex ((N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ)) := by
    intro a b
    rw [← hFa, ← hFa, ← u.ex_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsmul, hsmul,
      smul_add, map_smul, map_smul]
  refine ⟨fun i => u.ex ((N : ℂ)⁻¹ • (x i : Fin (Module.finrank ℚ F) → ℂ)), ?_, ?_, ?_⟩
  · intro i
    rw [← hpow, hcancel]
    exact (u.ker _).2 (x i).2
  · intro a b h
    rw [key] at h
    refine hfree a b ⟨⟨_, (u.ker _).1 h⟩, Subtype.ext ?_⟩
    exact (hcancel _).symm
  · intro y hy
    obtain ⟨z, rfl⟩ := u.ex_onto y
    have hz : N • z ∈ u.Λ := (u.ker _).1 (by rw [hpow]; exact hy)
    obtain ⟨a, b, m', hm⟩ := hgen ⟨N • z, hz⟩
    refine ⟨a, b, ?_⟩
    rw [key]
    have hm' : N • z = ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + N • (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val hm
    have hz' : z = (N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      have h1 : z = (N : ℂ)⁻¹ • (N • z) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      rw [h1, hm', smul_add, ← Nat.cast_smul_eq_nsmul ℂ N (m' : Fin (Module.finrank ℚ F) → ℂ), smul_smul,
        inv_mul_cancel₀ hN0, one_smul]
    conv_lhs => rw [hz']
    rw [u.ex_add, (u.ker _).2 m'.2, _root_.mul_one]

end GlobalTheory.TorsionPoints
