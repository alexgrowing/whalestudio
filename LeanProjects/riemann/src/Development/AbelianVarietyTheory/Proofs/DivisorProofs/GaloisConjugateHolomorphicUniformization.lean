import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialZeroOfNotTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationDifferentialZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationSemilinearMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjTangent

theorem exists_conj_holUnif_tangent : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X X' : Obj F 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ X.A.left) (g : ℂ ≃+* ℂ)
    (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p →
    ∃ u' : HolUnif X'.A (X'.diag c) n, ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v →
        u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
  intro _ _ _ F _ _ 𝔠 X X' p g c n u Ω₀ Ω₁ h0 h1 hX
  have hn := Obj.holUnif_dim_eq X u
  subst hn
  obtain ⟨L₁, u₁, -, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X'
  obtain ⟨u₀, -, -, -, -⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif X'.A X'.ab L₁ _ u₁ (X'.diag c)
    (pull_isLB (X'.isLB c) _)
  obtain ⟨-, hu⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨hu₀, -⟩ := GlobalTheory.TorusTransfer.tangent_bijective u₀ X'.dim
  obtain ⟨T, hTi, hT⟩ := GlobalTheory.T.conjugate_uniformization_semilinear_map X.A X'.A p g hX.grp _ _ _ u u₀ hu hu₀
  let ψ : (Fin (Module.finrank ℚ F) → ℂ) → (Fin (Module.finrank ℚ F) → ℂ) :=
    fun w' => Ω₀⁻¹ • fun j => g.symm (Ω₁ * w' j)
  have hψa : ∀ a b, ψ (a + b) = ψ a + ψ b := fun a b => by
    simp only [ψ, ← smul_add]
    congr 1
    ext j
    simp [mul_add]
  have hψs : ∀ (a : ℂ) b, ψ (a • b) = g.symm a • ψ b := fun a b => by
    simp only [ψ, smul_comm (g.symm a) Ω₀⁻¹]
    congr 1
    ext j
    simp [mul_left_comm]
  let φl : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) :=
    { toFun := fun w' => T (ψ w')
      map_add' := fun a b => by simp only [hψa, map_add]
      map_smul' := fun a b => by
        simp only [hψs, map_smulₛₗ, RingHom.id_apply]
        congr 1
        simp }
  have hinj : Function.Injective φl := by
    intro a b hab
    have hab' := hTi hab
    simp only [ψ] at hab'
    have := smul_right_injective _ (inv_ne_zero h0) hab'
    ext j
    have e := congrFun this j
    simp only [EmbeddingLike.apply_eq_iff_eq] at e
    exact mul_left_cancel₀ h1 e
  let φ := LinearEquiv.ofInjectiveEndo φl hinj
  obtain ⟨u', -, -, -, -, hD⟩ := GlobalTheory.exists_holUnif_reparam X'.A (X'.diag c) _ u₀ φ (fun _ => 1)
    (differentiable_const 1) (fun _ => one_ne_zero) rfl
  refine ⟨u', fun w v v' hv hd => hD _ _ ?_⟩
  by_cases ht : IsTangent v
  · have e : φ (fun j => g (Ω₀ * w j) / Ω₁) = T w := by
      show T (ψ _) = T w
      congr 1
      ext j
      simp only [ψ, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_cancel₀ _ h1, RingEquiv.symm_apply_apply]
      field_simp
    rw [e]
    exact hT w v v' ht hv hd
  · have hw := GlobalTheory.T.differential_zero_of_not_tangent F 𝔠 X _ _ u w v hd ht
    subst hw
    have e : φ (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
      have : (fun j => g (Ω₀ * (0 : Fin (Module.finrank ℚ F) → ℂ) j) / Ω₁) = 0 := by
        ext j
        simp
      rw [this, map_zero]
    rw [e]
    exact GlobalTheory.T.conjugate_uniformization_differential_zero X.A X'.A p g hX.grp _ _ _ _ u u₀ v v' hv hd

end GlobalTheory.ConjTangent
