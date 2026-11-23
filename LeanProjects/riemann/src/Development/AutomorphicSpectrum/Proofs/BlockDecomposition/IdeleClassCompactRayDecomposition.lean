import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (u : (AF F)ˣ) : IsNm σ (ofF u : (AF F ⊗[F] E)ˣ) (u * u) := by
  unfold IsNm
  have hs : sigR (AF F) σ ((u : AF F) ⊗ₜ[F] (1 : E)) = (u : AF F) ⊗ₜ[F] (1 : E) := by
    simp [sigR]
  have e : ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e, hs, Units.val_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ideleEquiv_ofE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : Eˣ) :
    GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
  apply Units.ext
  rw [GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv]
  exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem exists_unit_decomp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) :
    ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n →
      ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧
        md n = ε ^ (2 * Module.finrank ℚ F) := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  refine ⟨(GroundTheory.BlockD.ThmBHecke.ideleEquiv F E).symm '' D,
    hD.image GroundTheory.BlockD.ThmBHecke.continuous_ideleEquiv_symm, fun y n hyn => ?_⟩
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : 2 * Module.finrank ℚ F ≠ 0 := by omega
  have hn : 0 < md n := (IdeleGroup.ideleModule F n).2
  set m := 2 * Module.finrank ℚ F with hmdef
  set ε : ℝ := md n ^ ((m : ℝ)⁻¹) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hn _
  have hεm : md n = ε ^ m := (Real.rpow_inv_natCast_pow hn.le hm).symm
  have hray : md (r ε * r ε) = ε ^ m := by
    have h1 := ((GlobalTheory.T.ray_norm_and_module_formula F hcm.1 θ hθ r hr).2 ε hε)
    have h2 : md (r ε * r ε) = md (r ε) * md (r ε) := by simp [md, map_mul]
    rw [h2, h1, hmdef, two_mul, pow_add]
  have hy := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hyn
  have hu := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm (ofF (r ε)) (r ε * r ε) (isNm_ofF σ (r ε))
  set I := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E with hI
  have hker : I (y * (ofF (r ε))⁻¹) ∈ IdeleGroup.normOneSubgroup E := by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    have hpos : (0 : ℝ) < ε ^ m := pow_pos hε m
    rw [map_mul, map_inv, map_mul, map_inv]
    change ((IdeleGroup.ideleModule E (I y) : ℝ)) *
      ((IdeleGroup.ideleModule E (I (ofF (r ε))) : ℝ))⁻¹ = 1
    rw [hy, hu, hray, hεm]
    exact mul_inv_cancel₀ hpos.ne'
  obtain ⟨t, ht⟩ := hxD _ hker
  refine ⟨t⁻¹, I.symm (IdeleGroup.diagonal E t * I (y * (ofF (r ε))⁻¹)), ε, ⟨_, ht, rfl⟩, hε, ?_, hεm⟩
  apply I.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hI, ideleEquiv_ofE, map_inv, ← hI, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
