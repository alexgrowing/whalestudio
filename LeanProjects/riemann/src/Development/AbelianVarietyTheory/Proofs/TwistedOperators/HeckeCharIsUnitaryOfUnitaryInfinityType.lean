import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.HeckeUnitaryInf

theorem isUnitary_of_hasInf : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  intro L _ _ χ I _ φ n h
  have hinf : ∀ k : Lˣ, ‖((χ.1 (infDiag k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    have e : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := h k
    rw [e, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]
  have hI : ∀ y : (InfiniteAdeleRing L)ˣ, ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖ = 1 := by
    have := (GlobalTheory.HeckeGal.denseRange_units_inf L).equalizer
      (g := fun y => ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖) (h := fun _ => (1 : ℝ))
      ((Units.continuous_val.comp (χ.2.1.comp GlobalTheory.HeckeGal.continuous_inlInf)).norm) continuous_const
      (funext fun k => by
        simp only [Function.comp_apply]
        rw [← GlobalTheory.HeckeGal.infDiag_eq]
        exact hinf k)
    exact fun y => congrFun this y
  have hF : ∀ x : Ideles L, IsFinIdele x → ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1 := by
    intro x hx
    obtain ⟨m, hm, u, k, u1, u2, e⟩ := GlobalTheory.UnUnitCmp.Val.exists_pow_eq x hx
    have e1 := congrArg (fun a => ‖((χ.1 a : ℂˣ) : ℂ)‖) e
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hinf k,
      GlobalTheory.HeckeFin.norm_eq_one χ u u1 u2, χ.2.2 k, Units.val_one, norm_one, mul_one] at e1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e1
  intro z
  have hz : z = GlobalTheory.HeckeGal.inlInf L (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) z) *
      finPartI L z := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [hz, map_mul, Units.val_mul, norm_mul, hI, hF _ (fun _ => rfl), one_mul]

end GlobalTheory.HeckeUnitaryInf
