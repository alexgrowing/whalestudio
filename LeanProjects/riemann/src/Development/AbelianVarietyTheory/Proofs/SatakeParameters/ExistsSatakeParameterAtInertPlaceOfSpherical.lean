import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecomposeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesRightTranslationStablStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorCompSphericalConvolutionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorSphericalUnitEqIdStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorBilinearStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

noncomputable section

namespace GlobalTheory.SatExists

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivOutside_mul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem trivOutside_inv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hNf⟩ := π.irrS.1.le hf₀S
  let U : Subgroup (GAf L n) :=
    Subgroup.closure ({κ | NG.Cong L n N κ} ∪ {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ})
  have hUmax : U ≤ Umax L n := (Subgroup.closure_le _).2 (by
    rintro κ (hκ | hκ)
    · exact hκ.1
    · exact hκ.1)
  have hUv : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) := fun κ hκ =>
    ⟨fun h => hUmax h, fun h => Subgroup.subset_closure (Or.inr ⟨h, hκ⟩)⟩
  have hCU : ∀ κ, NG.Cong L n N κ → κ ∈ U := fun κ hκ => Subgroup.subset_closure (Or.inl hκ)
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := by
    intro κ hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact funext fun g => hNf x hx g
      · exact hf₀K x hx.1 hx.2
    | one => exact funext fun g => by change f₀ (g * 1) = f₀ g; rw [mul_one]
    | mul x y _ _ hx hy =>
      refine funext fun g => ?_
      change f₀ (g * (x * y)) = f₀ g
      have h1 : f₀ (g * x * y) = f₀ (g * x) := congrFun hy (g * x)
      have h2 : f₀ (g * x) = f₀ g := congrFun hx g
      rw [← mul_assoc, h1, h2]
    | inv x _ hx =>
      refine funext fun g => ?_
      change f₀ (g * x⁻¹) = f₀ g
      have h1 : f₀ (g * x⁻¹ * x) = f₀ (g * x⁻¹) := congrFun hx (g * x⁻¹)
      rw [← h1, inv_mul_cancel_right]
  have hdec : ∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨a, b, e, ha, hat, hb, hc⟩ := GlobalTheory.T.congruence_element_decompose L n v N x hx
        exact ⟨a, b, e, (hUv a hat).2 ha, hat, hCU b hb, hc⟩
      · exact ⟨x, 1, (mul_one x).symm, Subgroup.subset_closure (Or.inr hx), hx.2, one_mem _,
          fun y _ => by rw [mul_one, one_mul]⟩
    | one => exact ⟨1, 1, (mul_one 1).symm, one_mem _, trivOutside_one v, one_mem _,
        fun y _ => by rw [mul_one, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      obtain ⟨a', b', rfl, ha', hat', hb', hbc'⟩ := hy
      refine ⟨a * a', b * b', ?_, mul_mem ha ha', trivOutside_mul hat hat', mul_mem hb hb', fun z hz => ?_⟩
      · simp only [mul_assoc]
        rw [← mul_assoc b a', ← hbc a' hat', mul_assoc]
      · rw [← mul_assoc, hbc z hz, mul_assoc, hbc' z hz, ← mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      refine ⟨a⁻¹, b⁻¹, ?_, inv_mem ha, trivOutside_inv hat, inv_mem hb, fun z hz => ?_⟩
      · rw [mul_inv_rev, eq_mul_inv_iff_mul_eq, mul_assoc, hbc a⁻¹ (trivOutside_inv hat), inv_mul_cancel_left]
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc z hz, inv_mul_cancel_left]
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      add_mem' := fun ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add, ha.2 κ hκ, hb.2 κ hκ]⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI : FiniteDimensional ℂ V := by
    have := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) ?_
    rintro f ⟨hfS, hfU⟩
    exact ⟨(π.irrS.1.le hfS).1, fun κ hκ g => congrFun (hfU κ (hCU κ hκ)) g⟩
  have hf₀V : f₀ ∈ V := ⟨hf₀S, hf₀U⟩
  haveI : Nontrivial V := ⟨⟨⟨f₀, hf₀V⟩, 0, fun e => hf₀0 (congrArg Subtype.val e)⟩⟩
  let T : Hecke ℂ (KU Dv.σw n) → Module.End ℂ V := fun h =>
    { toFun := fun f => ⟨heckeFunI L n U Dv h.1 f.1,
        GlobalTheory.T.inertHeckeOperator_preserves_rightTranslationStable L n v w Dv U hUv π.W π.S π.irrS.1.stable h.1 h.2 f.1 f.2.1,
        GlobalTheory.T.inertHeckeOperator_preserves_levelInvariants L n v w Dv U hUv hdec π.W h.1 h.2 f.1 f.2.2⟩
      map_add' := fun f f' => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 1 f.1 f'.1).2.2.1)
      map_smul' := fun c f => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.2.2) }
  have hT : ∀ h (f : V), ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h.1 f.1 := fun _ _ => rfl
  have hcomm : ∀ a b, T a * T b = T b * T a := fun a b => LinearMap.ext fun f => Subtype.ext (by
    change heckeFunI L n U Dv a.1 (heckeFunI L n U Dv b.1 f.1) = heckeFunI L n U Dv b.1 (heckeFunI L n U Dv a.1 f.1)
    rw [← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W a.1 a.2 b.1 b.2 f.1 f.2.2,
      ← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W b.1 b.2 a.1 a.2 f.1 f.2.2,
      GlobalTheory.UnitarySwap.heckeCommU _ Dv.ϖ Dv.σw _ n ℂ Dv.unram a.1 a.2 b.1 b.2])
  obtain ⟨f, hf0, hμ⟩ := GlobalTheory.exists_common_eigenvector_of_commute T hcomm
  choose μ hμ using hμ
  have ev : ∀ h : Hecke ℂ (KU Dv.σw n), heckeFunI L n U Dv h.1 f.1 = μ h • f.1 := fun h =>
    congrArg Subtype.val (hμ h)
  have hf'0 : (f : GAf L n → π.W) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have inj := smul_left_injective ℂ hf'0
  let l : Hecke ℂ (KU Dv.σw n) →ₗ[ℂ] ℂ :=
    { toFun := μ
      map_add' := fun h h' => inj (by
        change μ (h + h') • f.1 = (μ h + μ h') • f.1
        rw [← ev, add_smul, ← ev, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 1 f.1 f.1).1)
      map_smul' := fun c h => inj (by
        change μ (c • h) • f.1 = (c * μ h) • f.1
        rw [← ev, mul_smul, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.1) }
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq Dv.unram l
    (inj (by
      change μ _ • f.1 = (1 : ℂ) • f.1
      rw [← ev, one_smul]
      exact GlobalTheory.T.inertHeckeOperator_sphericalUnit_eq_id L n v w Dv U hUv π.W f.1 f.2.2))
    (fun h h' => inj (by
      change μ _ • f.1 = (μ h * μ h') • f.1
      rw [← ev]
      change heckeFunI L n U Dv (conv (KU Dv.σw n) h.1 h'.1) f.1 = _
      rw [GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 f.1 f.2.2, ev h',
        (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 (μ h') f.1 f.1).2.2.2, ev h, smul_smul, mul_comm]))
  refine ⟨fun i => (α i : ℂ), f.1, f.2.1, hf'0, U, f.2.2, hUv, fun h hh => ?_⟩
  rw [ev ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.SatExists
