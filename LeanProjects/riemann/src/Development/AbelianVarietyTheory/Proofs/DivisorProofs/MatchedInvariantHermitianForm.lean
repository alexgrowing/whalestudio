import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory

noncomputable section

namespace GlobalTheory.PolarizedDataL2

theorem exists_invariant_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∃ Bf : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ⋆[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] ℂ, (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) ∧ (∀ x, x ≠ 0 → 0 < (Bf x x).re) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ x y x' y' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (x' : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) x → (y' : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) y → Bf x' y' = Bf x y := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf h
  letI mA : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  set μ : Measure (Fin a' × Fin (a + a') → AF F) := Measure.addHaar with hμdef
  haveI hH : μ.IsAddHaarMeasure := by rw [hμdef]; infer_instance
  set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hD
  have memS : ∀ z : D, (z : GlobalTheory.ThK.Fn F a' (a + a')) ∈ schA F (Fin a' × Fin (a + a')) := fun z =>
    GlobalTheory.ThKRatInv.polData_le_schA B G.M' h.triple.geo.hM' (Submodule.mem_inf.1 z.2).1
  have hL : ∀ z : D, MemLp (z : GlobalTheory.ThK.Fn F a' (a + a')) 2 μ := fun z =>
    GlobalTheory.WeilM.schA_memLp_two F _ μ hH _ (memS z)
  let L : D → Lp ℂ 2 μ := fun z => (hL z).toLp z
  have Ladd : ∀ x y : D, L (x + y) = L x + L y := fun x y => MemLp.toLp_add (hL x) (hL y)
  have Lsmul : ∀ (c : ℂ) (x : D), L (c • x) = c • L x := fun c x => MemLp.toLp_const_smul c (hL x)
  have Lnorm : ∀ z : D, ‖L z‖ = (eLpNorm (z : GlobalTheory.ThK.Fn F a' (a + a')) 2 μ).toReal := fun z => Lp.norm_toLp _ _
  let Bf : D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (L x) (L y))
    (fun x₁ x₂ y => by simp only [Ladd, inner_add_left])
    (fun c x y => by simp only [Lsmul, inner_smul_left, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [Ladd, inner_add_right])
    (fun c x y => by simp only [Lsmul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  refine ⟨Bf, fun x y => ?_, fun x hx => ?_, ?_⟩
  · show inner ℂ (L y) (L x) = starRingEnd ℂ (inner ℂ (L x) (L y))
    exact (inner_conj_symm _ _).symm
  · show 0 < (inner ℂ (L x) (L x)).re
    have e1 : (inner ℂ (L x) (L x)).re = ‖L x‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) (L x)
      simpa using this
    rw [e1]
    refine pow_pos (norm_pos_iff.2 fun h0 => hx ?_) 2
    have hae : (x : GlobalTheory.ThK.Fn F a' (a + a')) =ᵐ[μ] 0 := by
      have h1 := (hL x).coeFn_toLp
      have h2 : ((L x : Lp ℂ 2 μ) : GlobalTheory.ThK.Fn F a' (a + a')) =ᵐ[μ] 0 := by
        rw [h0]; exact Lp.coeFn_zero _ _ _
      exact h1.symm.trans h2
    have hc : Continuous (x : GlobalTheory.ThK.Fn F a' (a + a')) := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (memS x)
    have hz := (Continuous.ae_eq_iff_eq μ hc continuous_const).1 hae
    exact Subtype.ext hz
  · intro k _ x y x' y' hx hy
    have U := (IsUWeilPair.isUSplitting h.triple.weil').unit
    have key : ∀ c : ℂ, ‖L x' + c • L y'‖ = ‖L x + c • L y‖ := fun c => by
      rw [← Lsmul, ← Ladd, ← Lsmul, ← Ladd, Lnorm, Lnorm]
      congr 1
      have e : ((x' + c • y' : D) : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) ((x + c • y : D) : GlobalTheory.ThK.Fn F a' (a + a')) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, hx, hy]
      rw [e]
      have u := U μ hH (1, k) _ (memS (x + c • y))
      rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
      rw [u]
    have s : ∀ (u v : Lp ℂ 2 μ) (c : ℂ), u - c • v = u + (-c) • v := fun u v c => by rw [neg_smul, sub_eq_add_neg]
    have k1 : ‖L x' + L y'‖ = ‖L x + L y‖ := by simpa using key 1
    have k2 : ‖L x' - L y'‖ = ‖L x - L y‖ := by
      have := key (-1); simp only [neg_smul, one_smul, ← sub_eq_add_neg] at this; exact this
    have k3 : ∀ c : ℂ, ‖L x' - c • L y'‖ = ‖L x - c • L y‖ := fun c => by rw [s, s]; exact key _
    show inner ℂ (L x') (L y') = inner ℂ (L x) (L y)
    rw [inner_eq_sum_norm_sq_div_four (L x') (L y'), inner_eq_sum_norm_sq_div_four (L x) (L y), k1, k2, k3, key]

end GlobalTheory.PolarizedDataL2
