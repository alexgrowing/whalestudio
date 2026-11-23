import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}

private theorem zero_one_mem_gammaSet_one (f : bddAut V) : Continuous (f : GA D V → ℂ) ∧
    (∀ γ ∈ GQ V, ∀ g, (f : GA D V → ℂ) (γ * g) = (f : GA D V → ℂ) g) ∧
    ∃ C : ℝ, ∀ g, ‖(f : GA D V → ℂ) g‖ ≤ C := f.2

private theorem integrableOn_fundamentalDomain_of_bounded {E : Type} [NormedAddCommGroup E] (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) {φ : GA D V → E} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ g, ‖φ g‖ ≤ C) : IntegrableOn φ 𝓕 ν := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.1
  haveI := hT.2.2.2.1
  exact Measure.integrableOn_of_bounded
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕).ne hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_mul_conj_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f f₂ : bddAut V) :
    IntegrableOn (fun g => (f : GA D V → ℂ) g * starRingEnd ℂ ((f₂ : GA D V → ℂ) g)) 𝓕 ν := by
  obtain ⟨hc, -, C, hC⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨hc₂, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
  refine integrableOn_fundamentalDomain_of_bounded hν h𝓕 (hc.mul (Complex.continuous_conj.comp hc₂)) (C * C₂) fun g => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC g) (hC₂ g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem exists_form_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ, ∀ f f₂, B f f₂ = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f₂ : bddAut V => l2 ν 𝓕 (f : GA D V → ℂ) f₂) ?_ ?_ ?_ ?_, fun f f₂ => rfl⟩
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a c) (integrableOn_mul_conj_bddAut hν h𝓕 b c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a b) (integrableOn_mul_conj_bddAut hν h𝓕 a c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

theorem petersson_self_re_pos_of_ne_zero (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : bddAut V) (hf : f ≠ 0) :
    0 < (l2 ν 𝓕 (f : GA D V → ℂ) f).re := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  obtain ⟨hc, hi, C, hC⟩ := zero_one_mem_gammaSet_one f
  have key : l2 ν 𝓕 (f : GA D V → ℂ) f =
      ((∫ x in 𝓕, Complex.normSq ((f : GA D V → ℂ) x) ∂ν : ℝ) : ℂ) := by
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Complex.mul_conj]
    exact integral_ofReal
  rw [key, Complex.ofReal_re]
  have hint : IntegrableOn (fun x => Complex.normSq ((f : GA D V → ℂ) x)) 𝓕 ν :=
    integrableOn_fundamentalDomain_of_bounded hν h𝓕 (Complex.continuous_normSq.comp hc) (C * C) fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hC g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _) hint]
  set U : Set (GA D V) := {x | (f : GA D V → ℂ) x ≠ 0} with hUdef
  have hsupp : Function.support (fun x => Complex.normSq ((f : GA D V → ℂ) x)) = U := by
    ext x
    simp [U, Complex.normSq_eq_zero]
  rw [hsupp]
  have hU : IsOpen U := isOpen_ne_fun hc continuous_const
  have hne : U.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hf
    apply Subtype.ext
    funext x
    by_contra hx
    have hx' : x ∈ U := hx
    rw [hE] at hx'
    exact hx'
  refine pos_iff_ne_zero.2 fun h0 => (hU.measure_pos ν hne).ne' ?_
  have hsub : U ⊆ {x | ¬ ∃ γ : GQ V, γ • x ∈ 𝓕} ∪
      ⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) := by
    intro x hx
    by_cases hx' : ∃ γ : GQ V, γ • x ∈ 𝓕
    · obtain ⟨γ, hγ⟩ := hx'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩)
      show (f : GA D V → ℂ) ((γ : GA D V) * x) ≠ 0
      rw [hi γ γ.2]
      exact hx
    · exact Or.inl hx'
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 h𝓕.ae_covers) ?_)
  refine measure_iUnion_null fun γ => ?_
  rw [measure_preimage_mul]
  exact h0

theorem petersson_bounded_automorphic_right_translation_invariant (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (g : GA D V) (f f₂ : bddAut V) :
    l2 ν 𝓕 (bddRep V g f : GA D V → ℂ) (bddRep V g f₂ : GA D V → ℂ) = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V ν hν).1
  obtain ⟨-, hi, -⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨-, hi₂, -⟩ := zero_one_mem_gammaSet_one f₂
  rw [coe_bddRep, coe_bddRep]
  simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 g
    (fun x => (f : GA D V → ℂ) x * starRingEnd ℂ ((f₂ : GA D V → ℂ) x))
    fun γ hγ x => by simp only [hi γ hγ, hi₂ γ hγ]

end

theorem bddRep_unitarisable_and_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  intro D V
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  refine ⟨?_, fun ν 𝓕 hν h𝓕 f₂ => ?_⟩
  · have hH : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨𝓕, h𝓕⟩ :=
      (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar hH).2
    obtain ⟨B, hB⟩ := exists_form_bddAut hH h𝓕
    unfold IsUnitarisable
    refine ⟨B, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · rw [hB, hB]
      simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet]
      rw [← integral_conj]
      congr 1
      funext x
      rw [map_mul, Complex.conj_conj, mul_comm]
    · rw [hB]
      exact petersson_self_re_pos_of_ne_zero hH h𝓕 v hv
    · rw [hB, hB]
      exact petersson_bounded_automorphic_right_translation_invariant hH h𝓕 g v w
  · obtain ⟨B, hB⟩ := exists_form_bddAut hν h𝓕
    refine ⟨{ toFun := fun f => B f f₂, map_add' := fun a b => by simp, map_smul' := fun c a => by simp },
      fun f => hB f f₂, fun f => ?_⟩
    obtain ⟨-, -, C, hC⟩ := zero_one_mem_gammaSet_one f
    obtain ⟨-, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
    have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
    refine ⟨C * C₂ * (ν 𝓕).toReal, fun g => ?_⟩
    show ‖B (bddRep V g f) f₂‖ ≤ _
    rw [hB, coe_bddRep]
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

end GlobalTheory.FinZeta

end
