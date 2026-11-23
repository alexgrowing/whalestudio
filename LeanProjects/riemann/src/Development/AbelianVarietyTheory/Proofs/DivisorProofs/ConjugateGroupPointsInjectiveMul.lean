import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.UnrEuler.IdealPart

theorem nrm_eq_prod {E : Type} [Field E] [NumberField E] {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, FractionalIdeal.count E w 𝔞 ≠ 0 → w ∈ S) :
    nrm 𝔞 = ∏ w ∈ S, (Ideal.absNorm w.asIdeal : ℝ) ^ FractionalIdeal.count E w 𝔞 := by
  have h1 := FractionalIdeal.finprod_heightOneSpectrum_factorization' E h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)] at h1
  · unfold nrm
    conv_lhs => rw [← h1]
    rw [map_prod]
    simp only [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rfl
  · intro w hw
    refine Finset.mem_coe.2 (hS w fun h0 => hw ?_)
    simp [h0]

theorem absNorm_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
  have : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem nrm_cpow_eq_prod {E : Type} [Field E] [NumberField E] {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, FractionalIdeal.count E w 𝔞 ≠ 0 → w ∈ S) (s : ℂ) :
    (nrm 𝔞 : ℂ) ^ (-s) = ∏ w ∈ S, npow w (-(s * (FractionalIdeal.count E w 𝔞 : ℂ))) := by
  have hp := nrm_pos h
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le, nrm_eq_prod h S hS,
    Real.log_prod (fun w _ => (zpow_pos (absNorm_pos w) _).ne'), Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := absNorm_pos w
  have e : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℝ) : ℂ) := by simp
  unfold npow
  rw [e, Complex.cpow_def_of_ne_zero (by exact_mod_cast hw.ne'), ← Complex.ofReal_log hw.le, Real.log_zpow]
  congr 1
  push_cast
  ring

theorem hasProd_idealPart : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (T : Set (Pl F)) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → FractionalIdeal.count E w 𝔞 = 0) → ∀ s : ℂ, HasProd (fun v : {v : Pl F // v ∉ T} => ∏ w ∈ aboveF (L := E) F v.1, ((val ν w ^ FractionalIdeal.count E w 𝔞 : ℂˣ) : ℂ) * npow w (-(s * (FractionalIdeal.count E w 𝔞 : ℂ)))) (((idealVal ν 𝔞 : ℂˣ) : ℂ) * (nrm 𝔞 : ℂ) ^ (-s)) := by
  intro F E _ _ _ _ _ ν T 𝔞 h hT s
  classical
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := E) 𝔞)
  have hfin' : {v : {v : Pl F // v ∉ T} | v.1 ∈ (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)) ''
      {w | ¬ FractionalIdeal.count E w 𝔞 = 0}}.Finite :=
    (hfin.image _).preimage Subtype.val_injective.injOn
  set V := hfin'.toFinset with hV
  set S := V.biUnion (fun v => aboveF (L := E) F v.1) with hSdef
  have hS : ∀ w, FractionalIdeal.count E w 𝔞 ≠ 0 → w ∈ S := fun w hw =>
    Finset.mem_biUnion.2 ⟨⟨w.under (𝓞 F), fun hh => hw (hT w hh)⟩, hfin'.mem_toFinset.2 ⟨w, hw, rfl⟩,
      GlobalTheory.LFun.mem_aboveF.2 rfl⟩
  have hval : idealVal ν 𝔞 = ∏ w ∈ S, val ν w ^ FractionalIdeal.count E w 𝔞 := by
    unfold idealVal
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => Finset.mem_coe.2 (hS w fun h0 => hw ?_)
    simp [h0]
  rw [hval, nrm_cpow_eq_prod h S hS s, Units.coe_prod, ← Finset.prod_mul_distrib, hSdef, Finset.prod_biUnion]
  · refine hasProd_prod_of_ne_finset_one fun v hv => Finset.prod_eq_one fun w hw => ?_
    have h0 : FractionalIdeal.count E w 𝔞 = 0 := by
      by_contra h0
      exact hv (hfin'.mem_toFinset.2 ⟨w, h0, GlobalTheory.LFun.mem_aboveF.1 hw⟩)
    simp [h0, npow]
  · intro v _ v' _ hne
    refine Finset.disjoint_left.2 fun w h1 h2 => hne (Subtype.ext ?_)
    exact (GlobalTheory.LFun.mem_aboveF.1 h1).symm.trans (GlobalTheory.LFun.mem_aboveF.1 h2)

end GlobalTheory.UnrEuler.IdealPart
