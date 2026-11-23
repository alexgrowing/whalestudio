import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.Slice

open MvPolynomial GlobalTheory.Capelli

variable {σ σ₀ : Type} (ι : σ₀ → σ)

abbrev Outer := {v : σ // v ∉ Set.range ι}

noncomputable def sliceVar (v : σ) : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) := by
  classical
  exact if h : v ∈ Set.range ι then C (X h.choose) else X ⟨v, h⟩

noncomputable def slice : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) :=
  aeval (sliceVar ι)

variable {ι}

theorem slice_X_inner (hι : Function.Injective ι) (u : σ₀) : slice ι (X (ι u)) = C (X u) := by
  have h : ι u ∈ Set.range ι := ⟨u, rfl⟩
  simp only [slice, aeval_X, sliceVar, dif_pos h]
  rw [hι h.choose_spec]

theorem slice_X_outer {v : σ} (hv : v ∉ Set.range ι) : slice ι (X v) = X ⟨v, hv⟩ := by
  simp only [slice, aeval_X, sliceVar, dif_neg hv]

theorem slice_C (a : ℂ) : slice ι (C a) = C (C a) := by
  simp [slice, aeval_C, MvPolynomial.algebraMap_apply]

variable (ι)

noncomputable def coefAt (t : Outer ι →₀ ℕ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ₀ ℂ where
  toFun Q := coeff t (slice ι Q)
  map_add' _ _ := by simp
  map_smul' c Q := by simp [coeff_smul]

variable {ι}

theorem coefAt_X_mul (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) (u : σ₀)
    (Q : MvPolynomial σ ℂ) : coefAt ι t (X (ι u) * Q) = X u * coefAt ι t Q := by
  simp [coefAt, map_mul, slice_X_inner hι, coeff_C_mul]

theorem coefAt_pderiv (hι : Function.Injective ι) (u : σ₀) (Q : MvPolynomial σ ℂ) :
    ∀ t, coefAt ι t (pderiv (ι u) Q) = pderiv u (coefAt ι t Q) := by
  classical
  simp only [coefAt, LinearMap.coe_mk, AddHom.coe_mk]
  induction Q using MvPolynomial.induction_on with
  | C a => intro t; simp only [pderiv_C, map_zero, coeff_zero, slice_C, coeff_C]; split_ifs <;> simp
  | add p q hp hq => intro t; simp [hp, hq]
  | mul_X p v hp =>
    intro t
    by_cases hv : v ∈ Set.range ι
    · obtain ⟨w, rfl⟩ := hv
      by_cases huw : w = u
      · subst huw
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X, coeff_C_mul,
          mul_comm (slice ι p) (C (X w))]
        ring
      · have h1 : ι u ≠ ι w := fun h => huw (hι h).symm
        have h2 : u ≠ w := fun h => huw h.symm
        simp [Derivation.leibniz, map_mul, slice_X_inner hι, hp, pderiv_X,
          Pi.single_apply, h1, h2, coeff_C_mul, mul_comm (slice ι p) (C (X w))]
    · have h1 : ι u ≠ v := fun h => hv ⟨u, h⟩
      simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul, pderiv_X, Pi.single_apply,
        if_neg h1.symm, mul_zero, zero_add, slice_X_outer hv]
      rw [coeff_X_mul', coeff_mul_X']
      split_ifs
      · rw [hp]
      · simp

theorem coefAt_jointTop (hι : Function.Injective ι) (t : Outer ι →₀ ℕ) {k l N : ℕ}
    (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ) (α : Fin k → ℂ)
    (β : Fin l → ℂ) (P : MvPolynomial σ ℂ)
    (h : GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P) :
    GlobalTheory.CompactHarm.JointTop z y κ α β (coefAt ι t P) := by
  have hm : ∀ i j, coefAt ι t (mixedOp ℂ (ι ∘ z) (ι ∘ y) i j P) =
      mixedOp ℂ z y i j (coefAt ι t P) := fun i j => by
    simp only [mixedOp_apply, map_sub, map_sum, Function.comp_apply, coefAt_X_mul hι,
      coefAt_pderiv hι]
  have hr : ∀ {K : ℕ} (w : Fin K × Fin N → σ₀) (a b : Fin K),
      coefAt ι t (rowOp ℂ (ι ∘ w) a b P) = rowOp ℂ w a b (coefAt ι t P) := fun w a b => by
    simp only [rowOp_apply, map_sum, Function.comp_apply, coefAt_X_mul hι, coefAt_pderiv hι]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' hc => ?_, fun c => ?_, fun d d' hd => ?_,
    fun d => ?_, fun c d => ?_⟩
  · rw [← hm, h1 i j hij, map_zero]
  · rw [← hm, h2 i, map_smul]
  · rw [← hr, h3 c c' hc, map_zero]
  · rw [← hr, h4 c, map_smul]
  · rw [← hr, h5 d d' hd, map_zero]
  · rw [← hr, h6 d, map_smul]
  · have := congrArg (coefAt ι t) (h7 c d)
    simpa only [map_sum, Function.comp_apply, coefAt_pderiv hι, map_zero] using this

variable (ι)

noncomputable def unslice : MvPolynomial (Outer ι) (MvPolynomial σ₀ ℂ) →+* MvPolynomial σ ℂ :=
  eval₂Hom (rename ι).toRingHom (fun r => X r.1)

variable {ι}

theorem unslice_slice_X (hι : Function.Injective ι) (v : σ) : unslice ι (slice ι (X v)) = X v := by
  by_cases hv : v ∈ Set.range ι
  · obtain ⟨w, rfl⟩ := hv
    rw [slice_X_inner hι]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
  · rw [slice_X_outer hv]
    simp only [unslice, coe_eval₂Hom, eval₂_X]

theorem unslice_slice (hι : Function.Injective ι) (Q : MvPolynomial σ ℂ) :
    unslice ι (slice ι Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [slice_C]
    simp only [unslice, coe_eval₂Hom, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, unslice_slice_X hι]

theorem slice_decomp (hι : Function.Injective ι) (P : MvPolynomial σ ℂ) :
    P = ∑ t ∈ (slice ι P).support,
      rename ι (coefAt ι t P) * t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e) := by
  conv_lhs => rw [← unslice_slice hι P, (slice ι P).as_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [unslice, eval₂_monomial, coefAt]

theorem vars_outer_prod (t : Outer ι →₀ ℕ) :
    ∀ v ∈ (t.prod (fun r e => (X r.1 : MvPolynomial σ ℂ) ^ e)).vars, v ∉ Set.range ι := by
  classical
  intro v hv
  obtain ⟨r, -, hr⟩ := Finset.mem_biUnion.1 (vars_prod _ hv)
  have := vars_pow _ _ hr
  rw [vars_X, Finset.mem_singleton] at this
  exact this ▸ r.2

noncomputable def outerEmb : (Outer ι →₀ ℕ) ↪ (σ →₀ ℕ) :=
  ⟨Finsupp.mapDomain Subtype.val, Finsupp.mapDomain_injective Subtype.val_injective⟩

noncomputable def outerBack (i : σ →₀ ℕ) : Outer ι →₀ ℕ :=
  Finsupp.comapDomain Subtype.val i Subtype.val_injective.injOn

theorem outerBack_emb (t : Outer ι →₀ ℕ) : outerBack (outerEmb t) = t :=
  Finsupp.comapDomain_mapDomain _ Subtype.val_injective t

end GlobalTheory.Slice

open GlobalTheory.Slice in
theorem GlobalTheory.jointTop_slice : ∀ {σ σ₀ : Type} [DecidableEq σ] (ι : σ₀ → σ), Function.Injective ι →
    ∀ {k l N : ℕ} (z : Fin k × Fin N → σ₀) (y : Fin l × Fin N → σ₀) (κ : Fin N → ℂ)
    (α : Fin k → ℂ) (β : Fin l → ℂ) (P : MvPolynomial σ ℂ),
    GlobalTheory.CompactHarm.JointTop (ι ∘ z) (ι ∘ y) κ α β P →
    ∃ (s : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → MvPolynomial σ₀ ℂ) (g : (σ →₀ ℕ) → MvPolynomial σ ℂ),
      P = ∑ i ∈ s, MvPolynomial.rename ι (f i) * g i ∧
      (∀ i ∈ s, GlobalTheory.CompactHarm.JointTop z y κ α β (f i)) ∧
      ∀ i ∈ s, ∀ v ∈ (g i).vars, v ∉ Set.range ι := by
  intro σ σ₀ _ ι hι k l N z y κ α β P hP
  refine ⟨(slice ι P).support.map (outerEmb (ι := ι)), fun i => coefAt ι (outerBack (ι := ι) i) P,
    fun i => (outerBack (ι := ι) i).prod (fun r n => (MvPolynomial.X r.1 : MvPolynomial σ ℂ) ^ n), ?_, ?_, ?_⟩
  · rw [Finset.sum_map]
    simp only [outerBack_emb]
    exact slice_decomp hι P
  · intro i _
    exact coefAt_jointTop hι _ z y κ α β P hP
  · intro i _
    exact vars_outer_prod _
