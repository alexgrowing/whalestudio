import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetGlActionCompactPreservesJointHarmonics
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommonEigenvector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.KHwExist

open scoped Classical

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.LowestKType

variable {D : D7} {n m : ℕ}

def pol (τ : D.what₂.Tau) (a b : Fin m) : Derivation ℂ (PolF D m n) (PolF D m n) :=
  ∑ j : Fin n, (X (τ, a, j) : PolF D m n) • pderiv (τ, b, j)

theorem pol_apply (τ : D.what₂.Tau) (a b : Fin m) (Q : PolF D m n) :
    pol τ a b Q = ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q := by
  have e := map_sum (Derivation.coeFnAddMonoidHom : Derivation ℂ (PolF D m n) (PolF D m n) →+ _)
    (fun j : Fin n => (X (τ, a, j) : PolF D m n) • pderiv (τ, b, j)) Finset.univ
  simp only [Derivation.coeFnAddMonoidHom_apply] at e
  rw [pol, e, Finset.sum_apply]
  simp [Derivation.smul_apply]

theorem pol_X (τ : D.what₂.Tau) (a b : Fin m) (t : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    (pol τ a b (X (t, i, j)) : PolF D m n) = if t = τ ∧ i = b then X (τ, a, j) else 0 := by
  classical
  rw [pol_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases h : t = τ ∧ i = b
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => if_neg ?_
    rintro ⟨rfl, rfl, rfl⟩; exact h ⟨rfl, rfl⟩

theorem pol_comm (τ' τ : D.what₂.Tau) (c a b : Fin m) :
    ⁅(pol τ' c c : Derivation ℂ (PolF D m n) (PolF D m n)), (pol τ a b : Derivation ℂ (PolF D m n) (PolF D m n))⁆ =
      (if τ' = τ then ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ) else 0) • pol τ a b := by
  classical
  apply MvPolynomial.derivation_ext
  rintro ⟨t, i, j⟩
  rw [Derivation.commutator_apply, Derivation.smul_apply, pol_X, pol_X]
  by_cases h1 : t = τ ∧ i = b <;> by_cases h2 : t = τ' ∧ i = c
  · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
    simp only [pol_X, and_self, if_true, true_and]
    by_cases hai : a = i
    · subst hai; simp
    · simp [hai, Ne.symm hai]
  · rw [if_pos h1, if_neg h2, map_zero, sub_zero, pol_X]
    obtain ⟨rfl, rfl⟩ := h1
    by_cases h3 : t = τ' ∧ a = c
    · obtain ⟨rfl, rfl⟩ := h3
      simp only [and_self, if_true]
      have : i ≠ a := fun e => h2 ⟨rfl, e⟩
      simp [Ne.symm this]
    · rw [if_neg h3]
      by_cases h4 : t = τ'
      · subst h4
        have : c ≠ a := fun e => h3 ⟨rfl, e.symm⟩
        have : c ≠ i := fun e => h2 ⟨rfl, e.symm⟩
        simp [*]
      · simp [Ne.symm h4]
  · rw [if_neg h1, if_pos h2, map_zero, zero_sub, pol_X]
    obtain ⟨rfl, rfl⟩ := h2
    rw [if_neg h1, neg_zero, smul_zero]
  · rw [if_neg h1, if_neg h2, map_zero, map_zero, sub_zero, smul_zero]

end GlobalTheory.KHwExist

namespace GlobalTheory.KHwExist

open scoped Classical

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.LowestKType

variable {D : D7} {n m : ℕ}

theorem kop_pos (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) (ha : (a : ℕ) < w.p τ)
    (hb : (b : ℕ) < w.p τ) :
    kop w τ a b = ((pol τ a b : Derivation ℂ (PolF D m n) (PolF D m n)) : Module.End ℂ (PolF D m n)) +
      (if a = b then ((n : ℂ) / 2) else 0) • 1 := by
  refine LinearMap.ext fun Q => ?_
  rw [kop, GlobalTheory.CompactHarm.up_eq τ _ a b (by simpa using ha) (by simpa using hb)]
  simp only [LinearMap.add_apply, Derivation.coeFn_coe, pol_apply, LinearMap.smul_apply, Module.End.one_apply]
  split_ifs <;> simp

theorem kop_neg (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) (ha : ¬ (a : ℕ) < w.p τ)
    (hb : ¬ (b : ℕ) < w.p τ) :
    kop w τ a b = -((pol τ b a : Derivation ℂ (PolF D m n) (PolF D m n)) : Module.End ℂ (PolF D m n)) -
      (if a = b then ((n : ℂ) / 2) else 0) • 1 := by
  refine LinearMap.ext fun Q => ?_
  rw [kop, GlobalTheory.CompactHarm.dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
  simp only [GlobalTheory.CompactHarm.pd_X_mul, Finset.sum_add_distrib, Prod.mk.injEq, true_and, and_true,
    LinearMap.sub_apply, LinearMap.neg_apply, Derivation.coeFn_coe, pol_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    module
  · simp [hab, Ne.symm hab]

end GlobalTheory.KHwExist

namespace GlobalTheory.KHwExist

open scoped Classical

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.LowestKType

variable {D : D7} {n m : ℕ}

abbrev polE (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  ((pol τ a b : Derivation ℂ (PolF D m n) (PolF D m n)) : Module.End ℂ (PolF D m n))

theorem polE_comm (τ' τ : D.what₂.Tau) (c a b : Fin m) :
    (polE τ' c c : Module.End ℂ (PolF D m n)) * polE τ a b - polE τ a b * polE τ' c c =
      (if τ' = τ then ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ) else 0) • polE τ a b := by
  rw [← Ring.lie_def, polE, polE, ← Derivation.commutator_coe_linear_map, pol_comm]
  rfl

theorem polE_commute (τ' τ : D.what₂.Tau) (c c' : Fin m) :
    Commute (polE τ' c c : Module.End ℂ (PolF D m n)) (polE τ c' c') := by
  have h := polE_comm (n := n) τ' τ c c' c'
  rw [sub_self, ite_self, zero_smul, sub_eq_zero] at h
  exact h

theorem comm_aff {A B : Module.End ℂ (PolF D m n)} (h : Commute A B) (u v d e : ℂ) :
    Commute (u • A + d • 1) (v • B + e • 1) := by
  apply Commute.add_left
  · apply Commute.add_right
    · exact (h.smul_left u).smul_right v
    · exact ((Commute.one_right _).smul_right e).smul_left u
  · exact (((Commute.one_left B).smul_left d).smul_right v).add_right
      (((Commute.one_left (1 : Module.End ℂ (PolF D m n))).smul_left d).smul_right e)

theorem kop_diag (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (c : Fin m) :
    kop w τ c c = (if (c : ℕ) < w.p τ then (1 : ℂ) else -1) • polE τ c c +
      (if (c : ℕ) < w.p τ then (n : ℂ) / 2 else -((n : ℂ) / 2)) • 1 := by
  by_cases hc : (c : ℕ) < w.p τ
  · rw [kop_pos w τ c c hc hc]; simp [hc]
  · rw [kop_neg w τ c c hc hc]; simp only [hc, if_false, if_true, neg_smul, one_smul]; abel

theorem kop_diag_commute (w : GlobalTheory.ExportSeries.Weight D n) (τ τ' : D.what₂.Tau) (c c' : Fin m) :
    kop w τ c c * kop w τ' c' c' = kop w τ' c' c' * kop w τ c c := by
  rw [kop_diag, kop_diag]
  exact (comm_aff (polE_commute τ τ' c c') _ _ _ _).eq

theorem kop_comm (w : GlobalTheory.ExportSeries.Weight D n) (τ' τ : D.what₂.Tau) (c a b : Fin m) (hC : Cpt w τ a b)
    (hab : a ≠ b) :
    kop w τ' c c * kop w τ a b - kop w τ a b * kop w τ' c c =
      (if τ' = τ then ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ) else 0) • kop w τ a b := by
  have hC' : ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ) := hC
  have k1 : ∀ (A B : Module.End ℂ (PolF D m n)) (u d : ℂ), (u • A + d • 1) * B - B * (u • A + d • 1) =
      u • (A * B - B * A) := by
    intro A B u d
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub]
    abel
  rw [kop_diag, k1]
  by_cases ha : (a : ℕ) < w.p τ
  · have hb := hC'.1 ha
    rw [kop_pos w τ a b ha hb, if_neg hab, zero_smul, add_zero, polE_comm]
    by_cases hc : (c : ℕ) < w.p τ'
    · rw [if_pos hc, one_smul]
    · rw [if_neg hc]
      by_cases ht : τ' = τ
      · subst ht
        have h1 : c ≠ a := fun e => hc (e ▸ ha)
        have h2 : c ≠ b := fun e => hc (e ▸ hb)
        simp [h1, h2]
      · simp [ht]
  · have hb : ¬ (b : ℕ) < w.p τ := fun h => ha (hC'.2 h)
    rw [kop_neg w τ a b ha hb, if_neg hab, zero_smul, sub_zero, mul_neg, neg_mul, sub_neg_eq_add,
      neg_add_eq_sub, ← neg_sub, polE_comm, smul_neg, smul_neg, smul_smul]
    by_cases hc : (c : ℕ) < w.p τ'
    · rw [if_pos hc]
      by_cases ht : τ' = τ
      · subst ht
        have h1 : c ≠ a := fun e => ha (e ▸ hc)
        have h2 : c ≠ b := fun e => hb (e ▸ hc)
        simp [h1, h2]
      · simp [ht]
    · rw [if_neg hc]
      congr 2
      split_ifs <;> ring

end GlobalTheory.KHwExist

namespace GlobalTheory.KHwExist

theorem exists_common_eigenvector {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (H : ι → Module.End ℂ V) (hH : ∀ i j, H i * H j = H j * H i) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (hE : ∀ i, ∀ x ∈ E, H i x ∈ E) (hE0 : E ≠ ⊥) :
    ∃ v ∈ E, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, H i v = c • v := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvector.common_eigenvector
  | exact _root_.GlobalTheory.CommonEigenvector.common_eigenvector
  | (apply _root_.GlobalTheory.CommonEigenvector.common_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvector.common_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvector.common_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvector.common_eigenvector ..)

theorem exists_hw_of_height {V ι ρ : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (H : ι → Module.End ℂ V) (hH : ∀ i j, H i * H j = H j * H i)
    (h : Module.End ℂ V) (hh : ∀ i, h * H i = H i * h)
    (R : ρ → Module.End ℂ V) (β : ρ → ℝ) (hβ : ∀ r, 0 < β r) (hR : ∀ r, h * R r - R r * h = (β r : ℂ) • R r)
    (T : Submodule ℂ V) [FiniteDimensional ℂ T] (hT0 : T ≠ ⊥)
    (hTH : ∀ i, ∀ x ∈ T, H i x ∈ T) (hTh : ∀ x ∈ T, h x ∈ T) (hTR : ∀ r, ∀ x ∈ T, R r x ∈ T) :
    ∃ v ∈ T, v ≠ 0 ∧ (∀ r, R r v = 0) ∧ ∀ i, ∃ c : ℂ, H i v = c • v := by
  classical
  haveI : Nontrivial T := Submodule.nontrivial_iff_ne_bot.2 hT0
  let hT : Module.End ℂ T := h.restrict hTh
  have hfin : {μ | Module.End.HasEigenvalue hT μ}.Finite := Module.End.finite_hasEigenvalue hT
  obtain ⟨μ0, hμ0⟩ := Module.End.exists_eigenvalue hT
  obtain ⟨z, hz, hzmax⟩ := Set.exists_max_image _ (fun μ : ℂ => μ.re) hfin ⟨μ0, hμ0⟩
  let E : Submodule ℂ V := T ⊓ LinearMap.ker (h - z • 1)
  have memE : ∀ x, x ∈ E ↔ x ∈ T ∧ h x = z • x := by
    intro x; simp [E, sub_eq_zero]
  haveI : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hE0 : E ≠ ⊥ := by
    obtain ⟨x, hx⟩ := (hz : Module.End.HasEigenvalue hT z).exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    rw [Submodule.ne_bot_iff]
    refine ⟨x, (memE _).2 ⟨x.2, ?_⟩, fun h0 => hx.2 (Subtype.ext h0)⟩
    have := congrArg Subtype.val hx.1
    rwa [LinearMap.coe_restrict_apply] at this
  have hkill : ∀ r, ∀ x ∈ E, R r x = 0 := by
    intro r x hx
    obtain ⟨hxT, hxz⟩ := (memE x).1 hx
    by_contra hne
    have e1 : h (R r x) = (z + β r) • R r x := by
      have := LinearMap.congr_fun (hR r) x
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hxz, map_smul] at this
      rw [add_smul, ← this]; abel
    have hev : Module.End.HasEigenvalue hT (z + β r) := by
      refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨R r x, hTR r x hxT⟩) ?_
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      refine ⟨Subtype.ext ?_, fun h0 => hne (congrArg Subtype.val h0)⟩
      rw [LinearMap.coe_restrict_apply]
      exact e1
    have := hzmax _ hev
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith [hβ r]
  have hEH : ∀ i, ∀ x ∈ E, H i x ∈ E := by
    intro i x hx
    obtain ⟨hxT, hxz⟩ := (memE x).1 hx
    refine (memE _).2 ⟨hTH i x hxT, ?_⟩
    have := LinearMap.congr_fun (hh i) x
    simp only [Module.End.mul_apply] at this
    rw [this, hxz, map_smul]
  obtain ⟨v, hvE, hv0, hv⟩ := exists_common_eigenvector H hH E hEH hE0
  exact ⟨v, ((memE v).1 hvE).1, hv0, fun r => hkill r v hvE, hv⟩

end GlobalTheory.KHwExist

namespace GlobalTheory.KHwExist

open scoped Classical

open GlobalTheory.LowestKType

theorem exists_kHwMap : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (W : Type) [AddCommGroup W] [Module ℂ W] (T : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), FiniteDimensional ℂ T → T ≠ ⊥ → (∀ ψ ∈ T, ∀ (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b → GlobalTheory.LowestKType.kop w τ a b ∘ₗ ψ ∈ T) → ∃ ψ ∈ T, ψ ≠ 0 ∧ GlobalTheory.LowestKType.IsKHwMap w ψ := by
  intro D n m w W _ _ T hfd hT0 hst
  let post : Module.End ℂ (PolF D m n) → Module.End ℂ (W →ₗ[ℂ] PolF D m n) :=
    fun f => LinearMap.llcomp ℂ W (PolF D m n) (PolF D m n) f
  have post_mul : ∀ f g, post (f * g) = post f * post g := fun f g => LinearMap.ext fun ψ => rfl
  have post_sub : ∀ f g, post (f - g) = post f - post g := fun f g => map_sub _ f g
  have post_smul : ∀ (c : ℂ) f, post (c • f) = c • post f := fun c f => map_smul _ c f
  let H : D.what₂.Tau × Fin m → Module.End ℂ (W →ₗ[ℂ] PolF D m n) := fun x => post (kop w x.1 x.2 x.2)
  let ρ := {x : D.what₂.Tau × Fin m × Fin m // Cpt w x.1 x.2.1 x.2.2 ∧ x.2.1 < x.2.2}
  let R : ρ → Module.End ℂ (W →ₗ[ℂ] PolF D m n) := fun r => post (kop w r.1.1 r.1.2.1 r.1.2.2)
  let h : Module.End ℂ (W →ₗ[ℂ] PolF D m n) := ∑ x : D.what₂.Tau × Fin m, (-((x.2 : ℕ) : ℂ)) • H x
  have hHc : ∀ i j, H i * H j = H j * H i := fun i j => by
    simp only [H, ← post_mul, kop_diag_commute]
  have hcomm : ∀ (r : ρ) (x : D.what₂.Tau × Fin m), H x * R r - R r * H x =
      (if x.1 = r.1.1 then ((if x.2 = r.1.2.1 then 1 else 0) - (if x.2 = r.1.2.2 then 1 else 0) : ℂ) else 0) • R r := by
    intro r x
    simp only [H, R, ← post_mul, ← post_sub, ← post_smul]
    rw [kop_comm w x.1 r.1.1 x.2 r.1.2.1 r.1.2.2 r.2.1 (ne_of_lt r.2.2)]
  have hh : ∀ i, h * H i = H i * h := by
    intro i
    simp only [h, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hHc]
  have hR : ∀ r : ρ, h * R r - R r * h = ((((r.1.2.2 : ℕ) : ℝ) - ((r.1.2.1 : ℕ) : ℝ) : ℝ) : ℂ) • R r := by
    intro r
    simp only [h, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← Finset.sum_sub_distrib,
      ← smul_sub, hcomm, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [Fintype.sum_prod_type]
    simp [mul_sub, Finset.sum_sub_distrib]
    push_cast; ring
  obtain ⟨v, hvT, hv0, hvR, hvH⟩ := exists_hw_of_height H hHc h hh R
    (fun r => ((r.1.2.2 : ℕ) : ℝ) - ((r.1.2.1 : ℕ) : ℝ))
    (fun r => by have := r.2.2; simp only [sub_pos, Nat.cast_lt]; exact this) hR T hT0
    (fun i x hx => hst x hx i.1 i.2 i.2 Iff.rfl)
    (fun x hx => by
      simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
      exact T.sum_mem fun i _ => T.smul_mem _ (hst x hx i.1 i.2 i.2 Iff.rfl))
    (fun r x hx => hst x hx r.1.1 r.1.2.1 r.1.2.2 r.2.1)
  refine ⟨v, hvT, hv0, fun τ a b hC hab => hvR ⟨(τ, a, b), hC, hab⟩, fun τ a => hvH (τ, a)⟩

end GlobalTheory.KHwExist
