import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatSelfDual

variable {D : D7}

theorem cF_eq_conj (D : D7) (x : D.host.E) : cF D x = D.host.conj x :=
  bridge_star_holds D.R D.host x

noncomputable def frameForm (V : HSp D) (v y : Fin V.rank → D.host.E) : D.host.E :=
  ∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)

theorem frameForm_smul_left (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (e • v) y = e * frameForm V v y := by
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_smul_right (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (e • y) = D.host.conj e * frameForm V v y := by
  rw [← cF_eq_conj]
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_add_left (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V (v + w) y = frameForm V v y + frameForm V w y := by
  simp only [frameForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem frameForm_add_right (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V v (w + y) = frameForm V v w + frameForm V v y := by
  simp only [frameForm, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem frameForm_int_smul_left (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (c • v) y = c • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c v, frameForm_smul_left, Algebra.smul_def]

theorem frameForm_int_smul_right (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (c • y) = (D.host.conj • c) • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c y, frameForm_smul_right, Algebra.smul_def, algebraMap_conj_smul]

theorem mem_iff_trace (D : D7) (z : D.host.E) :
    z ∈ D.host.AA * D.host.AAbar ↔
      ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  constructor
  · intro hz a
    have h : a • z ∈ NAA D := Submodule.smul_mem _ a hz
    rw [Algebra.smul_def] at h
    exact trace_int_of_mem hP D h
  · intro h
    have hz : D.host.xi0 * z ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mem_dual
        (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [FractionalIdeal.mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨n, hn⟩ := h c
      rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
      exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
    rw [← dual_eq hP D] at hz
    have h4 := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
        FractionalIdeal.spanSingleton_one, one_mul]
    rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  intro h
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem selfDual_one (V : HSp D) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V 1, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V 1 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  have hAb := AAbar_ne_zero D
  have hC : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, frameForm V v y ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V :=
    (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.2.2.2.2.2
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2]
  constructor
  · intro h
    have h5 : ∀ y0 ∈ latC V, frameForm V v y0 ∈ D.host.AA := by
      intro y0 hy0
      have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) *
          D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
        rw [FractionalIdeal.spanSingleton_mul_le_iff]
        intro b hb
        have := h (D.host.conj b • y0) (Submodule.subset_span ⟨_, conj_mem_AA D hb, y0, hy0, rfl⟩)
        rw [frameForm_smul_right, conj_conj, mul_comm b] at this
        exact this
      have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) ≤
          D.host.AA := by
        calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0)
            = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
                (frameForm V v y0) * D.host.AAbar) := by
              rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
          _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
          _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)
    have h6 : ∀ c ∈ D.host.AA⁻¹, c • v ∈ latC V := by
      intro c hc
      refine (hC _).1 fun y hy => ?_
      rw [frameForm_smul_left, ← inv_mul_cancel₀ hAA]
      exact FractionalIdeal.mul_mem_mul hc (h5 y hy)
    have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
      intro e he
      refine FractionalIdeal.mul_induction_on (C := fun e => e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x}) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
      · show (a * c) • v ∈ _
        rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • v, h6 c hc, rfl⟩
      · show (u + w) • v ∈ _
        rw [add_smul]; exact add_mem hu hw
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    rwa [one_smul] at this
  · intro hv w hw
    show frameForm V v w ∈ NAA D
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hv
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, hb, y, hy, rfl⟩ := hw
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((hC x).2 hx y hy)
        rw [frameForm_smul_left, frameForm_smul_right, ← hr, ← mul_assoc, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
      | zero => simp [frameForm]
      | add w w' _ _ h h' => rw [frameForm_add_right]; exact add_mem h h'
      | smul c w _ h => rw [frameForm_int_smul_right]; exact Submodule.smul_mem _ _ h
    | zero => simp [frameForm]
    | add v v' _ _ h h' => rw [frameForm_add_left]; exact add_mem h h'
    | smul c v _ h => rw [frameForm_int_smul_left]; exact Submodule.smul_mem _ _ h

theorem selfDual (V : HSp D) (g : GA D V) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V g, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V g := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg, hspan, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  have hlat := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E V.rank (latG V 1) (cF D) V.gramᵀ
    (D.host.AA * D.host.AAbar) (finHom V g) hfg hspan hcc hG hdet
    (mul_ne_zero (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (AAbar_ne_zero D))
    (selfDual_one V) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V g).1 v
  rw [← hlat] at key
  exact key

end GlobalTheory.Member.LatSelfDual

namespace GlobalTheory.Member

open LatSelfDual

theorem latG_selfDual : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  intro D V g J hJ
  subst hJ
  refine ⟨mem_iff_trace D, selfDual V g, fun v => ?_⟩
  have hcc := (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.1
  have hh : ∀ y, herm (-V.gramᵀ) v y = - frameForm V v y := by
    intro y
    simp only [herm, frameForm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  have ht : ∀ y, (∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * frameForm V v y) = n := by
    intro y
    rw [hh, neg_neg, mul_neg, map_neg]
    exact ⟨fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩,
      fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, hn]⟩⟩
  simp only [ht]
  rw [← selfDual V g v]
  constructor
  · intro h y hy
    refine (mem_iff_trace D _).2 fun a => ?_
    have h1 := h _ ((latG V g).smul_mem (D.host.conj⁻¹ • a) hy)
    rw [frameForm_int_smul_right, smul_inv_smul, Algebra.smul_def] at h1
    exact h1
  · intro h y hy
    exact trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (h y hy)

end GlobalTheory.Member
