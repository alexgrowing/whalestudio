import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchOfDenseSeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisMatchingAddStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitStep

section Basic
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def qU {r : ℕ} (X : Hn r F E) : F := Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2

theorem mom_act_zero {r : ℕ} (g : GL (Fin r) F) (Y : Gl r F) : mom (act g Y) 0 = mom Y 0 := by
  simp only [mom, act, pow_zero, one_mulVec]
  rw [dotProduct_mulVec, vecMul_vecMul]
  have : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
    simp
  rw [this, vecMul_one]

theorem qU_actU {r : ℕ} (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : qU (actU g X) = qU X := by
  simp only [qU, actU]
  congr 2
  rw [Matrix.star_mulVec, dotProduct_mulVec, vecMul_vecMul]
  have : (g.1)ᴴ * g.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 g.2
  rw [this, vecMul_one]

theorem mom_sec_zero {r : ℕ} (a : Inv (r + 1) F) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct]

theorem qU_of_hasInv [Unram F E] {r : ℕ} {X : Hn (r + 1) F E} {a : Inv (r + 1) F} (h : HasInv X a) :
    qU X = mom (sec a) 0 := by
  have h1 := congrArg (fun p => p.2.1 0) h
  simp only [inv, Inv.map, Hn.toGl, mom] at h1
  rw [show ((0 : Fin (r + 1)) : ℕ) = 0 from rfl, pow_zero, one_mulVec] at h1
  rw [mom_sec_zero, qU, h1, Algebra.trace_algebraMap, Unram.finrank_eq]
  haveI := (Unram.charZero (F := F) (E := E))
  rw [nsmul_eq_mul]; push_cast; field_simp

theorem orbG_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f' : Gl r F → ℂ) (Y : Gl r F) :
    orbG M (fun Y => φ (mom Y 0) * f' Y) Y = φ (mom Y 0) * orbG M f' Y := by
  simp only [orbG, mom_act_zero, mul_assoc]
  exact integral_const_mul _ _

theorem orbU_mul {r : ℕ} (M : Meas r F E) (φ : F → ℂ) (f : Hn r F E → ℂ) (X : Hn r F E) :
    orbU M (fun X => φ (qU X) * f X) X = φ (qU X) * orbU M f X := by
  simp only [orbU, qU_actU]
  exact integral_const_mul _ _

theorem matchAt_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h : MatchAt M f' f a) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, h.1 X hX, qU_of_hasInv hX],
    fun hn => by rw [orbG_mul, h.2 hn, mul_zero]⟩

theorem matchAt_mul_zero [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) (f' : Gl (r + 1) F → ℂ)
    (f : Hn (r + 1) F E → ℂ) {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) = 0) :
    MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a :=
  ⟨fun X hX => by rw [orbG_mul, orbU_mul, qU_of_hasInv hX, h0, zero_mul, zero_mul],
    fun _ => by rw [orbG_mul, h0, zero_mul]⟩

theorem matchAt_of_mul [Unram F E] {r : ℕ} (M : Meas (r + 1) F E) (φ : F → ℂ) {f' : Gl (r + 1) F → ℂ}
    {f : Hn (r + 1) F E → ℂ} {a : Inv (r + 1) F} (h0 : φ (mom (sec a) 0) ≠ 0)
    (h : MatchAt M (fun Y => φ (mom Y 0) * f' Y) (fun X => φ (qU X) * f X) a) : MatchAt M f' f a := by
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · have := h.1 X hX
    rw [orbG_mul, orbU_mul, qU_of_hasInv hX] at this
    exact mul_left_cancel₀ h0 this
  · have := h.2 hn
    rw [orbG_mul] at this
    exact (mul_eq_zero.1 this).resolve_left h0

theorem match_zero {r : ℕ} (M : Meas r F E) : Match M (0 : Gl r F → ℂ) (0 : Hn r F E → ℂ) := by
  intro a _
  refine ⟨fun X _ => ?_, fun _ => ?_⟩ <;> simp [orbG, orbU]

theorem isTest_sub {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsTest f) (hg : IsTest g) :
    IsTest (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem wS_inv : (wS F)⁻¹ = wS F * wS F * wS F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  simp [wS, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem nS_inv (t : F) : (nS t)⁻¹ = nS (-t) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![1, -t; 0, 1] = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]

variable (E) in

theorem submonoid_eq_top [Unram F E] (S : Submonoid (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ S)
    (hn : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ S) (x : SpecialLinearGroup (Fin 2) F) : x ∈ S := by
  have hgen := GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ F E
  have hx : x ∈ Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) := by
    rw [hgen]; trivial
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
  refine (Submonoid.closure_le (S := S)).2 ?_ hx
  rintro g ((hg | ⟨t, ht, rfl⟩) | hg)
  · rw [Set.mem_singleton_iff.1 hg]; exact hw
  · exact hn t ht
  · rcases hg with hg | ⟨t, ht, hg⟩
    · rw [Set.mem_singleton_iff] at hg
      rw [← inv_inv g, hg, wS_inv]; exact S.mul_mem (S.mul_mem hw hw) hw
    · rw [← inv_inv g, hg, nS_inv]
      exact hn (-t) (fun y hy => by rw [neg_mul, norm_neg]; exact ht y hy)

end Basic
end GlobalTheory.JR.UnitStep

namespace GlobalTheory.JR.UnitStep

theorem unitMatch_succ : WeilEt → GammaOne → ∀ r : ℕ, FourierMatch (r + 1) → UnitMatch r → UnitMatch (r + 1) := by
  intro hWe hGo r hF hU F E _ _ _ _ _ M
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).1
  obtain ⟨W1, hW1r, hW1⟩ := GlobalTheory.T.exists_weilRepSL2_glBorderedBlock F E (r + 1) M ψ hψ
  obtain ⟨W2, hW2r, hW2⟩ := GlobalTheory.T.exists_weilRepSL2_hermitianBlock hWe hGo F E (r + 1) M ψ hψ
  obtain ⟨hTG, hTU, htG, htU, hfG, hfU⟩ := GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E (r + 1) M ψ hψ

  have hN1 : ∀ f, IsTest f → ∀ t : F, W1 (nS t) f = fun Y => (fun z => ψ (t * z)) (mom Y 0) * f Y :=
    fun f hf t => funext fun Y => (hW1 f hf).1 t Y
  have hN2 : ∀ f, IsTest f → ∀ t : F, W2 (nS t) f = fun X => (fun z => ψ (t * z)) (qU X) * f X :=
    fun f hf t => funext fun X => by
      rw [(hW2 f hf).1 t X, qU, mul_div_assoc]

  let S : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | ∀ f' f, IsTest f' → IsTest f → Match M f' f → Match M (W1 g f') (W2 g f)}
      one_mem' := fun f' f hf' hf hm => by rw [hW1r.2.1 f' hf', hW2r.2.1 f hf]; exact hm
      mul_mem' := fun {g h} hg hh f' f hf' hf hm => by
        rw [hW1r.2.2.1 g h f' hf', hW2r.2.2.1 g h f hf]
        exact hg _ _ (hW1r.1 h f' hf') (hW2r.1 h f hf) (hh f' f hf' hf hm) }
  have hS : ∀ g, g ∈ S := submonoid_eq_top E S
    (fun f' f hf' hf hm => by rw [(hW1 f' hf').2, (hW2 f hf).2]; exact hF F E M ψ hψ f' f hf' hf hm)
    (fun t _ f' f hf' hf hm => by
      rw [hN1 f' hf' t, hN2 f hf t]
      exact fun a ha => matchAt_mul M (fun z => ψ (t * z)) (hm a ha))

  let u' := unitG (r + 1) F
  let u := unitU (r + 1) F E
  let S' : Submonoid (SpecialLinearGroup (Fin 2) F) :=
    { carrier := {g | Match M (W1 g u' - u') (W2 g u - u)}
      one_mem' := by
        show Match M (W1 1 u' - u') (W2 1 u - u)
        rw [hW1r.2.1 u' htG, hW2r.2.1 u htU, sub_self, sub_self]; exact match_zero M
      mul_mem' := fun {g h} hg hh => by
        show Match M (W1 (g * h) u' - u') (W2 (g * h) u - u)
        have e1 : W1 (g * h) u' - u' = W1 g (W1 h u' - u') + (W1 g u' - u') := by
          have hs : W1 h u' - u' = (-1 : ℂ) • u' + W1 h u' := by
            funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW1r.2.2.1 g h u' htG, hs, hW1r.2.2.2 g (-1) u' (W1 h u') htG (hW1r.1 h u' htG)]
          funext Y; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have e2 : W2 (g * h) u - u = W2 g (W2 h u - u) + (W2 g u - u) := by
          have hs : W2 h u - u = (-1 : ℂ) • u + W2 h u := by
            funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          rw [hW2r.2.2.1 g h u htU, hs, hW2r.2.2.2 g (-1) u (W2 h u) htU (hW2r.1 h u htU)]
          funext X; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have d1 : IsTest (W1 h u' - u') := isTest_sub (hW1r.1 h u' htG) htG
        have d2 : IsTest (W2 h u - u) := isTest_sub (hW2r.1 h u htU) htU
        rw [e1, e2]
        exact GlobalTheory.T.jacquetRallis_matching_add F E (r + 1) M _ _ _ _ (hW1r.1 g _ d1) (isTest_sub (hW1r.1 g u' htG) htG)
          (hW2r.1 g _ d2) (isTest_sub (hW2r.1 g u htU) htU) (hS g _ _ d1 d2 hh) hg }
  have hD1 : ∀ t : F, W1 (nS t) u' - u' = fun Y => (fun z => ψ (t * z) - 1) (mom Y 0) * u' Y := by
    intro t; rw [hN1 u' htG t]; funext Y; simp only [Pi.sub_apply]; ring
  have hD2 : ∀ t : F, W2 (nS t) u - u = fun X => (fun z => ψ (t * z) - 1) (qU X) * u X := by
    intro t; rw [hN2 u htU t]; funext X; simp only [Pi.sub_apply]; ring
  have hS' : ∀ g, g ∈ S' := submonoid_eq_top E S'
    (by
      show Match M (W1 (wS F) u' - u') (W2 (wS F) u - u)
      rw [(hW1 u' htG).2, (hW2 u htU).2, hfG, hfU, sub_self, sub_self]; exact match_zero M)
    (fun t ht => by
      show Match M (W1 (nS t) u' - u') (W2 (nS t) u - u)
      rw [hD1 t, hD2 t]
      intro a ha
      by_cases h1 : 1 ≤ ‖mom (sec a) 0‖
      · exact matchAt_mul M (fun z => ψ (t * z) - 1) (GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm r hU F E M a ha h1)
      · refine matchAt_mul_zero M (fun z => ψ (t * z) - 1) u' u ?_
        have : ‖t * mom (sec a) 0‖ ≤ 1 := ht _ (lt_of_not_ge h1)
        simp [hψ.1 _ this])

  refine (GlobalTheory.T.jacquetRallis_match_of_dense_separable F E (r + 1) M u' u htG htU).2 (Nat.succ_pos r) ?_
  intro a ha ha0
  obtain ⟨x, hx, -⟩ := hψ.2
  have hm := hS' (nS (x / mom (sec a) 0))
  change Match M (W1 (nS _) u' - u') (W2 (nS _) u - u) at hm
  rw [hD1, hD2] at hm
  refine matchAt_of_mul M (fun z => ψ (x / mom (sec a) 0 * z) - 1) ?_ (hm a ha)
  simp only [div_mul_cancel₀ x ha0]
  exact sub_ne_zero.2 hx

end GlobalTheory.JR.UnitStep
