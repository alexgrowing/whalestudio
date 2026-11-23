import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RelIndexDualSubmoduleInfOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TailSumLtOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNormAndOverlapBoundStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionOverlapEqZeroOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNoCoinvariantsIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleDoubledHermitianThetaFamilyStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.RecSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem EF_swap (hs : IsSympl X bas) (u v : Fin r → E) : EF X u v = -EF X v u := by
  rw [EF_crd hs u v, EF_crd hs v u, neg_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_EF (hs : IsSympl X bas) (u : Fin r → E) (h : ∀ v, EF X u v = 0) : u = 0 := by
  have hc : crd X bas u = 0 := by
    funext j
    rcases j with i | i
    · have h1 := h (vecQ X bas (Pi.single (Sum.inr i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (vecQ X bas (Pi.single (Sum.inl i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
  rw [← vecQ_crd X bas u, hc]
  exact vecQ_zero X bas

theorem EFBil_nondegenerate (hs : IsSympl X bas) :
    LinearMap.BilinForm.Nondegenerate (EFBil X) := by
  refine ⟨fun u hu => eq_zero_of_EF hs u fun v => hu v, fun u hu => eq_zero_of_EF hs u fun v => ?_⟩
  have h0 : EF X v u = 0 := hu v
  rw [EF_swap hs, h0, neg_zero]

theorem selfD_int {L : Lt E r} (h : SelfD X L) : (L.restrictScalars ℤ).FG ∧
    LinearMap.BilinForm.dualSubmodule (EFBil X) (L.restrictScalars ℤ) = L.restrictScalars ℤ := by
  refine ⟨h.1.restrictScalars, ?_⟩
  ext x
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.restrictScalars_mem, h.2 x]
  constructor
  · intro H y hy
    obtain ⟨k, hk⟩ := Submodule.mem_one.1 (H y hy)
    exact ⟨k, hk.symm.trans (eq_intCast _ k)⟩
  · intro H y hy
    obtain ⟨k, hk⟩ := H y hy
    exact Submodule.mem_one.2 ⟨k, (eq_intCast _ k).trans hk.symm⟩

theorem tail_le (hs : IsSympl X bas) (hn : 4 * (Module.finrank ℚ E * r) + 4 ≤ n)
    (𝓛 : Set (Lt E r)) (h𝓛 : ∀ L ∈ 𝓛, SelfD X L) {L : Lt E r} (hL : L ∈ 𝓛) :
    Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2)) ∧
    ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) ≤ 0.65 := by
  classical
  have hρ : Module.finrank ℚ (Fin r → E) = Module.finrank ℚ E * r := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have hsw := EF_swap (X := X) hs
  have hB := EFBil_nondegenerate hs
  have hrefl : (EFBil X).IsRefl := fun x y hxy => by
    have h0 : EF X x y = 0 := hxy
    show EF X y x = 0
    rw [hsw, h0, neg_zero]
  have hlr : ∀ x y, EFBil X x y = EFBil X y x ∨ EFBil X x y = -EFBil X y x :=
    fun x y => Or.inr (show EF X x y = -EF X y x from hsw x y)
  obtain ⟨hLfg, hLd⟩ := selfD_int (h𝓛 L hL)
  have key := card_selfDual_le (EFBil X) hB hrefl hlr _ hLfg hLd
  let f : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℕ := fun L' => L'.1.toAddSubgroup.relIndex L.toAddSubgroup
  let G : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → Submodule ℤ (Fin r → E) := fun L' => L'.1.restrictScalars ℤ
  have hGinj : Function.Injective G := fun a b hab =>
    Subtype.ext (Submodule.restrictScalars_injective ℤ _ _ hab)
  have hGmem : ∀ i, (G i).FG ∧ LinearMap.BilinForm.dualSubmodule (EFBil X) (G i) = G i ∧
      (G i).toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = f i := fun i =>
    ⟨(selfD_int (h𝓛 i.1 i.2.1)).1, (selfD_int (h𝓛 i.1 i.2.1)).2, rfl⟩
  have h2 : ∀ i, 2 ≤ f i := by
    intro i
    obtain ⟨hne, h1⟩ := (key 1 le_rfl).2.2 (G i) (hGmem i).1 (hGmem i).2.1
    have hfi : f i ≠ 1 := fun h1' => i.2.2 (Submodule.restrictScalars_injective ℤ _ _ (h1 h1'))
    have : f i ≠ 0 := hne
    omega
  have hc : ∀ m, {i | f i = m}.Finite ∧ {i | f i = m}.ncard ≤ m ^ (2 * Module.finrank ℚ (Fin r → E)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have he : {i | f i = 0} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => by
        have := h2 i
        simp only [Set.mem_ofPred_eq] at hi
        omega
      simp [he]
    · have hsub : ∀ i ∈ {i | f i = m}, G i ∈ {L' : Submodule ℤ (Fin r → E) | L'.FG ∧
          LinearMap.BilinForm.dualSubmodule (EFBil X) L' = L' ∧ L'.toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = m} :=
        fun i hi => ⟨(hGmem i).1, (hGmem i).2.1, (hGmem i).2.2.trans hi⟩
      have hfin' := (key m hm).1
      refine ⟨(hfin'.preimage hGinj.injOn).subset fun i hi => hsub i hi, ?_⟩
      exact (Set.ncard_le_ncard_of_injOn G hsub hGinj.injOn hfin').trans (key m hm).2.1
  have hρn : 4 * Module.finrank ℚ (Fin r → E) + 4 ≤ n := by rw [hρ]; exact hn
  let c : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℂ := fun i => (((f i : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ)
  have hnorm : ∀ i, ‖c i‖ = (f i : ℝ) ^ (-(n : ℝ) / 2) := fun i =>
    Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have res := tail_sum_lt_one f _ n hρn h2 hc c fun i => (hnorm i).le
  simp only [hnorm] at res
  exact res

theorem norm_eq_one_of_ip {φ : TF n g} (hφ : IsSB φ) (h1 : SW.ip φ φ = 1) {c : ℂ}
    (h : SW.ip (c • φ) (c • φ) = 1) : ‖c‖ = 1 := by
  have hc := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ φ hφ hφ).2.2.2.1
  have hF := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ _ hφ hc).2.2.1
  have hsm := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hF hF).2.2.2.2.2.1 (c * conj c)
  have e : (fun x => (c • φ) x * conj ((c • φ) x)) = (c * conj c) • (φ * fun x => conj (φ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  have h1' : haar (φ * fun x => conj (φ x)) = 1 := h1
  unfold SW.ip at h
  rw [e, hsm, h1', mul_one, Complex.mul_conj] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  nlinarith [norm_nonneg c]

end GlobalTheory.SW.RecSys

namespace GlobalTheory.SW

open RecSys

theorem isSystem_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → IsSystem X bas idx M D.grp D.lats (D.phi bas hn v₀) μ := by
  intro E _ _ _ r X g bas idx n hs hn2 hnE D hn M hM0 hMm v₀ hv₀ μ hμ
  obtain ⟨-, -, hgrp, hlats, hlam, -, -⟩ := GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn2 D hn
  have T4 := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have T5 := GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have hfinQ : Finite (𝓞 E ⧸ D.𝔪) := D.𝔪.finiteQuotientOfFreeOfNeBot D.ne_bot
  have hfinM : Finite (Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) :=
    inferInstanceAs (Finite (Fin r → Fin r → 𝓞 E ⧸ D.𝔪))
  have hcard : 0 < Nat.card D.J := Nat.card_pos
  refine
    { un := fun γ hγ => ((hgrp γ).1 hγ).1
      lat := fun L hL => ⟨hL.1.1, (hlats L hL).2.1⟩
      stab := fun γ hγ L hL => ((hlats L hL).2.2.2 γ hγ).1
      sb := fun L hL Λ hΛ => (T4 L hL Λ hΛ).1
      norm := ⟨(Nat.card D.J : ℝ), by exact_mod_cast hcard,
        fun L hL Λ hΛ => by rw [(T5 L hL Λ hΛ).1, Complex.ofReal_natCast],
        fun L L' => (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2), 0.65,
        by norm_num, fun L hL L' hL' Λ hΛ => (T5 L hL Λ hΛ).2 L' hL',
        fun L hL => RecSys.tail_le hs hnE D.lats (fun L' hL' => hL'.1) hL⟩
      mu := fun γ hγ L hL => ?_
      supp := fun γ hγ hγ' L hL L' hL' Λ hΛ =>
        GlobalTheory.T.thetaTestFunction_overlap_eq_zero_outside_level E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ γ hγ hγ' L hL L' hL' Λ hΛ
      cusp := fun ξ hξ hξ0 L hL Λ hΛ =>
        GlobalTheory.T.thetaTestFunction_no_coinvariants_isotropic E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ ξ hξ hξ0 L hL Λ hΛ
      adm := fun L hL L' hL' => GlobalTheory.T.admissible_doubledHermitianThetaFamily E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ L hL L' hL' }
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hmem := ((hlats L hL).2.2.2 γ hγ).1
  have hrel := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  have hvac := hv₀ L hL
  have hvac' := hv₀ _ hmem
  have hip : SW.ip ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L))
      ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L)) = 1 := by
    rw [← hrel, ((wG_laws E r X g bas idx n hs hn2 γ hun (v₀ L) hvac.1).2.2.1 (v₀ L) hvac.1).1]
    exact hvac.2.1
  have htn := RecSys.norm_eq_one_of_ip hvac'.1 hvac'.2.1 hip
  have hl := hlam ⟨k, hkJ⟩
  refine ⟨?_, fun Λ hΛ => ?_⟩
  · rw [norm_mul, hl, mul_one] at htn
    exact htn
  · rw [(T4 L hL Λ hΛ).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ htn hrel, mul_inv_cancel_right₀ (Units.ne_zero _)]

end GlobalTheory.SW
