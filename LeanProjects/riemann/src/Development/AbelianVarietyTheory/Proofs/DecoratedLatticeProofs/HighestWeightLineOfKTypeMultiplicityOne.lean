import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.RealPar.HwLine

open GlobalTheory.RealPar.HwGen (PosRoot mono drop drop_cons mono_weight mono_stable weight_of_mem_span cnt)

variable {p q n : ℕ}

def ht : Ix p q → ℝ := Sum.elim (fun i => -(i : ℝ)) (fun j => -(j : ℝ))

theorem ht_lt {a b : Ix p q} (h : posC a b) : ht b < ht a := by
  rcases a with i | i <;> rcases b with j | j <;> simp [posC] at h <;> simp [ht] <;> exact_mod_cast h

theorem ht_drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) :
    ∑ x, ht x * drop l x < ∑ x, ht x * drop (r :: l) x := by
  have hr := ht_lt r.2
  simp only [drop_cons, mul_add, Finset.sum_add_distrib, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

theorem ht_drop_nonneg (l : List (PosRoot p q)) : 0 ≤ ∑ x, ht x * drop l x := by
  induction l with
  | nil => simp [drop, cnt]
  | cons r l ih => exact (lt_of_le_of_lt ih (ht_drop_cons r l)).le

theorem eq_smul_of_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) {w : V}
    (hw : w ∈ Submodule.span ℂ (Set.range (mono act v))) (hwt : ∀ a, act (Eab a a) w = ((μ a : ℚ) : ℂ) • w) :
    ∃ c : ℂ, c • v = w := by
  classical
  let m' : {l : List (PosRoot p q) // l ≠ []} → V := fun l => mono act v l.1
  have hle : Submodule.span ℂ (Set.range (mono act v)) ≤
      Submodule.span ℂ {v} ⊔ Submodule.span ℂ (Set.range m') := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    cases l with
    | nil => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | cons r l =>
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨r :: l, List.cons_ne_nil r l⟩, rfl⟩)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  by_contra hne
  have hz0 : z ≠ 0 := fun h0 => hne (by rw [h0, add_zero])
  have hzw : ∀ a, act (Eab a a) z = ((μ a : ℚ) : ℂ) • z := by
    intro a
    have h1 := hwt a
    rw [map_add, map_smul, hv a, smul_add, smul_comm c] at h1
    exact add_left_cancel h1
  obtain ⟨⟨l, hl0⟩, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) m'
    (fun l a => ((((μ a : ℚ) : ℝ) - drop l.1 a : ℝ) : ℂ)) (fun l a => mono_weight h hv l.1 a)
    (fun a => ((μ a : ℚ) : ℂ)) z hz hz0 hzw
  have hd : ∀ a, drop l a = 0 := by
    intro a
    have h1 : ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ) = (((μ a : ℚ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_ratCast]; exact congrFun hl a
    have h2 := Complex.ofReal_injective h1
    linarith
  obtain ⟨r, l', rfl⟩ := List.exists_cons_of_ne_nil hl0
  have h3 := ht_drop_cons r l'
  have h4 := ht_drop_nonneg l'
  simp only [hd, mul_zero, Finset.sum_const_zero] at h3
  linarith

variable {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
  {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)}

theorem isKTypeOf_span (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ) {v : R.HK.V}
    (hv : Formalism.BasicNotions.TH.IsHW R.HK.act μ v) :
    IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) ((Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι) := by
  classical
  set W := Submodule.span ℂ (Set.range (mono R.HK.act v)) with hWdef
  have hlie : IsLieAct R.HK.act := R.HK.lie
  have hv0 : v ≠ 0 := hv.1
  obtain ⟨hvw, hvr⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  have hvW : v ∈ W := Submodule.subset_span ⟨[], rfl⟩
  have hWst : KStable R.HK.act W := mono_stable hlie hvw hvr
  have hWle : ∀ W' : Submodule ℂ R.HK.V, v ∈ W' → KStable R.HK.act W' → W ≤ W' := by
    intro W' hvW' hW'
    rw [hWdef, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW'
    | cons r l ih => exact hW' _ (HwGen.isKC_Eab r.2) _ ih
  obtain ⟨W0, hW0f, hvW0, hW0s⟩ := R.HK.kfin v
  have := hW0f
  have hWf : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (hWle W0 hvW0 hW0s)
  have hι : Function.Injective R.ι := R.ι_inj
  have hKs : IsKStableOn ε σ (W.map R.ι) := isKStableOn_of_kStable p q n e ε T R σ h hσ W hWf hWst
  refine ⟨inferInstance, hKs, ?_, ?_, ?_⟩
  · intro S' hS'le hS'
    have hS'f : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
    have : CompleteSpace S' := FiniteDimensional.complete ℂ S'
    have hCK : IsKStableOn ε σ (S'ᗮ ⊓ W.map R.ι) := fun g hg x hx =>
      Submodule.mem_inf.2 ⟨kstable_orthogonal R h hσ hS' g hg x (Submodule.mem_inf.1 hx).1,
        hKs g hg x (Submodule.mem_inf.1 hx).2⟩
    have hCf : FiniteDimensional ℂ ↥(S'ᗮ ⊓ W.map R.ι) := Submodule.finiteDimensional_of_le inf_le_right
    obtain ⟨-, hS0map, hS0st⟩ := comap_kstable R h hσ hS'f hS'
    obtain ⟨-, -, hC0st⟩ := comap_kstable R h hσ hCf hCK
    have hdisj : ∀ x, x ∈ S'.comap R.ι → x ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι → x = 0 := by
      intro x hx1 hx2
      apply hι
      rw [map_zero]
      have hbot := Submodule.inf_orthogonal_eq_bot S'
      rw [Submodule.eq_bot_iff] at hbot
      exact hbot _ (Submodule.mem_inf.2 ⟨hx1, (Submodule.mem_inf.1 hx2).1⟩)
    have hsup : S' ⊔ S'ᗮ ⊓ W.map R.ι = W.map R.ι :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hS'le
    have hιv : R.ι v ∈ S' ⊔ S'ᗮ ⊓ W.map R.ι := hsup.symm ▸ Submodule.mem_map_of_mem hvW
    obtain ⟨s', hs', c', hc', hsc⟩ := Submodule.mem_sup.1 hιv
    obtain ⟨s, hsW, rfl⟩ := Submodule.mem_map.1 (hS'le hs')
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hc').2
    have hs : s ∈ S'.comap R.ι := Submodule.mem_comap.2 hs'
    have ht : t ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := Submodule.mem_comap.2 hc'
    have hvst : v = s + t := hι (by rw [map_add]; exact hsc.symm)
    have hsw : ∀ a, R.HK.act (Eab a a) s = ((μ a : ℚ) : ℂ) • s := by
      intro a
      have hK : IsKC (Eab a a) := isKC_Eab ((h.sameBlock_iff a a).2 rfl)
      have e1 := hvw a
      rw [hvst, map_add, smul_add] at e1
      have hm1 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ S'.comap R.ι :=
        Submodule.sub_mem _ (hS0st _ hK _ hs) (Submodule.smul_mem _ _ hs)
      have hm2 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := by
        have he : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s =
            ((μ a : ℚ) : ℂ) • t - R.HK.act (Eab a a) t := by
          rw [sub_eq_sub_iff_add_eq_add, e1]; abel
        rw [he]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ht) (hC0st _ hK _ ht)
      exact sub_eq_zero.1 (hdisj _ hm1 hm2)
    obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hsW hsw
    by_cases hc0 : c = 0
    · left
      have htv : t = v := by rw [hvst, ← hc, hc0, zero_smul, zero_add]
      have hWC : W ≤ (S'ᗮ ⊓ W.map R.ι).comap R.ι := hWle _ (htv ▸ ht) hC0st
      have hS0bot : S'.comap R.ι = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.1 (hS'le (Submodule.mem_comap.1 hx))
        obtain rfl : y = x := hι hyx
        exact hdisj y hx (hWC hyW)
      rw [← hS0map, hS0bot, Submodule.map_bot]
    · right
      have hvS0 : v ∈ S'.comap R.ι := by
        have hv' : v = c⁻¹ • s := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hv']
        exact Submodule.smul_mem _ _ hs
      have hWS : W ≤ S'.comap R.ι := hWle _ hvS0 hS0st
      refine le_antisymm hS'le ?_
      calc W.map R.ι ≤ (S'.comap R.ι).map R.ι := Submodule.map_mono hWS
        _ = S' := hS0map
  · refine ⟨R.ι v, Submodule.mem_map_of_mem hvW, fun h0 => hv0 (hι (by rw [h0, map_zero])), ?_⟩
    refine (TorusWt.isWtOn_iff p q n e ε T R σ h hσ _ v).2 fun a => ?_
    simp only [hvw a, Equiv.symm_apply_apply, Complex.ofReal_ratCast]
  · intro ν x hx hx0 hxw
    obtain ⟨w, hwW, rfl⟩ := Submodule.mem_map.1 hx
    have hw0 : w ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
    have hww := (TorusWt.isWtOn_iff p q n e ε T R σ h hσ ν w).1 hxw
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => R.HK.act (Eab a a)) (mono R.HK.act v)
      (fun l a => ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ)) (fun l a => mono_weight hlie hvw l a)
      (fun a => ((ν (e a) : ℝ) : ℂ)) w hwW hw0 hww
    have hl' : ∀ a, ((μ a : ℚ) : ℝ) - drop l a = ν (e a) :=
      fun a => Complex.ofReal_injective (congrFun hl a)
    have key : ∀ x, ∑ i, ∑ j, (cnt l (e.symm i) (e.symm j) : ℝ) * Formalism.REAL.root i j (e x) = drop l x := by
      intro x
      rw [← Equiv.sum_comp e]
      refine (Finset.sum_congr rfl fun a _ => (Equiv.sum_comp e _).symm).trans ?_
      simp only [Equiv.symm_apply_apply, root_apply e, drop]
    refine ⟨fun i j => cnt l (e.symm i) (e.symm j), fun i j hij => ?_, ?_⟩
    · have := (h.posC_iff _ _).1 (HwGen.posC_of_cnt l _ _ hij)
      simpa using this
    · funext k
      obtain ⟨x, rfl⟩ := e.surjective k
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
      linarith [key x, hl' x]

theorem finrank_hwSub_eq_one : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  intro p q n e ε T R σ h hσ μ hex huniq
  classical
  obtain ⟨S, hS⟩ := hex
  obtain ⟨v, hv⟩ := isHW_of_isKTypeOf R h hσ μ hS
  have hlie : IsLieAct R.HK.act := R.HK.lie
  obtain ⟨hvw, -⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  rw [finrank_eq_one_iff_of_nonzero' (⟨v, hv.2⟩ : hwSub R.HK.act μ)
    (fun h0 => hv.1 (congrArg Subtype.val h0))]
  rintro ⟨w, hw⟩
  by_cases hw0 : w = 0
  · exact ⟨0, Subtype.ext (by simp [hw0])⟩
  have hwHW : Formalism.BasicNotions.TH.IsHW R.HK.act μ w := ⟨hw0, hw⟩
  obtain ⟨hww, -⟩ := (mem_hwSub R.HK.act μ w).1 hw
  have hEq := huniq _ _ (isKTypeOf_span R h hσ μ hv) (isKTypeOf_span R h hσ μ hwHW)
  have hιw : R.ι w ∈ (Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι := by
    rw [hEq]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨[], rfl⟩)
  obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 hιw
  obtain rfl : y = w := R.ι_inj hyw
  obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hy hww
  exact ⟨c, Subtype.ext hc⟩

end GlobalTheory.RealPar.HwLine
