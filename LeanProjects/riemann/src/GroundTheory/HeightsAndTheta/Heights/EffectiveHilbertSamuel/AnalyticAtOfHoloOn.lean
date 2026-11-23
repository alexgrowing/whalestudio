import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.MemSectionsOfHolLineBundleEquiv
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.JetOfMonomialSumStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

noncomputable section

namespace EffectiveHilbertSamuelJetLemmas

variable {D : ℕ} {U : Type} [TopologicalSpace U]

theorem chart_sum_eq (A : FinHolAtlas D U) (s : Fin D → Fin A.n → U → ℂ) (a : ℕ)
    (h : (Fin D → ℕ) → Fin A.n → U → ℂ) (c : Fin A.n) :
    (∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s α * h α) c ∘ (A.chart c).symm =
      fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        (∏ i, (s i c ∘ (A.chart c).symm) z ^ α i) * (h α c ∘ (A.chart c).symm) z := by
  funext z
  simp [sPow, Finset.sum_apply, Finset.prod_apply]

theorem analyticAt_of_holoOn (A : FinHolAtlas D U) {f : U → ℂ} {c : Fin A.n}
    (hf : A.HoloOn (A.chart c).source f) {x : U} (hx : x ∈ (A.chart c).source) :
    AnalyticAt ℂ (f ∘ (A.chart c).symm) (A.chart c x) :=
  hf c _ ⟨(A.chart c).map_source hx, by rw [Set.mem_preimage, (A.chart c).left_inv hx]; exact hx⟩

theorem exists_unit {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (he : NoCommonZero A e) {S : Set U} (hS : S.Finite) :
    ∃ c : Fin N → ℂ, ∀ x ∈ S, lin e c (chartIdx A x) x ≠ 0 := by
  classical
  let φ : U → (Fin N → ℂ) →ₗ[ℂ] ℂ := fun x =>
    ∑ k, e k (chartIdx A x) x • (LinearMap.proj k : (Fin N → ℂ) →ₗ[ℂ] ℂ)
  have hφ : ∀ x c, φ x c = lin e c (chartIdx A x) x := by
    intro x c
    simp [φ, lin, Finset.sum_apply, mul_comm]
  have hne : ∀ x, LinearMap.ker (φ x) ≠ ⊤ := by
    intro x htop
    obtain ⟨k, hk⟩ := he x
    have h0 : Pi.single k 1 ∈ LinearMap.ker (φ x) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at h0
    have hl : lin e (Pi.single k 1) = e k := by simp [lin, Pi.single_apply]
    rw [hl] at h0
    exact hk h0
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt hS.toFinset
    (fun x => LinearMap.ker (φ x)) hne (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)
  obtain ⟨c, -, hc⟩ := Set.exists_of_ssubset hss
  refine ⟨c, fun x hx h0 => hc ?_⟩
  rw [Set.mem_iUnion₂]
  exact ⟨x, hS.mem_toFinset.2 hx, by rw [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact h0⟩

theorem _root_.GroundTheory.Heights₂.Heights.EffectiveHS.SymOnto.proof
    (hJ : JetOfMonomialSum.Statement) : SymOnto.Statement := by
  classical
  intro D T X Z Y hD hT hRes a ha g
  obtain ⟨c₀, hc₀⟩ := exists_unit X.A X.e X.gen Z.finite
  set w : Fin X.A.n → X.U → ℂ := lin X.e c₀ with hw
  set j := T - a with hj
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ i, α i = a := fun α hα =>
    Finset.Nat.mem_antidiagonalTuple.1 hα
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / w (chartIdx X.A y) y ^ j)
  have hwj : w ^ j = ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • ∏ l, X.e (ι l) := by
    rw [← Fin.prod_const j w, hw, lin, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    funext k x
    simp [Finset.prod_apply, Finset.prod_mul_distrib]
  have pt : ∀ x ∈ zeroSet X.A Z.s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
        (X.A.chart (chartIdx X.A x) x) = 0) ∧
      ∀ v : Fin D → ℂ, iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a,
        sPow Z.s α * (w ^ j * m α)) (chartIdx X.A x) ∘ (X.A.chart (chartIdx X.A x)).symm)
          (X.A.chart (chartIdx X.A x) x) (fun _ => v) / (a.factorial : ℂ) =
        sJac X.A Z.s (chartIdx X.A x) x * ∑ α ∈ Finset.Nat.antidiagonalTuple D a,
          (∏ i, (sJacMap X.A Z.s (chartIdx X.A x) x v i) ^ α i) * g α x := by
    intro x hx
    set c := chartIdx X.A x with hc
    have hxc : x ∈ (X.A.chart c).source := Classical.choose_spec (X.A.cover x)
    have hlin : ∀ c' : Fin X.N → ℂ, lin X.e c' ∈ X.L.sections 1 := fun c' =>
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)
    have au : ∀ i, AnalyticAt ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) := fun i =>
      analyticAt_of_holoOn X.A ((hlin (Z.c i)).1 c) hxc
    have aw : AnalyticAt ℂ (w c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      analyticAt_of_holoOn X.A ((hlin c₀).1 c) hxc
    have ah : ∀ α, AnalyticAt ℂ ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) :=
      fun α => (aw.pow j).mul (analyticAt_of_holoOn X.A ((Y.V_le 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, -, h3⟩ := hJ D D (fun i => Z.s i c ∘ (X.A.chart c).symm)
      (fun α => (w ^ j * m α) c ∘ (X.A.chart c).symm) _ a au hz ah
    have hF := chart_sum_eq X.A Z.s a (fun α => w ^ j * m α) c
    rw [hF]
    refine ⟨h1, fun v => ?_⟩
    rw [h3 v]
    have hJ0 : sJac X.A Z.s c x ≠ 0 := Z.nondeg x hx
    have hcoef : ∀ α, ((w ^ j * m α) c ∘ (X.A.chart c).symm) (X.A.chart c x) =
        g α x * sJac X.A Z.s c x := by
      intro α
      have hr := hm α x hx
      have hw0 : w c x ≠ 0 := hc₀ x hx
      simp only [res] at hr
      rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
      simp only [Function.comp_apply, (X.A.chart c).left_inv hxc, Pi.mul_apply, Pi.pow_apply]
      linear_combination hr
    have hder : ∀ i, sJacMap X.A Z.s c x v i =
        fderiv ℂ (Z.s i c ∘ (X.A.chart c).symm) (X.A.chart c x) v := by
      intro i
      show (fderiv ℂ (fun z i => (Z.s i c ∘ (X.A.chart c).symm) z) (X.A.chart c x)) v i = _
      rw [fderiv_pi (fun i => (au i).differentiableAt)]
      rfl
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hcoef α]
    simp only [hder]
    ring
  refine ⟨∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow Z.s α * (w ^ j * m α), ?_,
    fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩
  refine Submodule.sum_mem _ fun α hα => ?_
  have hexp : sPow Z.s α * (w ^ j * m α) =
      ∑ ι : Fin j → Fin X.N, (∏ l, c₀ (ι l)) • (sPow Z.s α * (∏ l, X.e (ι l)) * m α) := by
    rw [hwj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  rw [hexp]
  exact Submodule.sum_mem _ fun ι _ => Submodule.smul_mem _ _ (Submodule.mem_sup_left
    (Submodule.subset_span ⟨α, j, ι, m α, hmV α, by rw [hsum α hα]; omega,
      by rw [hsum α hα]; exact ha, rfl⟩))

theorem _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.proof
    (hJ : JetOfMonomialSum.Statement) : IndefiniteRowSideFullHecke.EffectiveHS.EffectiveHilbertSamuelJetSecond.Statement := by
  classical
  intro D hD X Y _ _ _ _ _ _ A d s hGood hRes hUnit a ha g
  obtain ⟨c₀, hc₀⟩ := hUnit
  set j := d.T - a with hj
  choose m hmV hm using fun α : Fin D → ℕ =>
    hRes (fun y => g α y / d.W.sec c₀ (chartIdx A y) y ^ j)
  let s' : Fin D → Fin A.n → X → ℂ := fun i => d.W.sec (s i)
  let hh : (Fin D → ℕ) → Fin A.n → X → ℂ := fun α =>
    IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.wProd fun _ : Fin j => c₀) (m α)
  have hF : (∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a,
      IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α)) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [TranslateEq.sPow_eq_monoSec]
    rfl
  refine ⟨∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, IndefiniteRowSideFullHecke.EffectiveHS.secMul (d.monoSec s α) (hh α),
    Submodule.sum_mem _ fun α hα => Submodule.mem_sup_left (Submodule.subset_span
      ⟨j, α, fun _ => c₀, m α, hmV α, ?_, ?_, rfl⟩), ?_⟩
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; omega
  · rw [Finset.Nat.mem_antidiagonalTuple.1 hα]; exact ha
  have hsec : ∀ c' : Fin d.W.n → ℂ,
      d.W.sec c' ∈ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace d.L 1 := fun c' =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (d.W.mem k)
  have pt : ∀ x ∈ d.zeroU s,
      (∀ k < a, iteratedFDeriv ℂ k ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) = 0) ∧
      iteratedFDeriv ℂ a ((∑ α ∈ Finset.Nat.antidiagonalTuple D a, sPow s' α * hh α)
        (chartIdx A x) ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) =
        ∑ α ∈ IndefiniteRowSideFullHecke.EffectiveHS.tuples D a, (g α x * d.sJac s (chartIdx A x) x) •
          iteratedFDeriv ℂ a (fun z => ∏ i, d.sLoc s (chartIdx A x) z i ^ α i)
            (A.chart (chartIdx A x) x) := by
    intro x hx
    set c := chartIdx A x with hc
    have hxc : x ∈ (A.chart c).source := Classical.choose_spec (A.cover x)
    have au : ∀ i, AnalyticAt ℂ (s' i c ∘ (A.chart c).symm) (A.chart c x) := fun i =>
      analyticAt_of_holoOn A ((hsec (s i)).1 c) hxc
    have aw : AnalyticAt ℂ (d.W.sec c₀ c ∘ (A.chart c).symm) (A.chart c x) :=
      analyticAt_of_holoOn A ((hsec c₀).1 c) hxc
    have hhc : ∀ α, hh α c ∘ (A.chart c).symm = fun z =>
        (d.W.sec c₀ c ∘ (A.chart c).symm) z ^ j * (m α c ∘ (A.chart c).symm) z := by
      intro α
      funext z
      simp [hh, IndefiniteRowSideFullHecke.EffectiveHS.secMul, IndefiniteRowSideFullHecke.EffectiveHS.FSData.wProd]
    have ah : ∀ α, AnalyticAt ℂ (hh α c ∘ (A.chart c).symm) (A.chart c x) := by
      intro α
      rw [hhc α]
      exact (aw.pow j).mul
        (analyticAt_of_holoOn A ((TranslateEq.space_le_topForms d 0 (hmV α)).1 c) hxc)
    have hz : ∀ i, (s' i c ∘ (A.chart c).symm) (A.chart c x) = 0 := fun i => by
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]; exact hx i
    obtain ⟨h1, h2, -⟩ := hJ D D (fun i => s' i c ∘ (A.chart c).symm)
      (fun α => hh α c ∘ (A.chart c).symm) _ a au hz ah
    rw [chart_sum_eq A s' a hh c]
    refine ⟨h1, ?_⟩
    rw [h2]
    have hJ0 : d.sJac s c x ≠ 0 := hGood.etale x hx
    refine Finset.sum_congr rfl fun α _ => ?_
    have hr := hm α x hx
    have hw0 : d.W.sec c₀ c x ≠ 0 := hc₀ x hx
    simp only [IndefiniteRowSideFullHecke.EffectiveHS.FSData.res] at hr
    rw [div_eq_div_iff hJ0 (pow_ne_zero _ hw0)] at hr
    have hcoef : (hh α c ∘ (A.chart c).symm) (A.chart c x) = g α x * d.sJac s c x := by
      rw [hhc α]
      simp only [Function.comp_apply, (A.chart c).left_inv hxc]
      linear_combination hr
    rw [hcoef]
    rfl
  rw [hF]
  exact ⟨fun x hx => (pt x hx).1, fun x hx => (pt x hx).2⟩

end EffectiveHilbertSamuelJetLemmas

end

end GroundTheory.Heights₂.Heights.EffectiveHS
