import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceKappa
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology MeasureTheory
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable logNormSec)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

namespace GreenMassReplace

theorem ell_anti {t t₀ : ℝ} (ht : 0 < t) (htt : t ≤ t₀) : ell t₀ ≤ ell t :=
  Real.log_le_log (inv_pos.2 (ht.trans_le htt)) (inv_anti₀ ht htt)

theorem formNonneg_mono {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {V : Set X} {P : LocPot X} (h : FormNonneg A Set.univ P) : FormNonneg A V P :=
  fun x k y hy w => h x k y ⟨hy.1, trivial, hy.2.2⟩ w

theorem formNonneg_kaehler {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    (Om : KaehlerForm A) (V : Set X) : FormNonneg A V Om.pot :=
  fun x k y hy w => KaehlerForm.isPsh Om x k y ⟨hy.1, hy.2.2⟩ w

theorem mInt_nonneg_of_compl {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (V : Set X) (hAn : A.IsAnalyticSubset Vᶜ) (hint : interior Vᶜ = ∅) (Φ : Fin e → LocPot X)
    (hpot : ∀ i, IsPotential A (Φ i)) (hnn : ∀ i, FormNonneg A V (Φ i)) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mInt A Φ f := by
  rw [ReciprocityTheory.AnForm.M.mIntCongrNull A Φ Vᶜ hAn hint f (V.indicator f) (fun x hx => by
    rw [Set.indicator_of_mem (Set.not_notMem.mp hx)])]
  refine SystemIndependence.mInt_nonneg_on A V Φ hpot hnn _ (fun x => ?_)
    (fun x hx => Set.indicator_of_notMem hx _)
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]
    exact hf x
  · rw [Set.indicator_of_notMem hx]

theorem levi_smul' {ι : Type} [Fintype ι] {f : (ι → ℂ) → ℝ} {y : ι → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f y) (w : ι → ℂ) : levi (fun z => c * f z) y w = c * levi f y w := by
  have h := levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf w
  simp only [zero_add] at h
  rw [h, levi_const, zero_add]

theorem mixedForms_eq_cons {W : Type} [TopologicalSpace W] {D : ℕ} (Om : LocPot W)
    (T : Fin (D + 1) → LocPot W) (a : ℕ) (ha : a < D + 1) :
    mixedForms Om T a = Fin.cons Om (restForms Om T a) ∘ Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1)) := by
  funext i
  simp only [Function.comp_apply, mixedForms]
  rcases lt_trichotomy i ⟨a, ha⟩ with h | h | h
  · have hi : (i : ℕ) < a := h
    have hD : (i : ℕ) < D := by omega
    have hc : Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1)) i = Fin.succ ⟨i, hD⟩ :=
      Fin.ext (by simp [Fin.coe_cycleRange_of_lt h])
    rw [hc, Fin.cons_succ, if_pos hi]
    simp only [restForms, if_pos hi]
    rfl
  · rw [h, Fin.cycleRange_self, Fin.cons_zero, if_neg (lt_irrefl a)]
  · have hi : a < (i : ℕ) := h
    have hne : i ≠ 0 := fun h0 => by rw [h0] at hi; exact Nat.not_lt_zero _ hi
    rw [Fin.cycleRange_of_gt h, if_neg (by omega)]
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hne
    rw [Fin.cons_succ]
    simp only [restForms]
    rw [if_neg]
    simp only [Fin.val_succ] at hi
    omega

variable {D : ℕ} {W : Type} [TopologicalSpace W]

theorem divInt_linear [CompactSpace W] [T2Space W] (S : UIData D W) (Φ : Fin D → LocPot W)
    (hΦ : ∀ i, IsPotential S.A (Φ i)) (c : ℝ) {f g : W → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    S.divInt Φ (fun x => c * f x + g x) = c * S.divInt Φ f + S.divInt Φ g := by
  unfold UIData.divInt
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : CompactSpace (S.comp k) := isCompact_iff_compactSpace.mp
    (ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.isClosed_divisorComponent S.A S.L S.s S.mult S.comp S.s_snc k).isCompact
  have hpot : ∀ i, IsPotential (S.B k) (restrictForms (S.comp k) Φ i) := fun i =>
    ReciprocityTheory.AnForm.M.isPotentialPullback S.A (S.B k) Subtype.val (S.B_holo k) (Φ i) (hΦ i)
  have h := ReciprocityTheory.AnForm.M.mIntLinear (S.B k) (restrictForms (S.comp k) Φ) hpot c
    (f ∘ Subtype.val) (g ∘ Subtype.val)
    (ReciprocityTheory.AnForm.M.mIntegrableCont _ _ hpot _ (hf.comp continuous_subtype_val))
    (ReciprocityTheory.AnForm.M.mIntegrableCont _ _ hpot _ (hg.comp continuous_subtype_val))
  have e : ((fun x => c * f x + g x) ∘ Subtype.val : S.comp k → ℝ) =
      fun x => c * (f ∘ Subtype.val) x + (g ∘ Subtype.val) x := rfl
  rw [e, h]
  ring

end GreenMassReplace

open GreenMassReplace in
theorem GreenMassReplace.proof : GreenMassReplace.Statement := by
  intro D W _ _ _ S
  obtain ⟨Cκ, hCκ0, hκ⟩ := kappaEp_formNonneg S.Om S.L_pot S.s_sec
  refine ⟨Cκ, hCκ0, fun a ha t₀ ht₀ hℓ₀ => ?_⟩
  have hform₀ := S.form ⟨a, ha⟩ t₀ ht₀ hℓ₀
  set ut : W → ℝ := fun x => S.u ⟨a, ha⟩ t₀ x + S.C * errE S.C t₀ with hutdef
  have hut : S.A.Smooth ut := fun j => (hform₀.2 j).add contDiffOn_const
  have hutpot : IsPotential S.A (LocPot.ofFun ut) := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ hut
  obtain ⟨K, hK0, hK⟩ := levi_abs_le_global S.A isCompact_univ (LocPot.ofFun ut) S.Om.pot hutpot
    S.Om.isPot S.Om.pos
  refine ⟨K, hK0, fun ε t hε _ ht htt => ?_⟩
  have hℓ : S.ell₀ ≤ ell t := hℓ₀.trans (ell_anti ht htt)

  have hTpot : ∀ j, IsPotential S.A (S.T t j) := fun j =>
    ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form j t ht hℓ).1.th_pot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ (S.form j t ht hℓ).2)
  have hTnn : ∀ j, FormNonneg S.A S.Yo (S.T t j) := fun j => (S.form j t ht hℓ).1.nonneg
  set Φ' := S.rest a t with hΦ'
  have hΦpot : ∀ i, IsPotential S.A (Φ' i) := by
    intro i
    simp only [hΦ', UIData.rest, restForms]
    split_ifs
    · exact hTpot _
    · exact S.Om.isPot
  have hΦnn : ∀ i, FormNonneg S.A S.Yo (Φ' i) := by
    intro i
    simp only [hΦ', UIData.rest, restForms]
    split_ifs
    · exact hTnn _
    · exact formNonneg_kaehler S.Om S.Yo
  have hcons : ∀ P, IsPotential S.A P →
      ∀ i, IsPotential S.A ((Fin.cons P Φ' : Fin (D + 1) → LocPot W) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hP
    · simpa using hΦpot j
  have hconsnn : ∀ P, FormNonneg S.A S.Yo P →
      ∀ i, FormNonneg S.A S.Yo ((Fin.cons P Φ' : Fin (D + 1) → LocPot W) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hP
    · simpa using hΦnn j
  have hκpot := isPotential_kappaEp S.L_pot S.s_sec hε
  have hOmK : ∀ c : ℝ, IsPotential S.A (S.Om.pot.rsmul c) := fun c =>
    ReciprocityTheory.AnForm.M.isPotentialRsmul S.A c _ S.Om.isPot

  set u := S.u ⟨a, ha⟩ t with hudef
  have hu : S.A.Smooth u := (S.form ⟨a, ha⟩ t ht hℓ).2
  have hut_c : Continuous ut := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hut
  have hu_c : Continuous u := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hu
  set g := S.gap a ha t₀ t with hgdef
  have hg_eq : g = fun x => ut x - u x := rfl
  have hg_c : Continuous g := by rw [hg_eq]; exact hut_c.sub hu_c
  have hgnn : ∀ x, 0 ≤ g x := fun x => by
    have := S.mono ⟨a, ha⟩ t t₀ ht htt hℓ₀ x
    rw [hg_eq]
    simp only [hutdef, hudef]
    linarith
  have hu_eq : (fun x => -1 * g x + ut x) = u := by
    funext x
    rw [hg_eq]
    ring
  set F := logNormSqAdd S.L S.s ε with hFdef
  have hF : S.A.Smooth F := smooth_logNormSqAdd S.L_pot S.s_sec hε
  have hF_c : Continuous F := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous hF
  have hint : ∀ P, IsPotential S.A P → ∀ f : W → ℝ, Continuous f →
      MIntegrable S.A (Fin.cons P Φ') f := fun P hP f hf =>
    ReciprocityTheory.AnForm.M.mIntegrableCont S.A _ (hcons P hP) f hf

  have sA : mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') u =
      mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') ut -
        mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') g := by
    have h := ReciprocityTheory.AnForm.M.mIntLinear S.A _ (hcons _ hκpot) (-1) g ut
      (hint _ hκpot g hg_c) (hint _ hκpot ut hut_c)
    rw [hu_eq] at h
    linarith

  have sB : 0 ≤ mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') g +
      Cκ * mInt S.A (Fin.cons S.Om.pot Φ') g := by
    have hPpot : IsPotential S.A (kappaEp S.L S.s ε + S.Om.pot.rsmul Cκ) :=
      ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ hκpot (hOmK Cκ)
    have h0 := mInt_nonneg_of_compl S.A S.Yo S.bd_analytic S.bd_interior _ (hcons _ hPpot)
      (hconsnn _ (formNonneg_mono (hκ ε hε))) g hgnn
    rw [ReciprocityTheory.AnForm.M.mIntAdd S.A _ _ Φ' hκpot (hOmK Cκ) hΦpot g (hint _ hκpot g hg_c)
      (hint _ (hOmK Cκ) g hg_c),
      ReciprocityTheory.AnForm.M.mIntRsmul S.A Cκ S.Om.pot Φ' S.Om.isPot hΦpot g] at h0
    exact h0

  have sC : S.divInt Φ' u = S.divInt Φ' ut - S.divInt Φ' g := by
    have h := divInt_linear S Φ' hΦpot (-1) hg_c hut_c
    rw [hu_eq] at h
    linarith

  set H : W → ℝ := fun x => -2 * logNormSec S.L S.s x + F x with hHdef
  have hlns : ∀ P, IsPotential S.A P → MIntegrable S.A (Fin.cons P Φ') (logNormSec S.L S.s) :=
    fun P hP => ReciprocityTheory.AnForm.M.logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec
      S.s_snc _ (hcons P hP)
  have sD : mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') ut - 2 * S.divInt Φ' ut =
      mInt S.A (Fin.cons (LocPot.ofFun ut) Φ') H := by
    have hL2 := ReciprocityTheory.AnForm.M.isPotentialRsmul S.A 2 S.L S.L_pot
    have hFpot : IsPotential S.A (LocPot.ofFun F) := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ hF
    have hadd := ReciprocityTheory.AnForm.M.mIntAdd S.A (S.L.rsmul 2) (LocPot.ofFun F) Φ' hL2 hFpot hΦpot ut
      (hint _ hL2 ut hut_c) (hint _ hFpot ut hut_c)
    have hrs := ReciprocityTheory.AnForm.M.mIntRsmul S.A 2 S.L Φ' S.L_pot hΦpot ut
    have hbp := ReciprocityTheory.AnForm.M.byPartsSymm S.A ut F hut hF Φ' hΦpot
    have hpl := ReciprocityTheory.AnForm.M.poincareLelong S.A S.L S.s S.mult S.comp S.B S.L_pot S.s_sec
      S.s_snc S.B_holo ut hut Φ' hΦpot
    have hlin := ReciprocityTheory.AnForm.M.mIntLinear S.A _ (hcons _ hutpot) (-2) (logNormSec S.L S.s) F
      (hlns _ hutpot) (hint _ hutpot F hF_c)
    have hk : kappaEp S.L S.s ε = S.L.rsmul 2 + LocPot.ofFun F := rfl
    have hdiv : S.divInt Φ' ut = ∑ k, (S.mult k : ℝ) * mInt (S.B k)
        (fun i => (Φ' i).pullback Subtype.val continuous_subtype_val) (ut ∘ Subtype.val) := rfl
    rw [hk, hadd, hrs, hbp, hdiv]
    rw [show (fun x => -2 * logNormSec S.L S.s x + F x) = H from rfl] at hlin
    rw [hlin]
    linarith

  have hZ := zeroSet_analytic (A := S.A) S.s_sec
  have hZi := interior_zeroSet S.s_sec S.s_snc
  have hGH : ∀ x ∉ zeroSet S.s, S.green ε x = H x := fun x hx =>
    greenEp_eq_off S.L S.s hε hx
  have hHint : ∀ P, IsPotential S.A P → MIntegrable S.A (Fin.cons P Φ') H := by
    intro P hP j K' hK' hKc
    have h1 := hlns P hP j K' hK' hKc
    have h2 := hint P hP F hF_c j K' hK' hKc
    exact IntegrableOn.congr_fun ((h1.const_mul (-2)).add h2)
      (fun y _ => by simp only [hHdef, Pi.add_apply]; ring) hKc.measurableSet
  have hPnn : FormNonneg S.A Set.univ ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K) := by
    intro x k y hy w
    have hyt : y ∈ (S.A.chart k).target := hy.1
    have hyΩ : (S.A.chart k).symm y ∈ S.Om.pot.U x := hy.2.2.2
    have hu2 : ContDiffAt ℝ 2 ((LocPot.ofFun ut).φ x ∘ (S.A.chart k).symm) y :=
      ReciprocityTheory.AnForm.M.pot_contDiffAt_two hutpot x k hyt trivial
    have hΨ2 : ContDiffAt ℝ 2 (S.Om.pot.φ x ∘ (S.A.chart k).symm) y :=
      ReciprocityTheory.AnForm.M.pot_contDiffAt_two S.Om.isPot x k hyt hyΩ
    have hsum : ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K).φ x ∘ (S.A.chart k).symm =
        fun z => (fun z' => -1 * ((LocPot.ofFun ut).φ x ∘ (S.A.chart k).symm) z') z +
          K * (S.Om.pot.φ x ∘ (S.A.chart k).symm) z := rfl
    rw [hsum, levi_add_smul K (contDiffAt_const.mul hu2) hΨ2 w, levi_smul' (-1) hu2 w]
    have hb := abs_le.mp (hK x k y ⟨hyt, trivial, hyΩ⟩ w)
    linarith [hb.2]
  have sE : 0 ≤ -mInt S.A (Fin.cons (LocPot.ofFun ut) Φ') H +
      K * mInt S.A (Fin.cons S.Om.pot Φ') H := by
    have hm1 := ReciprocityTheory.AnForm.M.isPotentialRsmul S.A (-1) _ hutpot
    have hPpot : IsPotential S.A ((LocPot.ofFun ut).rsmul (-1) + S.Om.pot.rsmul K) :=
      ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ hm1 (hOmK K)
    have h0 := mInt_nonneg_of_compl S.A S.Yo S.bd_analytic S.bd_interior _ (hcons _ hPpot)
      (hconsnn _ (formNonneg_mono hPnn)) (S.green ε)
      (fun x => GreenMassReplace.greenEp_nonneg S.L S.s hε x)
    rw [ReciprocityTheory.AnForm.M.mIntCongrNull S.A _ (zeroSet S.s) hZ hZi (S.green ε) H hGH,
      ReciprocityTheory.AnForm.M.mIntAdd S.A _ _ Φ' hm1 (hOmK K) hΦpot H (hHint _ hm1) (hHint _ (hOmK K)),
      ReciprocityTheory.AnForm.M.mIntRsmul S.A (-1) _ Φ' hutpot hΦpot H,
      ReciprocityTheory.AnForm.M.mIntRsmul S.A K S.Om.pot Φ' S.Om.isPot hΦpot H] at h0
    linarith

  have hperm : ∀ f : W → ℝ, mInt S.A (mixedForms S.Om.pot (S.T t) a) f =
      mInt S.A (Fin.cons S.Om.pot Φ') f := fun f => by
    rw [mixedForms_eq_cons S.Om.pot (S.T t) a ha, ReciprocityTheory.AnForm.M.mIntSymm]
    rfl
  have hJ : S.J a ε t = mInt S.A (Fin.cons S.Om.pot Φ') H := by
    rw [← ReciprocityTheory.AnForm.M.mIntCongrNull S.A _ (zeroSet S.s) hZ hZi (S.green ε) H hGH]
    exact hperm _
  have hW : S.errW a ha t₀ t = mInt S.A (Fin.cons S.Om.pot Φ') g := hperm _
  have hP : S.plTerm a ha ε t = mInt S.A (Fin.cons (kappaEp S.L S.s ε) Φ') u -
      2 * S.divInt Φ' u := rfl
  have hD : S.errDiv a ha t₀ t = S.divInt Φ' g := rfl
  rw [hP, hJ, hW, hD, sA, sC]
  nlinarith [sA, sB, sC, sD, sE]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
