import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceIndep

theorem sum_dual_smul_eq_zero {W ι I : Type} [AddCommGroup W] [Module ℂ W] (F : Subfield ℂ) {b : ι → W}
    (hb : LinearIndependent ℂ b) {v : I → W} (hv : ∀ a, v a ∈ Submodule.span F (Set.range b)) (s : Finset I) (c : I → ℂ)
    (h : ∑ a ∈ s, c a • v a = 0) (φ : Module.Dual F ℂ) : ∑ a ∈ s, φ (c a) • v a = 0 := by
  classical
  choose g hg using fun a => Finsupp.mem_span_range_iff_exists_finsupp.1 (hv a)
  set t := s.biUnion fun a => (g a).support with ht
  have hv' : ∀ a ∈ s, v a = ∑ k ∈ t, g a k • b k := fun a ha => by
    rw [← hg a]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun a => (g a).support) ha) _ fun _ _ => zero_smul _ _
  have h1 : ∑ k ∈ t, (∑ a ∈ s, g a k • c a) • b k = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv' a ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_assoc, smul_comm]
  have h2 := linearIndependent_iff'.1 hb t _ h1
  rw [Finset.sum_congr rfl fun a ha => by rw [hv' a ha, Finset.smul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have h3 := congrArg φ (h2 k hk)
  rw [map_sum, map_zero] at h3
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, Finset.sum_congr rfl fun a _ => by rw [mul_comm, ← smul_eq_mul, ← map_smul], h3, zero_smul]

theorem coefLatFn_mem_span {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {F : Subfield ℂ} (hF : O ≤ F.toSubring)
    (lam : D.what₂.Tau → DomWeight n) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {φ : GLR D n → ℂ}
    (h : φ ∈ coefLatFn σ emb O lam M) :
    φ ∈ Submodule.span F (Set.range fun k => HarmLattice.cf lam (GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k))) := by
  have hσ : ∀ x : K, σ x ∈ F := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    rw [map_div₀]
    exact div_mem (hF (hc.int a)) (hF (hc.int b))
  induction h using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨G, -, rfl⟩ := h
    rw [HarmLattice.coefFn_eq]
    have hG : G ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hG using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
    | smul a G _ h1 =>
      rw [LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hσ a⟩ : F) h1
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c.1, hF c.2⟩ : F) h1

theorem linearIndependent_complex : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ F : Subfield ℂ, O ≤ F.toSubring →
  ∀ (I : Type) (f : I → Bridge.Gf S → PolF D T.rank S.rank), (∀ a h, f a h ∈ B.coefLat σ emb O h) → LinearIndependent F f → LinearIndependent ℂ f := by
  intro D S T B hB K _ _ σ emb O hc F hF I f hf hli
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hcf : Function.Injective (HarmLattice.cf B.w.lam) :=
    (injective_iff_map_eq_zero _).2 fun G hG => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D _ B.w.lam G fun x => congrFun hG x)
  have hb := (GlobalTheory.CoefModel.linearIndependent_mapVV σ B.w.lam).map' (HarmLattice.cf B.w.lam) (LinearMap.ker_eq_bot.2 hcf)
  refine linearIndependent_iff'.2 fun s c h a ha => (Module.forall_dual_apply_eq_zero_iff F (c a)).1 fun φ => ?_
  refine linearIndependent_iff'.1 hli s (fun a => φ (c a)) (funext fun y => ?_) a ha
  refine GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ ?_ ?_
  · rw [Finset.sum_apply]
    exact sum_mem fun a _ => Submodule.smul_mem _ (φ (c a) : ℂ) (hf a y).1
  · have h0 := congrArg (harmFn T.rank B.w B.F.BS) (congrFun h y)
    rw [Finset.sum_apply, map_sum, Pi.zero_apply, map_zero] at h0
    simp only [Pi.smul_apply, map_smul] at h0
    have := sum_dual_smul_eq_zero F hb (fun a => coefLatFn_mem_span hc hF B.w.lam _ (hf a y).2) s c h0 φ
    rw [Finset.sum_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun a _ => (harmFn T.rank B.w B.F.BS).map_smul (φ (c a) : ℂ) (f a y)

end GlobalTheory.PlaceIndep

end
