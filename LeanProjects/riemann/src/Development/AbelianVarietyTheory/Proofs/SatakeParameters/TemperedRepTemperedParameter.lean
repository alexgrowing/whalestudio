import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedSpecialOfUnitEigenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumTemperedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LocLanglands
namespace TemperedRec

theorem tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := GlobalTheory.T.tempered_direct_sum

theorem tempered_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), x.mono0 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ‖α‖ = 1) → ∀ l : ℕ, (x.lpChar (WD.lpSp h l)).tempered := GlobalTheory.T.tempered_special_of_unit_eigen

theorem norm_eig_eq_of_isIrrWD : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := GlobalTheory.T.irreducible_wd_eigen_equal_norm

theorem prod_eig_lpChar_lpSp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := GlobalTheory.T.lp_character_eigen_product

theorem not_precedes_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := GlobalTheory.T.segment_sum_tempered

theorem monodromy_zero_of_irreducible_weilDeligne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → x.mono0 := by
  intro E Ω _ _ _ _ _ A w h x ⟨n, a, hx, hirr⟩
  subst hx
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [Module.End.coe_pow]; exact hinj.iterate m
    rw [hm] at hinj'
    have := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · refine LinearMap.ext fun v => ?_
    have : v ∈ S.toSubmodule := by rw [hS]; trivial
    exact LinearMap.mem_ker.1 this

theorem tempered_lpZero {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : (WD.lpZero h).tempered :=
  (WD.tempered_mk _).mpr ((WD.tempered_diag_iff _).mpr fun i => i.elim0)

theorem tempered_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} :
    ∀ l : List (WD h), (∀ y ∈ l, y.tempered) → (sumList l).tempered
  | [], _ => tempered_lpZero h
  | y :: l, H => tempered_lpSum E Ω A w h y (sumList l) (H y (by simp))
      (tempered_sumList l fun z hz => H z (by simp [hz]))

theorem norm_centralChar_eq_one {k : Type} [CommRing k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] {π : Representation ℂ (GL (Fin n) k) V} {ω : kˣ →* ℂˣ} (hu : IsUnitarisable π)
    (hω : HasCentralChar π ω) (z : kˣ) : ‖(ω z : ℂ)‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := hinv (Matrix.GeneralLinearGroup.scalar (Fin n) z) v v
  rw [hω] at h1
  simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : ((ω z : ℂ) * starRingEnd ℂ (ω z : ℂ)) * B v v = 1 * B v v := by linear_combination h1
  have h3 := mul_right_cancel₀ hB h2
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
  have h4 : ‖(ω z : ℂ)‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem norm_eq_one_of_norm_prod {s : Multiset ℂ} (hp : ‖s.prod‖ = 1) (hs : ∀ α ∈ s, ∀ β ∈ s, ‖α‖ = ‖β‖) {α : ℂ}
    (hα : α ∈ s) : ‖α‖ = 1 := by
  have hmap : s.map (fun β => ‖β‖) = Multiset.replicate (Multiset.card s) ‖α‖ := by
    rw [Multiset.eq_replicate]
    refine ⟨by simp, fun r hr => ?_⟩
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hr
    exact (hs α hα β hβ).symm
  have h1 : ‖s.prod‖ = (s.map (fun β => ‖β‖)).prod := map_multiset_prod (normHom : ℂ →*₀ ℝ) s
  rw [hmap, Multiset.prod_replicate, hp] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Multiset.card_pos_iff_exists_mem.2 ⟨α, hα⟩).ne').1 h1.symm

theorem isCosocle_rep_cl {G : Type} [Group G] [TopologicalSpace G] (σ : IrrRep G) {V : Type} [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} (e : σ.ρ.Equiv π) : IsCosocle σ.cl.rep.ρ π := by
  obtain ⟨f⟩ := σ.nonempty_equiv_rep
  exact (isCosocle_self σ.irr).of_equiv f.symm e

theorem norm_eig_segParam {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (δ : IrrGL (w.adicCompletion E))
    (Δ : Segment (w.adicCompletion E)) (hΔ : IsLSeg Δ δ.rep) (hu : IsUnitarisable δ.rep) :
    ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1 := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  intro φ hφ
  have hz : (rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2) = rc (Δ.first.nu ((((Δ.len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 (Δ.isCusp_first.nu _)
  have hδ : rc δ = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
    have hL : IsL ((([Δ] : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))) δ.rep := by
      simpa using hΔ.isL
    rw [H.langlands [Δ] δ hL]
    exact WD.lpSum_zero _
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar δ.2.rep.smooth δ.2.rep.irr
  have : Nontrivial δ.2.rep.V := Model.nontrivial_of_isIrreducible δ.2.rep.irr
  have hc := H.central δ ω hω φ
  rw [hδ, prod_eig_lpChar_lpSp] at hc
  have hn : ‖((((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ).prod)‖ ^ Δ.len = 1 := by
    rw [← norm_pow, hc]; exact norm_centralChar_eq_one hu hω _
  have hp1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) Δ.len_pos.ne').1 hn
  intro α hα
  exact norm_eq_one_of_norm_prod hp1 (norm_eig_eq_of_isIrrWD E Ω A w h _ hirr φ hφ) hα

end TemperedRec

open TemperedRec in

theorem tempered_of_isTemperedGL : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  intro E Ω _ _ _ _ _ A w h rc hrc n σ hσ
  have hrc' := hrc
  obtain ⟨a, ha, ε, -, H⟩ := hrc'
  obtain ⟨m, δ, hd, hδ, ⟨e⟩⟩ := hσ
  choose Δ hΔ using fun i => (hδ i).1
  have hunit := fun i => norm_eig_segParam hrc (δ i) (Δ i) (hΔ i) (hδ i).2
  have hL : IsL (((List.ofFn Δ : List (Segment (w.adicCompletion E)))) : Multiset (Segment (w.adicCompletion E)))
      (cls σ).rep := by
    refine ⟨m, δ, hd, ⟨Δ, ⟨?_, fun i j _ hp => not_precedes_of_norm_eig E Ω A w h rc hrc (Δ i) (Δ j) (hunit i) (hunit j) hp⟩, hΔ⟩, ?_⟩
    · exact Fin.univ_val_map Δ
    · exact isCosocle_rep_cl σ e
  rw [H.langlands _ _ hL]
  refine tempered_sumList _ fun y hy => ?_
  obtain ⟨Γ, hΓ, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hΓ
  have hz : (rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2) = rc ((Δ i).first.nu (((((Δ i).len : ℝ) - 1) / 2 : ℝ) : ℂ)) :=
    (H.nu_eq _ _).symm
  have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
    rw [hz]; exact (H.cusp _).1 ((Δ i).isCusp_first.nu _)
  exact tempered_lpChar_lpSp E Ω A w h _ (monodromy_zero_of_irreducible_weilDeligne E Ω A w h _ hirr) (hunit i) _

end GlobalTheory.LocLanglands
