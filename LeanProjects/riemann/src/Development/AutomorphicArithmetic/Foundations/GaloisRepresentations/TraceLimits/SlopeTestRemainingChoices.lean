import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL
open Polynomial

namespace UpperTheory.Gal.Lim

theorem approx_index {k J I : Type} [NormedField k] [IsUltrametricDist k] {θ : J → k} {η : I → J → k} {A : Set I}
    (h : PolyApprox θ (η '' A)) {ε : ℝ} (hε : 0 < ε) : ∃ (F : Finset I) (c : I → k), (↑F : Set I) ⊆ A ∧
      ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε := by
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  choose ι hιA hιη using fun e : s => hs e.2
  have inj : Function.Injective ι := fun e₁ e₂ h => Subtype.ext (by rw [← hιη e₁, ← hιη e₂, h])
  refine ⟨Finset.univ.image ι, fun i => c (η i), ?_, fun P => ?_⟩
  · intro i hi
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hιA e
  rw [Finset.sum_image inj.injOn]
  simp only [hιη]
  rw [Finset.sum_coe_sort s fun e => c e * MvPolynomial.aeval e P]
  exact hP P

theorem approx_left {k J J' I : Type} [NormedField k] [IsUltrametricDist k] {θ : J → k} {θ' : J' → k} {η : I → J → k}
    {η' : I → J' → k} {A : Set I} (h : PolyApprox (Sum.elim θ θ') ((fun i => Sum.elim (η i) (η' i)) '' A)) :
    PolyApprox θ (η '' A) := by
  classical
  intro ε hε
  obtain ⟨F, c, hF, hP⟩ := approx_index h hε
  refine ⟨F.image η, fun e => ∑ i ∈ F.filter (fun i => η i = e), c i, ?_, fun P => ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    exact ⟨i, hF hi, rfl⟩
  have hsum : ∑ e ∈ F.image η, (∑ i ∈ F.filter (fun i => η i = e), c i) * MvPolynomial.aeval e P =
      ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := η) (t := F.image η) (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  have h0 := hP (MvPolynomial.rename Sum.inl P)
  simp only [MvPolynomial.aeval_rename, Sum.elim_comp_inl] at h0
  exact le_of_eq_of_le (congrArg (fun z => ‖MvPolynomial.aeval θ P - z‖) hsum) h0

theorem joint {k Γ J J' I : Type} [NormedField k] [IsUltrametricDist k] [Group Γ] {a : ℕ} {r : Γ →* GL (Fin a) k}
    {ρ : I → Γ →* GL (Fin a) k} {θ : J → k} {θ' : J' → k} {η : I → J → k} {η' : I → J' → k} {A : Set I}
    (h : PolyApprox (Sum.elim θ θ') ((fun i => Sum.elim (η i) (η' i)) '' A))
    (ht : ∀ (F : Finset I) (c : I → k) (ε : ℝ),
      (∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ i ∈ F, c i * MvPolynomial.aeval (η i) P‖ ≤ ε) →
      ∀ g, ‖trc r g - ∑ i ∈ F, c i * trc (ρ i) g‖ ≤ ε)
    (S : ℕ → k) (s : (Γ →* GL (Fin a) k) → ℕ → k) (p : ℕ → J') (u : ℕ → k) (hS : ∀ n, S n = u n * θ' (p n))
    (hs : ∀ i ∈ A, ∀ n, s (ρ i) n = u n * η' i (p n)) : GlobalTheory.CongPhi.JointApprox r (ρ '' A) S s := by
  classical
  intro n ε hε
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ j ≤ n, ‖u j‖ ≤ M :=
    ⟨1 + ∑ j ∈ Finset.range (n + 1), ‖u j‖, le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _), fun j hj =>
      (Finset.single_le_sum (f := fun j => ‖u j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))).trans
        (le_add_of_nonneg_left zero_le_one)⟩
  have hM0 : 0 < M := by linarith
  obtain ⟨F, c, hF, hP⟩ := approx_index h (div_pos hε hM0)
  have hsum : ∀ f : (Γ →* GL (Fin a) k) → k, ∑ e ∈ F.image ρ, (∑ i ∈ F.filter (fun i => ρ i = e), c i) * f e =
      ∑ i ∈ F, c i * f (ρ i) := fun f => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := ρ) (t := F.image ρ) (fun i hi => Finset.mem_image_of_mem _ hi)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
  refine ⟨F.image ρ, fun e => ∑ i ∈ F.filter (fun i => ρ i = e), c i, ?_, fun g => ?_, fun j hj => ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
    exact ⟨i, hF hi, rfl⟩
  · rw [hsum fun e => trc e g]
    refine (ht F c (ε / M) (fun P => ?_) g).trans (div_le_self hε.le hM1)
    have h0 := hP (MvPolynomial.rename Sum.inl P)
    simpa only [MvPolynomial.aeval_rename, Sum.elim_comp_inl] using h0
  · rw [hsum fun e => s e j]
    have h0 := hP (MvPolynomial.X (Sum.inr (p j)))
    simp only [MvPolynomial.aeval_X, Sum.elim_inr] at h0
    have e : S j - ∑ i ∈ F, c i * s (ρ i) j = u j * (θ' (p j) - ∑ i ∈ F, c i * η' i (p j)) := by
      rw [hS, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hs i (hF hi)]; ring
    rw [e, norm_mul]
    calc _ ≤ M * (ε / M) := mul_le_mul (hM j hj) h0 (norm_nonneg _) hM0.le
      _ = ε := by field_simp

theorem phiSum_satWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (σ : Weil h) (n : ℕ) :
    GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD h a B) σ n =
      ((UpperTheory.V.Af.algSat a (normV w) B).map fun z => z ^ (-(deg σ) * n : ℤ)).sum := by
  have e := Multiset.map_map (fun z : ℂ => X - C z) (fun b : ℂˣ =>
    (((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - a) / 2 : ℝ)) : ℂ)) ^ deg σ * ((b : ℂ)⁻¹) ^ deg σ) B
  rw [GlobalTheory.CongPhi.phiSum, GlobalTheory.SatChar.charPol_satWD]
  erw [← e]
  rw [roots_multiset_prod_X_sub_C, UpperTheory.V.Af.algSat]
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  have hq : (((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - a) / 2 : ℝ)) : ℂ)) = ((((normV w : ℕ) : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 2
    ring
  simp only [Function.comp_apply]
  rw [hq, ← mul_zpow, ← mul_inv, inv_zpow', zpow_mul, zpow_natCast]

theorem powSatU_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U)
    {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) {B : Multiset ℂˣ} (hB : SatU U w B) (n : ℤ) :
    PowSatU U w n = ((UpperTheory.V.Af.algSat a (normV w) B).map fun z => z ^ n).sum := by
  have h : ∃ B, SatU U w B := ⟨B, hB⟩
  obtain ⟨σ, hσ, h1⟩ := h.choose_spec
  obtain ⟨σ', hσ', h2⟩ := hB
  obtain ⟨e⟩ := (GlobalTheory.SplitComp.exists_comp_and_unique E a U hU w hw).2 _ _ hσ hσ'
  rw [PowSatU, dif_pos h, GlobalTheory.LFun.HasSatGL.unique (GlobalTheory.PrinSat.hasSatGL_of_equiv e.symm h1) h2]

end UpperTheory.Gal.Lim
