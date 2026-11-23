import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalLatticeDecomposition

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace MajorantOperators

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

private theorem hermC_smul_left_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (k : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (k • u) v = k * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hermC_add_left_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hermC_sub_left_of_natDim (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hermC_sub_right_of_conj_symm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem hermC_smul_right_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (k : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (k • v) = conj k * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private theorem hermC_emb_emb_eq_tau_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem Hf_zero_right (z : Frame X.Ψ r) (τ : X.Ψ) (u : Fin r → ℂ) : X.Hf z τ u 0 = 0 := by
  simp [Data.Hf, hermC]

theorem Hf_sub_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ u (v - w) = X.Hf z τ u v - X.Hf z τ u w := by
  simp only [Data.Hf, hermC_sub_right_of_conj_symm]

theorem maj_zero {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) : X.maj z τ 0 = 0 := by
  have h := X.Hf_self hz τ 0
  rw [Hf_zero_right] at h
  exact_mod_cast h.symm

theorem maj_nonneg {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero hz]
  · exact (X.maj_pos hz τ hv).le

theorem Hf_cs {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    ‖X.Hf z τ u w‖ ^ 2 ≤ X.maj z τ u * X.maj z τ w := by
  by_cases hw : w = 0
  · rw [hw, Hf_zero_right, maj_zero hz]
    simp
  have hmw := X.maj_pos hz τ hw
  have hww : X.Hf z τ w w = (X.maj z τ w : ℂ) := X.Hf_self hz τ w
  have hne : X.Hf z τ w w ≠ 0 := by
    rw [hww]
    exact_mod_cast hmw.ne'
  have hd := UnipotentCoefficientShift.maj_decomp hz τ u w hne
  rw [hww, norm_div, Complex.norm_real, Real.norm_of_nonneg hmw.le] at hd
  have h0 := maj_nonneg hz τ (u - (X.Hf z τ u w / (X.maj z τ w : ℂ)) • w)
  have e : (‖X.Hf z τ u w‖ / X.maj z τ w) ^ 2 * X.maj z τ w = ‖X.Hf z τ u w‖ ^ 2 / X.maj z τ w := by
    have := hmw.ne'
    field_simp
  have h1 : ‖X.Hf z τ u w‖ ^ 2 / X.maj z τ w ≤ X.maj z τ u := by
    rw [hd, ← e]
    linarith
  exact (div_le_iff₀ hmw).mp h1

theorem mem_Uz_iff (z : Frame X.Ψ r) (ξ : Fin r → E) (u : X.Ψ → Fin r → ℂ) :
    u ∈ X.Uz z ξ ↔ ∀ τ : X.Ψ, hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ) = 0 := by
  simp only [Data.Uz, Data.Iperp, Set.mem_setOf_eq, Data.Jz_apply, hermC_smul_left_embedding, mul_eq_zero,
    Complex.I_ne_zero, false_or]
  exact ⟨fun h τ => ⟨h.1 τ, h.2 τ⟩, fun h => ⟨fun τ => (h τ).1, fun τ => (h τ).2⟩⟩

theorem smul_fam_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (s : X.Ψ → ℂ) {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : (fun τ => s τ • u τ) ∈ X.Uz z ξ := by
  rw [mem_Uz_iff] at hu ⊢
  intro τ
  simp only [Data.jp_smul, hermC_smul_left_embedding, (hu τ).1, (hu τ).2, mul_zero, and_self]

theorem jp_fam_mem {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : (fun τ => X.jp z τ (u τ)) ∈ X.Uz z ξ := by
  rw [mem_Uz_iff] at hu ⊢
  intro τ
  exact ⟨(hu τ).2, by rw [X.jp_jp hz]; exact (hu τ).1⟩

theorem add_mem {z : Frame X.Ψ r} {ξ : Fin r → E} {u v : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) (hv : v ∈ X.Uz z ξ) : u + v ∈ X.Uz z ξ := by
  rw [mem_Uz_iff] at hu hv ⊢
  intro τ
  simp only [Pi.add_apply, Data.jp_add, hermC_add_left_embedding, (hu τ).1, (hu τ).2, (hv τ).1, (hv τ).2,
    add_zero, and_self]

theorem zero_mem (z : Frame X.Ψ r) (ξ : Fin r → E) : (0 : X.Ψ → Fin r → ℂ) ∈ X.Uz z ξ := by
  rw [mem_Uz_iff]
  intro τ
  have h0 : X.jp z τ 0 = 0 := by simpa using Data.jp_sub (X := X) z τ 0 0
  simp [h0, hermC]

theorem Hf_xi_of_mem {z : Frame X.Ψ r} {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) (τ : X.Ψ) : X.Hf z τ (u τ) (Data.emb τ.1 ξ) = 0 := by
  rw [Data.Hf_eq_jp]
  exact ((mem_Uz_iff z ξ u).mp hu τ).2

theorem ucomp_of_mem {z : Frame X.Ψ r} {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : X.ucomp z ξ u = u := by
  have h0 : X.aproj z ξ u = 0 := by
    funext τ
    simp [Data.aproj, Data.lineV, Hf_xi_of_mem hu τ]
  simp [Data.ucomp, h0]

noncomputable def gI (z : Frame X.Ψ r) (u v : X.Ψ → Fin r → ℂ) : ℝ := ∑ τ, (X.Hf z τ (u τ) (v τ)).re

noncomputable def Bop (z : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => (2 * τ.1 (-X.ξ0)) • X.jp z τ (u τ)

theorem conj_purely_imaginary_generator (τ : X.Ψ) : conj (τ.1 X.ξ0) = -τ.1 X.ξ0 := by
  rw [← emb_cc τ.1 X.ξ0, X.ξ0_im, map_neg]

theorem Bop_mem {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : Bop z u ∈ X.Uz z ξ :=
  smul_fam_mem _ (jp_fam_mem hz hu)

theorem Bop_add (z : Frame X.Ψ r) (u v : X.Ψ → Fin r → ℂ) : Bop z (u + v) = Bop z u + Bop z v := by
  funext τ
  simp [Bop, Data.jp_add, smul_add]

theorem Bop_smul (z : Frame X.Ψ r) (c : ℝ) (u : X.Ψ → Fin r → ℂ) : Bop z (c • u) = c • Bop z u := by
  funext τ
  simp only [Bop, Pi.smul_apply]
  rw [show c • u τ = (c : ℂ) • u τ by ext a; simp [Complex.real_smul], Data.jp_smul]
  ext a
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem gI_Bop_left {z : Frame X.Ψ r} (hz : z ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    gI z (Bop z u) v = ∑ τ, (2 * τ.1 (-X.ξ0) * hermC τ.1 X.Gm (u τ) (v τ)).re := by
  unfold gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Bop, UnipotentCoefficientShift.Hf_smul_left, Data.Hf_eq_jp, Data.jp_smul, hermC_smul_left_embedding, X.jp_jp hz]

theorem gI_Bop_right {z : Frame X.Ψ r} (hz : z ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    gI z u (Bop z v) = -gI z (Bop z u) v := by
  rw [gI_Bop_left hz, ← Finset.sum_neg_distrib]
  unfold gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Bop, UnipotentCoefficientShift.Hf_smul_right, Data.Hf_eq_jp, hermC_smul_right_embedding, X.hermC_jp_jp hz, map_mul, map_neg,
    conj_purely_imaginary_generator, neg_neg, map_ofNat]
  simp [neg_mul, mul_neg, Complex.neg_re]

theorem gI_add_left (z : Frame X.Ψ r) (u u' v : X.Ψ → Fin r → ℂ) :
    gI z (u + u') v = gI z u v + gI z u' v := by
  simp only [gI, Pi.add_apply, UnipotentCoefficientShift.Hf_add_left, Complex.add_re, Finset.sum_add_distrib]

theorem gI_smul_left (z : Frame X.Ψ r) (c : ℝ) (u v : X.Ψ → Fin r → ℂ) :
    gI z (c • u) v = c * gI z u v := by
  simp only [gI, Pi.smul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [show c • u τ = (c : ℂ) • u τ by ext a; simp [Complex.real_smul], UnipotentCoefficientShift.Hf_smul_left,
    Complex.re_ofReal_mul]

theorem gI_comm {z : Frame X.Ψ r} (hz : z ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    gI z u v = gI z v u := by
  unfold gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← UnipotentCoefficientShift.Hf_conj hz τ (u τ) (v τ), Complex.conj_re]

theorem gI_self {z : Frame X.Ψ r} (hz : z ∈ X.dom) (u : X.Ψ → Fin r → ℂ) :
    gI z u u = ∑ τ, X.maj z τ (u τ) := by
  simp only [gI, X.Hf_self hz, Complex.ofReal_re]

theorem trace_eq_sum (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 a).re := by
  classical

  have h1 : ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ a := by
    rw [show ((Algebra.trace ℚ E a : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E a) from (eq_ratCast _ _).symm,
      trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

  have h2 : ∑ σ ∈ X.Ψᶜ, σ a = ∑ σ ∈ X.Ψ, conj (σ a) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ]
      exact hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  apply Complex.ofReal_injective
  push_cast
  rw [h1, ← Finset.sum_add_sum_compl X.Ψ (fun σ => σ a), h2, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_conj]
  push_cast
  ring

private theorem hermC_ucomp_ucomp_of_herm_eq_zero {z : Frame X.Ψ r} {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0)
    {μ ν : Fin r → E} (hμ : herm X.Gm μ ξ = 0) (hν : herm X.Gm ν ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z ξ (X.embV μ) τ) (X.ucomp z ξ (X.embV ν) τ) = τ.1 (herm X.Gm μ ν) := by
  simp only [Data.ucomp, Data.aproj, Data.lineV, Data.embV, Pi.sub_apply]
  have e1 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_tau_herm, hμ, map_zero]
  have e2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ν) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm, hermC_emb_emb_eq_tau_herm, hν, map_zero, map_zero]
  have e3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_tau_herm, hξξ, map_zero]
  simp only [hermC_sub_left_of_natDim, hermC_sub_right_of_conj_symm, hermC_smul_left_embedding, hermC_smul_right_embedding, e1, e2, e3,
    mul_zero, sub_zero]
  exact hermC_emb_emb_eq_tau_herm _ _ _ _

theorem EF_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0)
    {μ ν : Fin r → E} (hμ : herm X.Gm μ ξ = 0) (hν : herm X.Gm ν ξ = 0) :
    ((EFf X.ξ0 X.Gm μ ν : ℚ) : ℝ) =
      gI z (Bop z (X.ucomp z ξ (X.embV μ))) (X.ucomp z ξ (X.embV ν)) := by
  unfold EFf
  rw [trace_eq_sum (X := X), gI_Bop_left hz]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hermC_ucomp_ucomp_of_herm_eq_zero hξξ hμ hν τ, map_mul, mul_assoc]
  simp [Complex.mul_re]
  ring

section dataX

variable {Y : DataX E r}

private theorem two_tau_neg_xi0_sq_eq_neg_k0_sq (τ : Y.Ψ) :
    (2 * τ.1 (-Y.ξ0)) * (2 * τ.1 (-Y.ξ0)) = -((Y.k0 : ℂ) ^ 2) := by
  have h1 := conj_purely_imaginary_generator (X := Y.toData) τ
  have h2 : τ.1 Y.ξ0 * conj (τ.1 Y.ξ0) = (((Y.k0 / 2) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ξ0_abs τ]
  rw [h1] at h2
  rw [map_neg]
  push_cast at h2 ⊢
  linear_combination -4 * h2

private theorem two_tau_neg_xi0_mul_conj_eq_k0_sq (τ : Y.Ψ) :
    (2 * τ.1 (-Y.ξ0)) * conj (2 * τ.1 (-Y.ξ0)) = ((Y.k0 ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, map_neg, norm_neg, Y.ξ0_abs τ]
  simp only [Complex.norm_ofNat]
  push_cast
  ring

theorem gI_Bop_self {z : Frame Y.Ψ r} (hz : z ∈ Y.dom) (u : Y.Ψ → Fin r → ℂ) :
    gI (X := Y.toData) z (Bop (X := Y.toData) z u) (Bop (X := Y.toData) z u) =
      Y.k0 ^ 2 * gI (X := Y.toData) z u u := by
  rw [gI_Bop_left hz]
  unfold gI
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Bop, hermC_smul_right_embedding, Data.Hf_eq_jp]
  rw [← Data.hermC_jp_left Y.toData hz, ← mul_assoc, two_tau_neg_xi0_mul_conj_eq_k0_sq τ, Complex.re_ofReal_mul]

theorem Bop_Bop {z : Frame Y.Ψ r} (hz : z ∈ Y.dom) (u : Y.Ψ → Fin r → ℂ) :
    Bop (X := Y.toData) z (Bop (X := Y.toData) z u) = (-(Y.k0 ^ 2) : ℝ) • u := by
  funext τ
  simp only [Bop, Data.jp_smul, Data.jp_jp Y.toData hz, smul_smul, Pi.smul_apply]
  rw [two_tau_neg_xi0_sq_eq_neg_k0_sq τ]
  ext a
  simp [Complex.real_smul]
end dataX

end MajorantOperators

end ReciprocityTheory.ChartRestriction.G.FD
