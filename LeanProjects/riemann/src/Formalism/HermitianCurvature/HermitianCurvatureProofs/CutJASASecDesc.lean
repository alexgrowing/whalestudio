import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def EqvL (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (J : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  LeftEq k r z i D J ∧ RightEq k r z' i D J ∧
    ∀ g ∈ Glev k r i ∩ D, ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', J (h * g * h') = (π h).comp ((J g).comp (π' h'))

def FamD (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  (∀ c ∈ OmX r, EqvL z z' π π' i D (Φ c)) ∧
  ∀ c₀ ∈ OmX r, ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → (Wq →L[ℂ] Wp)),
    IsOpen U ∧ (c₀, g₀) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ U, x.1 ∈ OmX r → x.2 ∈ Glev k r i → x.2 ∈ D → Φ x.1 x.2 = F x

theorem famD_FFl {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsOpen D) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' i D Φ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' i D := by
  refine ⟨?_, (hΦ.1 c hc).1, (hΦ.1 c hc).2.1, (hΦ.1 c hc).2.2⟩
  intro g₀ hg₀
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2 c hc g₀ hg₀
  refine ⟨(fun g => (c, g)) ⁻¹' U ∩ D, fun g => F (c, g), (hU.preimage (by fun_prop)).inter hD, ⟨hx, hg₀.2⟩, ?_,
    fun g hg hgl => hΦF (c, g) hg.1 hc hgl hg.2⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg.1)

theorem upd_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {c'' : ℂ} (h : c'' ≠ 0) (l : Fin r) :
    Function.update c l c'' ∈ OmX r := by
  intro a
  by_cases ha : a = l
  · subst ha; simpa using h
  · simpa [Function.update_apply, ha] using hc a

def JxF (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
    Φ (Function.update c l (cF k r l g)) (rho k r l g)

theorem dec_JxF {l : Fin r} {g u g₁ u' : Mx k r} {c' : ℂ} (h : Dec k r l g c' u g₁ u')
    (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) :
    JxF l z z' Φ c g = (psi k r z cStd u * psi k r z' cStd u') • Φ (Function.update c l c') g₁ := by
  unfold JxF
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]

theorem descended_function_apply_w1_mul {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) {c' : ℂ} (hc' : c' ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    JxF l z z' Φ c (w1 k r l c' * g) = Φ (Function.update c l c') g := by
  rw [dec_JxF (dec_w hc' hg), psi_one hz, psi_one hz', one_mul, one_smul]

theorem w1_mul_mem_descended_set_iff (l : Fin r) (D₁ : Set (Mx k r)) {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ D0 k r l D₁ ↔ g ∈ D₁ := by
  have d := dec_w (l := l) hc hg
  constructor
  · intro h
    have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
    rwa [d.rho_eq] at h2
  · intro h
    refine ⟨d.cell_decomposition_mem, ?_⟩
    show rho k r l (w1 k r l c * g) ∈ D₁
    rw [d.rho_eq]; exact h

theorem smM_snd (s : Set ((Fin r → ℂ) × Mx k r)) : SmM (fun x : (Fin r → ℂ) × Mx k r => x.2) s := fun i j =>
  ((contDiff_apply_apply ℝ ℂ i j).comp contDiff_snd).contDiffOn

theorem descended_set_is_domain {z z' : Fin (2 * r + k + 1) → ℂ} (l : Fin r) {D₁ : Set (Mx k r)} (hD₁ : IsDom k r z z' l.succ D₁) :
    IsDom k r z z' l.castSucc (D0 k r l D₁) := by
  refine ⟨isOpen_cell_domain hD₁.1, ?_⟩
  rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
  obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
  obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
  have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
  have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
  have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
  have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
  rw [e2]; exact h2

theorem famStep {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) {D₁ : Set (Mx k r)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' l.succ D₁ Φ) :
    FamD z z' π π' l.castSucc (D0 k r l D₁) (JxF l z z' Φ) := by
  refine ⟨fun c hc => ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    have hL := (hΦ.1 _ (upd_mem hc d.hc l)).1 g₁ ⟨d.hg, hg₁⟩ n₁ hn₁
    rw [Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hL,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    have hR := (hΦ.1 _ (upd_mem hc d.hc l)).2.1 g₁ ⟨d.hg, hg₁⟩ n₃ hn₃
    rw [← Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hR,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    have hW := (hΦ.1 _ (upd_mem hc d.hc l)).2.2 g₁ ⟨d.hg, hg₁⟩ h hh h' hh'
    rw [dec_JxF d1, dec_JxF d, hW, psi_conjW hz hh (up_nset d.hu), psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  ·
    intro c₀ hc₀ g₀ hg₀
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΦ.2 (Function.update c₀ l c'') (upd_mem hc₀ d.hc l) g₁ ⟨d.hg, hg₁⟩
    have hs0 : IsOpen {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := isOpen_adelicUnipotentTimesIntegralOutsideSet.preimage continuous_snd
    have h1 := smM_snd (k := k) (r := r) {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l}
    have hupd : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => Function.update x.1 l (cF k r l x.2))
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := by
      refine contDiffOn_pi.2 fun a => ?_
      by_cases ha : a = l
      · subst ha
        exact (sm_cF (l := a) h1).congr fun x _ => by simp
      · exact ((contDiff_apply ℝ ℂ a).comp contDiff_fst).contDiffOn.congr fun x _ => by
          simp [ha]
    have hrho : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => rho k r l x.2)
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} :=
      (smM_contDiffOn smM_rho).comp contDiff_snd.contDiffOn fun x hx => hx
    have hm := hupd.prodMk hrho
    refine ⟨{x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
        (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁,
      fun x => (psi k r z cStd (uL k r l x.2) * psi k r z' cStd (iH (uL k r l (iH x.2)))) •
        F₁ (Function.update x.1 l (cF k r l x.2), rho k r l x.2),
      hm.continuousOn.isOpen_inter_preimage hs0 hU₁, ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show (Function.update c₀ l (cF k r l g₀), rho k r l g₀) ∈ U₁
      rw [d.cF_eq, d.rho_eq]; exact hmem
    · have hs : {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁ ⊆
          {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := Set.inter_subset_left
      have h1' := smM_snd (k := k) (r := r) ({x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁)
      have h2 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l x.2) _ := smM_uL h1' fun x hx => hx.1.1
      have h3 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l (iH x.2)) _ := smM_uL (smM_iH h1') fun x hx => hx.1.2
      have h5 := hF₁.comp (hm.mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul h5
    · intro x hxU hx1 hxG hxD
      obtain ⟨u3, g3, u3', d3⟩ := dec_exists hxG hxU.1.1
      have hy := hag (Function.update x.1 l (cF k r l x.2), rho k r l x.2) hxU.2 (upd_mem hx1 hxU.1.1 l)
        (by show rho k r l x.2 ∈ Glev k r l.succ; rw [d3.rho_eq]; exact d3.hg) hxD.2
      show JxF l z z' Φ x.1 x.2 = _
      unfold JxF
      rw [hy]

end fam

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc
