import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.PlaceSeriesJetsOneLetterOrbits
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Formalism.L2.DIV.C.X

open Formalism.L2.DIV Formalism.L2.DIV.C
open Formalism.L2.Th1.H (Sesq IsHerm IsSemiChar altE opU alphaQ qOf fixedBy dualLat IsReps sumU inter relIdx imgLat pow4
  slice stdH stdLat matH blk4 F0 prodFn kernel4 tens4 Th IsSelfDual IsIsom cmL)
open Formalism.L2.Th1.F (scalePair)
open Formalism.L2.Th1.Top (kappa_integral local_kappa_shape_holds frameExistsH)

section Transport

variable {V : Type} [AddCommGroup V] [Module ℂ V] {c : ℂ}

theorem gcm_mem_map_smul (hc : c ≠ 0) (A : AddSubgroup V) (x : V) :
    x ∈ A.map (DistribSMul.toAddMonoidHom V c) ↔ c⁻¹ • x ∈ A := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [DistribSMul.toAddMonoidHom_apply, inv_smul_smul₀ hc]
    exact hy
  · intro h
    exact ⟨c⁻¹ • x, h, by rw [DistribSMul.toAddMonoidHom_apply, smul_inv_smul₀ hc]⟩

theorem gcm_relIdx_map_smul (hc : c ≠ 0) (A B : AddSubgroup V) :
    relIdx (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c)) = relIdx A B :=
  AddSubgroup.relIndex_map_map_of_injective A B fun _ _ hxy => smul_right_injective V hc hxy

variable {H H' : Sesq V}

theorem gcm_opU_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x : V) (F : V → ℂ) (z : V) :
    opU H' x (fun w => F (c⁻¹ • w)) z = opU H (c⁻¹ • x) F (c⁻¹ • z) := by
  simp only [opU]
  rw [hH', hH', smul_add]

theorem gcm_alphaQ_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (r : ℝ) (x : V) :
    alphaQ r H' x = alphaQ r H (c⁻¹ • x) := by
  simp only [alphaQ, qOf]
  rw [hH']

theorem gcm_altE_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x y : V) :
    altE H' x y = altE H (c⁻¹ • x) (c⁻¹ • y) := by
  simp only [altE]
  rw [hH']

theorem gcm_isHerm_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H) : IsHerm H' := by
  intro x y
  rw [hH', hH', hH]

theorem gcm_semi_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {M : AddSubgroup V}
    {β : V → ℂ} (hβ : IsSemiChar H M β) :
    IsSemiChar H' (M.map (DistribSMul.toAddMonoidHom V c)) (fun x => β (c⁻¹ • x)) := by
  refine ⟨fun x hx => hβ.1 _ ((gcm_mem_map_smul hc M x).1 hx), fun x hx y hy => ?_⟩
  show β (c⁻¹ • (x + y)) = β (c⁻¹ • x) * β (c⁻¹ • y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H' x y : ℂ))
  rw [smul_add, gcm_altE_scale hH']
  exact hβ.2 _ ((gcm_mem_map_smul hc M x).1 hx) _ ((gcm_mem_map_smul hc M y).1 hy)

theorem gcm_fixed_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {S : AddSubgroup V}
    {β : V → ℂ} {F : V → ℂ} (hF : F ∈ fixedBy H β S) :
    (fun w => F (c⁻¹ • w)) ∈ fixedBy H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) := by
  intro x hx z
  show β (c⁻¹ • x) * opU H' x (fun w => F (c⁻¹ • w)) z = F (c⁻¹ • z)
  rw [gcm_opU_scale hH']
  exact hF _ ((gcm_mem_map_smul hc S x).1 hx) _

theorem gcm_reps_scale (hc : c ≠ 0) [DecidableEq V] {A B : AddSubgroup V} {R : Finset V} (hR : IsReps A B R) :
    IsReps (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c))
      (R.image (fun x => c • x)) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    rw [gcm_mem_map_smul hc, inv_smul_smul₀ hc]
    exact hR.1 x' hx'
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    rw [gcm_mem_map_smul hc, ← smul_sub, inv_smul_smul₀ hc] at hxy
    rw [hR.2.1 x' hx' y' hy' hxy]
  · obtain ⟨x, hx, hyx⟩ := hR.2.2 (c⁻¹ • y) ((gcm_mem_map_smul hc B y).1 hy)
    refine ⟨c • x, Finset.mem_image_of_mem _ hx, ?_⟩
    rw [gcm_mem_map_smul hc, smul_sub, inv_smul_smul₀ hc]
    exact hyx

theorem gcm_dualLat_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (Λ : AddSubgroup V) :
    dualLat H' (Λ.map (DistribSMul.toAddMonoidHom V c)) = (dualLat H Λ).map (DistribSMul.toAddMonoidHom V c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  show (∀ y ∈ Λ.map (DistribSMul.toAddMonoidHom V c), ∃ m : ℤ, altE H' x y = (m : ℝ)) ↔
    (∀ y ∈ Λ, ∃ m : ℤ, altE H (c⁻¹ • x) y = (m : ℝ))
  constructor
  · intro hx y hy
    have := hx (c • y) ((gcm_mem_map_smul hc Λ _).2 (by rw [inv_smul_smul₀ hc]; exact hy))
    rwa [gcm_altE_scale hH', inv_smul_smul₀ hc] at this
  · intro hx y hy
    rw [gcm_altE_scale hH']
    exact hx _ ((gcm_mem_map_smul hc Λ y).1 hy)

theorem gcm_inter_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H)
    {S M : AddSubgroup V} {β : V → ℂ} {F : V → ℂ} (hβ : IsSemiChar H M β) (hF : F ∈ fixedBy H β S)
    (hidx : relIdx S M ≠ 0) (w : V) :
    inter H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) (M.map (DistribSMul.toAddMonoidHom V c))
      (fun v => F (c⁻¹ • v)) w = inter H β S M F (c⁻¹ • w) := by
  classical
  obtain ⟨⟨R, hR⟩, -⟩ := Formalism.L2.Th1.H.repsExist V S M hidx
  rw [Formalism.L2.Th1.H.interReps V H' (gcm_isHerm_scale hH' hH) _ _ _ (gcm_semi_scale hc hH' hβ) _
      (gcm_fixed_scale hc hH' hF) _ (gcm_reps_scale hc hR) w,
    Formalism.L2.Th1.H.interReps V H hH S M β hβ F hF R hR (c⁻¹ • w), gcm_relIdx_map_smul hc]
  congr 1
  simp only [sumU]
  rw [Finset.sum_image fun _ _ _ _ hxy => smul_right_injective V hc hxy]
  refine Finset.sum_congr rfl fun x _ => ?_
  show β (c⁻¹ • c • x) * opU H' (c • x) (fun v => F (c⁻¹ • v)) w = β x * opU H x F (c⁻¹ • w)
  rw [gcm_opU_scale hH', inv_smul_smul₀ hc]

end Transport

section Forms

theorem gcm_inv_mul_conj (c : ℂ) : (c⁻¹ * conj c⁻¹ : ℂ) = ((Complex.normSq c : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, ← mul_inv, Complex.mul_conj]

theorem gcm_matH_scale {m : Type} [Fintype m] (c : ℂ) (M : Matrix m m ℂ) (u v : m → ℂ) :
    matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • M) u v = matH M (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.matHBasic m _).1, (Formalism.L2.Th1.H.matHBasic m M).1, ← gcm_inv_mul_conj c]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul]
  ring

theorem blockFour_smul {n : Type} (k : ℂ) (h : Matrix n n ℂ) : blk4 (k • h) = k • blk4 h := by
  funext w w'
  simp only [blk4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem gcm_stdH_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) [Fintype m] [DecidableEq m]
    (u v : m → ℂ) : stdH (scalePair L c hc) m u v = stdH L m (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.stdHBasic _ m).1, (Formalism.L2.Th1.H.stdHBasic L m).1]
  have hA := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.1
  have key : (c⁻¹ * conj c⁻¹ : ℂ) = ((‖c‖ : ℂ) ^ 2)⁻¹ := by
    rw [map_inv₀, ← mul_inv, Complex.mul_conj']
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Formalism.L2.Th1.F.herm, hA, Pi.smul_apply, smul_eq_mul, map_mul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_inv]
  rw [← key]
  ring

theorem gcm_stdLat_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) :
    stdLat (scalePair L c hc) m = (stdLat L m).map (DistribSMul.toAddMonoidHom (m → ℂ) c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [stdLat, AddSubgroup.mem_pi, Submodule.mem_toAddSubgroup, (Formalism.L2.Th1.F.homogeneity L c hc).1,
    Pi.smul_apply, smul_eq_mul]

theorem gcm_imgLat_scale {W : Type} [AddCommGroup W] [Module ℂ W] {n : Type} (c : ℂ) (hc : c ≠ 0)
    (g : (Fin 4 × n → ℂ) →ₗ[ℂ] W) (Λ : AddSubgroup (n → ℂ)) :
    imgLat g (pow4 (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))) =
      (imgLat g (pow4 Λ)).map (DistribSMul.toAddMonoidHom W c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ a, slice a y ∈ Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c) := hy
    refine ⟨c⁻¹ • y, fun a => (gcm_mem_map_smul hc Λ _).1 (hy' a), ?_⟩
    simp
  · rintro ⟨y, hy, hyx⟩
    have hy' : ∀ a, slice a y ∈ Λ := hy
    refine ⟨c • y, fun a => (gcm_mem_map_smul hc Λ _).2 ?_, ?_⟩
    · have : c⁻¹ • slice a (c • y) = slice a y := by
        funext i
        simp only [slice, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
      rw [this]
      exact hy' a
    · simp only [LinearMap.toAddMonoidHom_coe] at hyx ⊢
      rw [map_smul, hyx, smul_inv_smul₀ hc]

theorem periodF0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (m : Type) [Fintype m]
    (w : m → ℂ) : F0 (scalePair L c hc) (c * ω₀) m w = F0 L ω₀ m (c⁻¹ • w) := by
  simp only [F0, prodFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h9 := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.2.2.2.1 (ω₀ / 2) (c⁻¹ * w i)
  rw [mul_inv_cancel_left₀ hc] at h9
  rw [show c * ω₀ / 2 = c * (ω₀ / 2) by ring, h9]
  rfl

theorem gcm_scalePair_scalePair (L : PeriodPair) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    scalePair (scalePair L a ha) b hb = scalePair L (a * b) (mul_ne_zero ha hb) := by
  show PeriodPair.mk _ _ _ = PeriodPair.mk _ _ _
  congr 1
  · show b * (a * L.ω₁) = _
    ring
  · show b * (a * L.ω₂) = _
    ring

theorem gcm_kernel4_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (r : ℝ) {n : Type} [Fintype n]
    [DecidableEq n] (Λ : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hβ : IsSemiChar (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (alphaQ r (stdH L (Fin 4 × n))))
    (hF : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) (alphaQ r (stdH L (Fin 4 × n))) (stdLat L (Fin 4 × n)))
    (hidx : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (z : Fin 4 × n → ℂ) :
    kernel4 (scalePair L c hc) (c * ω₀) (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))
      (alphaQ r (stdH (scalePair L c hc) (Fin 4 × n))) g z =
    kernel4 L ω₀ Λ (alphaQ r (stdH L (Fin 4 × n))) g (c⁻¹ • z) := by
  have hH' := gcm_stdH_scale L c hc (Fin 4 × n)
  have hα : alphaQ r (stdH (scalePair L c hc) (Fin 4 × n)) = fun x => alphaQ r (stdH L (Fin 4 × n)) (c⁻¹ • x) :=
    funext (gcm_alphaQ_scale hH' r)
  have hF0 : F0 (scalePair L c hc) (c * ω₀) (Fin 4 × n) = fun w => F0 L ω₀ (Fin 4 × n) (c⁻¹ • w) :=
    funext (periodF0_scale L c hc ω₀ (Fin 4 × n))
  simp only [kernel4]
  rw [gcm_stdLat_scale, gcm_imgLat_scale c hc, hα, hF0, map_smul]
  exact gcm_inter_scale hc hH' (Formalism.L2.Th1.H.stdHBasic L (Fin 4 × n)).2.1 hβ hF hidx _

end Forms

end Formalism.L2.DIV.C.X
