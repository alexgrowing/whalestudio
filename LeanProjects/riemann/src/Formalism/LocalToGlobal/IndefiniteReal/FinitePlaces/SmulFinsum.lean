import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourExist

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

section FinsumAux

variable {α M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem finsum_add' {f g : α → M} (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i + g i) = ∑ᶠ i, f i + ∑ᶠ i, g i := by
  exact finsum_add_distrib hf hg

theorem map_finsum' (φ : M →ₗ[ℂ] M') {f : α → M} (hf : (Function.support f).Finite) :
    φ (∑ᶠ i, f i) = ∑ᶠ i, φ (f i) := by
  exact map_finsum φ hf

theorem smul_finsum' (c : ℂ) {f : α → M} (hf : (Function.support f).Finite) :
    c • ∑ᶠ i, f i = ∑ᶠ i, c • f i := by
  exact map_finsum (DistribMulAction.toAddMonoidHom M c) hf

end FinsumAux

section Main

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_add {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') :
    tfun ρ χ L X Y f₀ (Φ + Φ') = tfun ρ χ L X Y f₀ Φ + tfun ρ χ L X Y f₀ Φ' := by
  unfold tfun
  rw [← finsum_add' (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)
    (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h')]
  refine finsum_congr fun q => ?_
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy, term, coef_add hχl hχr hχ0 hLL hfinX hoY h h' _ hy, add_smul]
  · simp only [if_neg hy, add_zero]

include hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_smul {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : tfun ρ χ L X Y f₀ (c • Φ) = c • tfun ρ χ L X Y f₀ Φ := by
  unfold tfun
  rw [smul_finsum' c (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine finsum_congr fun q => ?_
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy, term, coef_smul hfinX, smul_smul]
  · simp only [if_neg hy, smul_zero]

include hX hXY hfX hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_trans {Φ : W → ℂ} (h : IsSB L X Φ) {x : W} (hx : x ∈ X) :
    tfun ρ χ L X Y f₀ (fun t => Φ (t + x)) = ρ x (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.addRight (QuotientAddGroup.mk x : QX L X)) (Equiv.refl (QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ x (if q.2.out ∈ Y then
    term ρ χ L X f₀ Φ (q.1 + (QuotientAddGroup.mk x : QX L X)).out q.2.out else 0)
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy]
    obtain ⟨l, hl, hout⟩ := QX_out (L := L) (X := X) (q.1.out + x)
    have hq : q.1 + (QuotientAddGroup.mk x : QX L X) = QuotientAddGroup.mk (q.1.out + x) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [hq, hout, term_add_left hχl hχ0 hfinX hX hXY hfX Φ hs _ hy hl]
    unfold term
    have hc : coef χ L X (fun t => Φ (t + x)) q.1.out q.2.out = coef χ L X Φ (q.1.out + x) q.2.out := by
      unfold coef
      congr 1
      funext t
      rw [add_right_comm]
    rw [hc, map_smul]
    by_cases ha : q.1.out + x ∈ X
    · have hρ : ρ x (ρ (-(q.1.out + x)) (ρ q.2.out f₀)) = ρ (-q.1.out) (ρ q.2.out f₀) := by
        rw [← Module.End.mul_apply, ← hX _ hx _ (X.neg_mem ha), show x + -(q.1.out + x) = -q.1.out by abel]
      rw [hρ]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · simp only [if_neg hy, map_zero]

include hY hXY hfY hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf in
open Classical in
theorem tfun_modul {Φ : W → ℂ} (h : IsSB L X Φ) {y₀ : W} (hy₀ : y₀ ∈ Y) :
    tfun ρ χ L X Y f₀ (fun t => χ t y₀ * Φ t) = ρ y₀ (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.refl (QX L X)) (Equiv.addRight (QuotientAddGroup.mk (-y₀) : QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ y₀ (if (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out ∈ Y then
    term ρ χ L X f₀ Φ q.1.out (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out else 0)
  obtain ⟨μ, hμ, hout⟩ := QY_out (L := L) (Y := Y) (q.2.out + -y₀)
  have hq : q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y) = QuotientAddGroup.mk (q.2.out + -y₀) := by
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  rw [hq, hout]
  have hμY := (AddSubgroup.mem_inf.1 hμ).2
  by_cases hy : q.2.out ∈ Y
  · have hy1 : q.2.out + -y₀ ∈ Y := Y.add_mem hy (Y.neg_mem hy₀)
    rw [if_pos hy, if_pos (Y.add_mem hy1 hμY), term_add_right hfinX hχr hLL hY hfY Φ _ hy1 hμ]
    unfold term
    have hc : coef χ L X (fun t => χ t y₀ * Φ t) q.1.out q.2.out =
        χ q.1.out y₀ * coef χ L X Φ q.1.out (q.2.out + -y₀) := by
      unfold coef
      rw [← integ_cmul' hfinX]
      congr 1
      funext t
      have e1 : χ t q.2.out = χ t (q.2.out + -y₀) * χ t y₀ := by rw [← hχr, neg_add_cancel_right]
      show χ (q.1.out + t) y₀ * Φ (q.1.out + t) * (χ t q.2.out)⁻¹ = _
      rw [hχl, e1, mul_inv]
      linear_combination (χ q.1.out y₀ * Φ (q.1.out + t) * (χ t (q.2.out + -y₀))⁻¹) *
        mul_inv_cancel₀ (hχ0 t y₀)
    rw [hc]
    by_cases ha : q.1.out ∈ X
    · have hc2 := congrArg (fun T : Module.End ℂ V => T (ρ (q.2.out + -y₀) f₀)) (hXY _ (X.neg_mem ha) y₀ hy₀)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at hc2
      have hρy : ρ y₀ (ρ (q.2.out + -y₀) f₀) = ρ q.2.out f₀ := by
        rw [← Module.End.mul_apply, ← hY _ hy₀ _ hy1, show y₀ + (q.2.out + -y₀) = q.2.out by abel]
      have hswap : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) = χ q.1.out y₀ • ρ (-q.1.out) (ρ q.2.out f₀) := by
        have h3 : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) =
            (χ (-q.1.out) y₀)⁻¹ • ρ (-q.1.out) (ρ y₀ (ρ (q.2.out + -y₀) f₀)) := by
          rw [hc2, smul_smul, inv_mul_cancel₀ (hχ0 _ _), one_smul]
        rw [h3, hρy, chi_neg_left hχl hχ0, inv_inv]
      rw [map_smul, hswap, smul_smul, mul_comm]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · have hy' : q.2.out + -y₀ + μ ∉ Y := fun h' => hy (by
      have := Y.add_mem (Y.sub_mem h' hμY) hy₀
      simpa using this)
    rw [if_neg hy, if_neg hy', map_zero]

include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoY hfinX in
open Classical in
theorem tfun_vac : tfun ρ χ L X Y f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  have hsupp := (isSB_ind (L := L) (X := X)).1
  have hval : ∀ a ∈ L ⊓ X, ∀ y ∈ L ⊓ Y,
      term ρ χ L X f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) a y = f₀ := by
    intro a ha y hy
    have e1 := term_add_left hχl hχ0 hfinX hX hXY hfX _ hsupp 0 (AddSubgroup.mem_inf.1 hy).2 ha
    have e2 := term_add_right hfinX hχr hLL hY hfY (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0
      Y.zero_mem hy
    rw [zero_add] at e1 e2
    rw [e1, e2]
    have hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0 0 = 1 := by
      have hpt : ∀ t ∈ L ⊓ X, (if 0 + t ∈ L ∧ 0 + t ∈ X then (1 : ℂ) else 0) * (χ t 0)⁻¹ = 1 := by
        intro t ht
        rw [zero_add, if_pos (AddSubgroup.mem_inf.1 ht), chi_zero_right hχr hχ0, inv_one, mul_one]
      unfold coef
      exact (integ_congr hfinX (g' := fun _ => (1 : ℂ)) hpt).trans (integ_one hfinX)
    rw [term, hc, one_smul, neg_zero, hfX 0 (L ⊓ X).zero_mem, hfX 0 (L ⊓ X).zero_mem]
  unfold tfun
  have h0X : (0 : QX L X).out ∈ L ⊓ X := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  have h0Y : (0 : QY L Y).out ∈ L ⊓ Y := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  rw [finsum_eq_single _ ((0 : QX L X), (0 : QY L Y))]
  · show (if (0 : QY L Y).out ∈ Y then _ else _) = f₀
    rw [if_pos (AddSubgroup.mem_inf.1 h0Y).2]
    exact hval _ h0X _ h0Y
  · rintro ⟨q1, q2⟩ hq
    by_cases hy : q2.out ∈ Y
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_pos hy, term]
      suffices hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) q1.out q2.out = 0 by
        rw [hc, zero_smul]
      by_cases h1 : q1 = 0
      · have hq2 : q2 ≠ 0 := fun h2 => hq (by rw [h1, h2])
        have h1X : q1.out ∈ L ⊓ X :=
          (QuotientAddGroup.eq_zero_iff _).1 ((QuotientAddGroup.out_eq' q1).trans h1)
        have hyL : q2.out ∉ L := fun hL => hq2 ((QuotientAddGroup.out_eq' q2).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_inf.2 ⟨hL, hy⟩)))
        have hne : ¬ ∀ x ∈ L ⊓ X, χ x q2.out = 1 := fun hall => hyL (hdY _ hy hall)
        push_neg at hne
        obtain ⟨u, hu, hχu⟩ := hne
        obtain ⟨m, hm, hmy⟩ := hoY _ hy
        unfold coef
        rw [integ_congr hfinX (g' := fun t => (χ t q2.out)⁻¹) fun t ht => by
          show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = _
          rw [if_pos (AddSubgroup.mem_inf.1 ((L ⊓ X).add_mem h1X ht)), one_mul]]
        refine integ_twist hfinX hm (fun t _ u' hu' => ?_) hu (ζ := (χ u q2.out)⁻¹) (by rwa [Ne, inv_eq_one]) ?_
        · rw [hχl, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
            hLL _ hu' _ (AddSubgroup.mem_inf.2 ⟨hmy, Y.nsmul_mem hy m⟩), mul_one]
        · intro t _
          rw [hχl, mul_inv, mul_comm]
      · have h1X : q1.out ∉ L ⊓ X := fun hm => h1 ((QuotientAddGroup.out_eq' q1).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 hm))
        unfold coef
        refine integ_zero_of hfinX fun t ht => ?_
        show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = 0
        rw [if_neg, zero_mul]
        intro hh
        exact h1X (by simpa using (L ⊓ X).sub_mem (AddSubgroup.mem_inf.2 hh) ht)
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_neg hy]

include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoX hoY hfinX hfinY htf in
open Classical in

theorem exists_model : ∃ T : (W → ℂ) →ₗ[ℂ] V,
    (∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ) ∧
    (∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧
    (∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ)) ∧
    T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  let S : Submodule ℂ (W → ℂ) :=
    { carrier := {Φ | IsSB L X Φ}
      add_mem' := fun h h' => IsSB.add h h'
      zero_mem' := isSB_zero
      smul_mem' := fun c _ h => IsSB.smul h c }
  let tL : S →ₗ[ℂ] V :=
    { toFun := fun Φ => tfun ρ χ L X Y f₀ Φ.1
      map_add' := fun Φ Φ' => tfun_add (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 Φ'.2
      map_smul' := fun c Φ => tfun_smul (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 c }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend tL
  have hTe : ∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ := fun Φ h => LinearMap.congr_fun hT ⟨Φ, h⟩
  refine ⟨T, hTe, fun Φ h x hx => ?_, fun Φ h y hy => ?_, ?_⟩
  · rw [hTe _ (h.trans hoX hx), hTe _ h]
    exact tfun_trans (hX := hX) (hXY := hXY) (hfX := hfX) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hx
  · rw [hTe _ (h.modul hχl hχr hχ0 hLL hoY hy), hTe _ h]
    exact tfun_modul (hY := hY) (hXY := hXY) (hfY := hfY) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hy
  · rw [hTe _ isSB_ind]
    exact tfun_vac (hX := hX) (hY := hY) (hXY := hXY) (hfX := hfX) (hfY := hfY) (hχl := hχl) (hχr := hχr)
      (hχ0 := hχ0) (hLL := hLL) (hdY := hdY) (hoY := hoY) (hfinX := hfinX)

end Main

end Formalism.IndefR.Fin.Four

end
