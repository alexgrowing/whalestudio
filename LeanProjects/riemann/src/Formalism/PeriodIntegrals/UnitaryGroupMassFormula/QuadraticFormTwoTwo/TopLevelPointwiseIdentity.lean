import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.GANormSqStar

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SlopeTestRemainingChoices

variable {k r : ℕ}

theorem ffa_hpk_esI_row (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ffa_herm_esI (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (esI k r a)) = x (eI k r a) := by
  have hs : star (bvec (esI k r a)) = bvec (esI k r a) := by
    funext j
    by_cases h : j = esI k r a <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, mulVec, dotProduct, Pi.single_apply, ffa_hpk_esI_row]

theorem ffa_herm_UH {n : Mx k r} (hn : n ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (n *ᵥ x) (n *ᵥ y) = herm (Hpk k r) x y := by
  have hn' : nᴴ * Hpk k r * n = Hpk k r := hn
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hn']

private theorem hpk_eI_apply (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem herm_bvec_eI_quadratic_form_two_two (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (eI k r a)) = x (esI k r a) := by
  have hs : star (bvec (eI k r a)) = bvec (eI k r a) := by
    funext j
    by_cases h : j = eI k r a <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, mulVec, dotProduct, Pi.single_apply, hpk_eI_apply]

theorem ffa_nlev_fix {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : n *ᵥ w = w := by
  rcases hn with ⟨⟨hU, -, h3⟩, -, hG⟩
  have hlast : ∀ a : Fin r, a.val < (Fin.last r).val := fun a => by simp
  funext i
  have hi := i.isLt
  by_cases hlo : i.val < r
  · have hi' : i = eI k r ⟨i.val, hlo⟩ := Fin.ext (by simp [eI])
    rw [hi', ← ffa_herm_esI (n *ᵥ w), ← ffa_herm_esI w]
    conv_lhs => rw [← (hG ⟨i.val, hlo⟩ (hlast _)).2]
    exact ffa_herm_UH hU w _
  by_cases hhi : r + k < i.val
  · have hb : 2 * r + k - i.val < r := by omega
    have hi' : i = esI k r ⟨2 * r + k - i.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    rw [hi', ← herm_bvec_eI_quadratic_form_two_two (n *ᵥ w), ← herm_bvec_eI_quadratic_form_two_two w]
    conv_lhs => rw [← (hG ⟨2 * r + k - i.val, hb⟩ (hlast _)).1]
    exact ffa_herm_UH hU w _
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [h3 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [h3 i j hj.1 hj.2 (by omega), if_neg (Ne.symm hji), zero_mul]
    · rw [hw j (by omega), mul_zero]
  · simp

theorem ffa_fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  unfold fvec
  rw [dif_neg (by simp)]

theorem ffa_zeta_left {z z' : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (hz : h *ᵥ z = z)
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (h * g) = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, ← ffa_herm_UH hh (g *ᵥ z') z, hz]

theorem ffa_zeta_right {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (g * h') = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, hz']

theorem ffa_GG_left {z z' : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (hz : h *ᵥ z = z)
    (g : Mx k r) : GGl k r z z' (h * g) = GGl k r z z' g := by
  unfold GGl
  rw [ffa_zeta_left hh hz]

theorem ffa_GG_right {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : GGl k r z z' (g * h') = GGl k r z z' g := by
  unfold GGl
  rw [ffa_zeta_right hz']

def ffaZetaLin (z z' : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℝ] ℂ where
  toFun x := herm (Hpk k r) (x *ᵥ z') z
  map_add' x y := by simp [herm, add_mulVec, mulVec_add, dotProduct_add]
  map_smul' c x := by
    simp only [herm, RingHom.id_apply]
    rw [smul_mulVec, mulVec_smul, dotProduct_smul]

theorem ffa_GG_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ∞ (fun x : Mx k r => (GGl k r z z' x : ℂ)) := by
  have hζ : ContDiff ℝ ∞ (fun x : Mx k r => zetaL k r z z' (Fin.last r) x) := by
    have h1 := (LinearMap.toContinuousLinearMap (ffaZetaLin z z')).contDiff (n := ∞)
    convert h1 using 1
    funext x
    simp only [zetaL, ffa_fvec_last]
    rfl
  have hc : ContDiff ℝ ∞ (fun x : Mx k r => Complex.conjCLE (zetaL k r z z' (Fin.last r) x)) :=
    Complex.conjCLE.contDiff.comp hζ
  have he : (fun x : Mx k r => (GGl k r z z' x : ℂ)) = fun x =>
      zetaL k r z z' (Fin.last r) x * Complex.conjCLE (zetaL k r z z' (Fin.last r) x) -
        (Tz k r z : ℂ) * (Tz k r z' : ℂ) := by
    funext x
    simp [GGl, Complex.mul_conj]
  rw [he]
  exact (hζ.mul hc).sub contDiff_const

end SlopeTestRemainingChoices

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem ff_zero : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq]
  refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const,
    fun _ _ _ => rfl⟩, fun _ _ _ _ => (smul_zero _).symm, fun _ _ _ _ => (smul_zero _).symm,
    fun _ _ _ _ _ _ => ?_⟩
  simp

theorem ff_add {J₁ J₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : J₁ ∈ FFl k r z z' π π' (Fin.last r) D)
    (h₂ : J₂ ∈ FFl k r z z' π π' (Fin.last r) D) : (fun x => J₁ x + J₂ x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  obtain ⟨s₁, l₁, r₁, e₁⟩ := h₁
  obtain ⟨s₂, l₂, r₂, e₂⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, o₁, m₁, c₁, q₁⟩ := s₁ g₀ hg₀
    obtain ⟨U₂, F₂, o₂, m₂, c₂, q₂⟩ := s₂ g₀ hg₀
    refine ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
      (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
    rw [q₁ g hg.1 hgl, q₂ g hg.2 hgl]
  · intro g hg n hn
    rw [l₁ g hg n hn, l₂ g hg n hn, smul_add]
  · intro g hg n hn
    rw [r₁ g hg n hn, r₂ g hg n hn, smul_add]
  · intro g hg h hh h' hh'
    rw [e₁ g hg h hh h' hh', e₂ g hg h hh h' hh', ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]

theorem ff_smul {J : Mx k r → (Wq →L[ℂ] Wp)} (h : J ∈ FFl k r z z' π π' (Fin.last r) D) (c : ℂ) :
    (fun x => c • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h ⊢
  obtain ⟨s, l, rr, e⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun g hg hgl => by rw [q g hg hgl]⟩
  · intro g hg n hn
    rw [l g hg n hn, smul_comm]
  · intro g hg n hn
    rw [rr g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem ff_GGinv (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hGG : ∀ g ∈ D, GGl k r z z' g ≠ 0) {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) :
    (fun x => ((GGl k r z z' x : ℂ))⁻¹ • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  have hcd := ffa_GG_contDiff (k := k) (r := r) z z'
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at hJ ⊢
  obtain ⟨s, l, rr, e⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    have ho : IsOpen {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0} :=
      isOpen_ne_fun hcd.continuous continuous_const
    refine ⟨U ∩ {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0}, fun x => ((GGl k r z z' x : ℂ))⁻¹ • F x,
      o.inter ho, ⟨m, Complex.ofReal_ne_zero.mpr (hGG g₀ hg₀.2)⟩, ?_, fun g hg hgl => by rw [q g hg.1 hgl]⟩
    exact ((hcd.contDiffOn.mono Set.inter_subset_left).inv (fun x hx => hx.2)).smul
      (cd.mono Set.inter_subset_left)
  · intro g hg n hn
    have hnz : n *ᵥ z = z := ffa_nlev_fix hn hz
    rw [l g hg n hn, ffa_GG_left hn.1.1 hnz, smul_comm]
  · intro g hg n hn
    have hnz : n *ᵥ z' = z' := ffa_nlev_fix hn hz'
    rw [rr g hg n hn, ffa_GG_right hnz, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ffa_GG_right hh'.2.2, ffa_GG_left hh.1 hh.2.2,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem top_level_pointwise_identity (hCap : CapelliIdentityEntry) (hRTA : RightTypeAction) [FiniteDimensional ℂ Wq]
    (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hπ'r : IsCRepOn (UWset k r z') π') (hπ'c : ContinuousOn π' (UWset k r z'))
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hGG : GGl k r z z' g ≠ 0)
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs) (Y : ℂ) (v : Wq) :
    tL k r z z' (Fin.last r) Y 1 1 F g v = (GGl k r z z' g : ℂ) • F g (capRep k r π' Bs (Y + ((k : ℂ) - 2) / 2) v) := by
  have hBs' : IsFrameOf k r [z'] Bs :=
    ⟨hBs.1, hBs.2.1, fun a w hw => hBs.2.2 a w (List.mem_cons_of_mem _ hw)⟩
  rw [hCap _ k r z z' D F hz hz' hD.1 hF.1 g hg hGG Bs hBs Y, _root_.smul_apply,
    hRTA Wp Wq k r (k - 1) z z' π π' D hz hz' hD hπ'r hπ'c F hF g hg Bs hBs']

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
