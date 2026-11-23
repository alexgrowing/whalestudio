import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNC

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem stepD (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0)
    (Λ Λ₃ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (hΛ₃fg : Λ₃.FG)
    (hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃) (hSD₃ : SD S Λ₃)
    (hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ orth S X, n x = x) ∧
      (n : S.V → S.V) '' Λ₃ = Λ := by
  classical
  obtain ⟨c, hcI, hc⟩ := htr
  have hXo := X_le_orth S X hXiso

  have hsurj : ∀ x ∈ Λ₃, ∃ y ∈ Λ, y - x ∈ X := fun x hx => by
    obtain ⟨w, hw, hxw⟩ := dual_sum S Λ hΛ hSD (orth S X) x
      (fun m hmΛ hmU => sd_int hSD₃ hx ((hM m hmU).2 hmΛ))
    refine ⟨w, hw, ?_⟩
    have : x - w ∈ X := mem_of_orth_orth S X fun u hu => by
      rw [hsw S u (x - w), orth_X S hxw hu, star_zero]
    have h2 := X.neg_mem this
    rwa [neg_sub] at h2
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S Λ₃ Λ hΛ₃fg X (orth S X) (fun x hx hxo => (hM x hxo).1 hx) hsurj
  obtain ⟨B₀, hB₀⟩ := ext_top S (W := S.V) Λ₃ hfull₃ δ
  have hscale : ∀ v : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • v) ∈ Λ₃, (d : E) • B₀ v = δ ⟨_, hm⟩ := fun v => by
    obtain ⟨d, hd, hdv⟩ := hfull₃ v
    rw [oSmul] at hdv
    exact ⟨d, hd, hdv, by rw [← map_smul, hB₀ _ hdv]⟩
  have hB₀X : ∀ v, B₀ v ∈ X := fun v => by
    obtain ⟨d, hd, hm, he⟩ := hscale v
    have h1 : (d : E) • B₀ v ∈ X := by rw [he]; exact hδX _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  have hB₀o : ∀ u ∈ orth S X, B₀ u = 0 := fun u hu => by
    obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ0 _ ((orth S X).smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)

  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  let σL : Fin S.rank → S.V →ₗ[E] E := fun k => S.hT (B₀ (b k)) + S.hT (b k) ∘ₗ B₀
  let B₁ : S.V →ₗ[E] S.V := ∑ k, ((-c) • σL k).smulRight (bs k)
  have hB₁app : ∀ v, B₁ v = ∑ k, (-c * (S.hT (B₀ (b k)) v + S.hT (b k) (B₀ v))) • bs k := fun v => by
    show (∑ k, ((-c) • σL k).smulRight (bs k)) v = _
    rw [LinearMap.sum_apply]
    rfl
  have hB₁ : ∀ v v', S.hT (B₁ v) v' = -(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v')) := fun v v' => by
    have key : S.hT (B₁ v) = -(star c) • (S.hT (B₀ v) + S.hT v ∘ₗ B₀) := by
      apply b.ext
      intro k'
      rw [hB₁app, map_sum, LinearMap.sum_apply]
      simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul,
        LinearMap.add_apply, LinearMap.comp_apply]
      rw [Finset.sum_eq_single k']
      · rw [hsw S (b k') (bs k'), hbs k' k', if_pos rfl, star_one, mul_one, star_mul, star_neg, star_add,
          ← hsw S (B₀ (b k')) v, ← hsw S (b k') (B₀ v)]
        ring
      · intro k _ hk
        rw [hsw S (b k') (bs k), hbs k' k, if_neg (Ne.symm hk), star_zero, mul_zero]
      · simp
    rw [key]
    rfl
  let B : S.V →ₗ[E] S.V := B₀ + B₁
  have hBapp : ∀ v, B v = B₀ v + B₁ v := fun v => rfl
  have hB₁X : ∀ v, B₁ v ∈ X := fun v => mem_of_orth_orth S X fun u hu => by
    rw [hB₁, hB₀o u hu, map_zero, orth_X S hu (hB₀X v)]
    ring
  have hB₁o : ∀ u ∈ orth S X, B₁ u = 0 := fun u hu => S.nondeg.1 _ fun v' => by
    rw [hB₁, hB₀o u hu, map_zero, LinearMap.zero_apply, orth_X' S hu (hB₀X v')]
    ring
  have hBX : ∀ v, B v ∈ X := fun v => by rw [hBapp]; exact X.add_mem (hB₀X v) (hB₁X v)
  have hBo : ∀ u ∈ orth S X, B u = 0 := fun u hu => by rw [hBapp, hB₀o u hu, hB₁o u hu, add_zero]
  have hBB : ∀ v, B (B v) = 0 := fun v => hBo _ (hXo (hBX v))
  have hBiso : ∀ v v', S.hT (v + B v) (v' + B v') = S.hT v v' := fun v v' => by
    have expand : S.hT (v + B v) (v' + B v') = S.hT v v' + S.hT (B v) v' + S.hT v (B v') + S.hT (B v) (B v') := by
      simp only [map_add, LinearMap.add_apply]; ring
    have f1 : S.hT (B v) v' = S.hT (B₀ v) v' + (-(star c) * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add, LinearMap.add_apply, hB₁]
    have f2 : S.hT v (B v') = S.hT v (B₀ v') + (-c * (S.hT (B₀ v) v' + S.hT v (B₀ v'))) := by
      rw [hBapp, map_add, hsw S (B₁ v') v, hB₁, star_mul, star_neg, star_add, ← hsw S (B₀ v') v,
        ← hsw S v' (B₀ v), star_star]
      ring
    rw [expand, hXiso _ (hBX v) _ (hBX v'), f1, f2]
    linear_combination (-(S.hT (B₀ v) v' + S.hT v (B₀ v'))) * hc
  let n : S.V ≃ₗ[E] S.V := LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B)
    (by ext v; simp [hBB]) (by ext v; simp [hBB])
  have hnapp : ∀ v, n v = v + B v := fun v => rfl
  have hniso : ∀ a b, S.hT (n a) (n b) = S.hT a b := fun a b => by rw [hnapp, hnapp, hBiso]
  have hnin : ∀ x ∈ Λ₃, n x ∈ Λ := fun x hx => by
    rw [hnapp, hBapp, ← add_assoc]
    refine Λ.add_mem (by rw [hB₀ x hx]; exact hδΛ ⟨x, hx⟩) ((hM _ (hXo (hB₁X x))).1 ?_)
    refine (hSD₃ _).2 fun y hy => ?_
    have hσ : IsIntegral ℤ (S.hT (B₀ x) y + S.hT x (B₀ y)) := by
      have h1 : IsIntegral ℤ (S.hT (x + B₀ x) (y + B₀ y)) := by
        rw [hB₀ x hx, hB₀ y hy]; exact sd_int hSD (hδΛ ⟨y, hy⟩) (hδΛ ⟨x, hx⟩)
      have h2 : IsIntegral ℤ (S.hT x y) := sd_int hSD₃ hy hx
      have e : S.hT (B₀ x) y + S.hT x (B₀ y) = S.hT (x + B₀ x) (y + B₀ y) - S.hT x y := by
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hXiso _ (hB₀X x) _ (hB₀X y)]
        ring
      rw [e]; exact h1.sub h2
    rw [hsw S (B₁ x) y, hB₁, star_mul, star_neg, star_star]
    exact (isInt_star hσ).mul hcI.neg
  refine ⟨n, hniso, fun x hx => by rw [hnapp, hBo x hx, add_zero], ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hnin y hy
  · intro hx
    refine ⟨n.symm x, (hSD₃ _).2 fun y hy => ?_, n.apply_symm_apply x⟩
    rw [← hniso y (n.symm x), n.apply_symm_apply]
    exact sd_int hSD hx (hnin y hy)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
