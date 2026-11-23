import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.FlagCent

variable {K : Type} [Field K] {n : ℕ}

theorem img_mul (g h : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img (g * h) W = img g (img h W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_one (W : Submodule K (Fin n → K)) : img (1 : GL (Fin n) K) W = W := by
  simp [img]

theorem mem_img_iff (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) (y : Fin n → K) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) K).val *ᵥ y ∈ W := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g⁻¹ : GL (Fin n) K).val * g.val = 1 := by rw [← Units.val_mul]; simp
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, this] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

theorem form_mulVec (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    ∑ i, σ ((A *ᵥ x) i) * y i = ∑ j, σ (x j) * ((A.map σ)ᵀ *ᵥ y) j := by
  simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, transpose_apply,
    map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem perp_img (σ : K →+* K) (g : GL (Fin n) K) (X : Submodule K (Fin n → K)) :
    perp σ (img g X) = img (thetaR σ n g) (perp σ X) := by
  ext y
  rw [mem_img_iff]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  constructor
  · intro h x hx
    rw [← form_mulVec]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, form_mulVec]
    exact h x hx

theorem le_perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    W ≤ perp σ (perp σ W) := fun z hz y hy => by
  have h2 := congrArg σ (hy z hz)
  simp only [map_sum, map_mul, hσ, map_zero] at h2
  simpa [mul_comm] using h2

theorem perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    perp σ (perp σ W) = W := by
  refine le_antisymm (fun z hz => ?_) (le_perp_perp σ hσ W)
  by_contra hn
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hn
  let a : Fin n → K := fun i => f fun j => if i = j then 1 else 0
  have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]; rfl
  have hy : (fun i => σ (a i)) ∈ perp σ W := fun x hx => by
    have h0 : f x = 0 := hf hx
    rw [hfa] at h0
    have := congrArg σ h0
    simpa only [map_sum, map_mul, map_zero] using this
  have h1 := hz _ hy
  simp only [hσ] at h1
  exact hf0 (by rw [hfa]; simpa [mul_comm] using h1)

theorem perpD_perpD (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    perpD σ d (perpD σ d W) = img (d * thetaR σ n d) W := by
  simp only [perpD]
  rw [perp_img, perp_perp σ hσ, img_mul]

theorem thetaR_thetaR (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) K) :
    thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  ext i j
  simp [hσ]

theorem commute_norm (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {d t : GL (Fin n) K}
    (ht : t ∈ twCent (thetaR σ n) d) :
    t * (d * thetaR σ n d) = (d * thetaR σ n d) * t := by
  have h1 : t⁻¹ * d * thetaR σ n t = d := ht
  have h2 : thetaR σ n d = (thetaR σ n t)⁻¹ * thetaR σ n d * t := by
    conv_lhs => rw [← h1]
    rw [map_mul, map_mul, map_inv, thetaR_thetaR σ hσ]
  have h3 : t * d = d * thetaR σ n t := by
    calc t * d = t * (t⁻¹ * d * thetaR σ n t) := by rw [h1]
      _ = d * thetaR σ n t := by group
  have h4 : thetaR σ n t * thetaR σ n d = thetaR σ n d * t := by
    calc thetaR σ n t * thetaR σ n d
        = thetaR σ n t * ((thetaR σ n t)⁻¹ * thetaR σ n d * t) := by rw [← h2]
      _ = thetaR σ n d * t := by group
  rw [← mul_assoc, h3, mul_assoc, h4, ← mul_assoc]

theorem map_le_of_commute [IsAlgClosed K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f t : Module.End K V) (hs : LinearMap.charpoly f |>.Separable)
    (hc : Commute f t) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) : W.map t ≤ W := by
  have hW' : W = ⨆ μ, W ⊓ f.maxGenEigenspace μ := by
    have h := Submodule.inf_iSup_genEigenspace (p := W) (f := f) hW ⊤
    rw [show ⨆ μ, f.genEigenspace μ ⊤ = ⊤ from Module.End.iSup_maxGenEigenspace_eq_top f,
      inf_top_eq] at h
    exact h
  rw [Submodule.map_le_iff_le_comap]
  conv_lhs => rw [hW']
  refine iSup_le fun μ x hx => ?_
  have hdim : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
  have htx : t x ∈ f.maxGenEigenspace μ := Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hx.2
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
  obtain ⟨a, ha⟩ := hv ⟨x, hx.2⟩
  obtain ⟨b, hb⟩ := hv ⟨t x, htx⟩
  have ha' : a • (v : V) = x := congrArg Subtype.val ha
  have hb' : b • (v : V) = t x := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using ha'.symm)
  change t x ∈ W
  rw [← hb', show b • (v : V) = (b / a) • x by rw [← ha', smul_smul, div_mul_cancel₀ _ ha0]]
  exact W.smul_mem _ hx.1

theorem img_eq_of_commute [IsAlgClosed K] (γ t : GL (Fin n) K) (hs : γ.val.charpoly.Separable)
    (hc : t * γ = γ * t) (W : Submodule K (Fin n → K)) (hW : img γ W = W) : img t W = W := by
  have key : ∀ s : GL (Fin n) K, s * γ = γ * s → img s W ≤ W := fun s hcs => by
    refine map_le_of_commute (Matrix.toLin' γ.val) (Matrix.toLin' s.val)
      (by rwa [Matrix.charpoly_toLin']) ?_ W fun x hx => ?_
    · change Matrix.toLin' γ.val * Matrix.toLin' s.val = Matrix.toLin' s.val * Matrix.toLin' γ.val
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Units.val_mul, ← Units.val_mul, hcs]
    · rw [← hW]; exact ⟨x, hx, rfl⟩
  refine le_antisymm (key t hc) ?_
  have hinv : t⁻¹ * γ = γ * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, hc]
  calc W = img t (img t⁻¹ W) := by rw [← img_mul, mul_inv_cancel, img_one]
    _ ≤ img t W := Submodule.map_mono (key t⁻¹ hinv)

theorem twCent_preserves_flag [IsAlgClosed K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (d : GL (Fin n) K) (hd : (d * thetaR σ n d).val.charpoly.Separable)
    (W₁ W₂ : Submodule K (Fin n → K)) (h₁ : perpD σ d W₁ = W₂) (h₂ : perpD σ d W₂ = W₁)
    {t : GL (Fin n) K} (ht : t ∈ twCent (thetaR σ n) d) : img t W₁ = W₁ ∧ img t W₂ = W₂ := by
  have hc := commute_norm σ hσ ht
  refine ⟨img_eq_of_commute _ t hd hc _ ?_, img_eq_of_commute _ t hd hc _ ?_⟩
  · rw [← perpD_perpD σ hσ, h₁, h₂]
  · rw [← perpD_perpD σ hσ, h₂, h₁]

end GlobalTheory.CompanionTheory.FlagCent
