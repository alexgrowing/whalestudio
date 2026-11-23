import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact finsum_prod_mul_of_finite u v hu hv
    · rw [finsum_of_infinite_support hv, mul_zero]
      by_cases h0 : ∀ a, u a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        apply finsum_of_infinite_support
        intro hfin
        apply hv
        refine (hfin.image Prod.snd).subset ?_
        intro b hb
        exact ⟨(a, b), by simp only [Function.mem_support] at hb ⊢; exact mul_ne_zero ha hb, rfl⟩
  · rw [finsum_of_infinite_support hu, zero_mul]
    by_cases h0 : ∀ b, v b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      apply finsum_of_infinite_support
      intro hfin
      apply hu
      refine (hfin.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, b), by simp only [Function.mem_support] at ha ⊢; exact mul_ne_zero ha hb, rfl⟩

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem map_conj_mul (K : Subgroup G) (t x : G) :
    K.map (MulAut.conj (t * x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  have h := map_conj_mul_three_subgroup_of_mem K K.one_mem t x
  rwa [mul_one] at h

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem conj_isOpen {K : Subgroup G} (hKo : IsOpen (K : Set G)) (g : G) :
    IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ((MulAut.conj g).toMonoidHom : G → G) = (fun y => y * g⁻¹) ∘ (fun y => g * y) := by
    funext y; simp [MulAut.conj_apply]
  rw [e]
  exact ((isOpenMap_mul_right g⁻¹).comp (isOpenMap_mul_left g)) _ hKo

theorem conj_isCompact {K : Subgroup G} (hKc : IsCompact (K : Set G)) (g : G) :
    IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact hKc.image (by show Continuous fun y : G => g * y * g⁻¹; fun_prop)

theorem vol_conj (T K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    {t : G} (ht : t ∈ T) (hvol : vol (T ⊓ K) ((T ⊓ K).map (MulAut.conj t).toMonoidHom) = 1) (x : G) :
    vol (T ⊓ K) ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom) =
      vol (T ⊓ K) (T ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  have hc := GlobalTheory.FunObj.idxRatio_cocycle T (conj_isOpen hKo (t * x)) (conj_isCompact hKc (t * x))
    (conj_isOpen hKo t) (conj_isCompact hKc t) hKo hKc
  rw [map_conj_mul, inf_map_conj T _ ht, inf_map_conj T _ ht, GlobalTheory.FunObj.idxRatio_map (MulAut.conj t).injective,
    show GlobalTheory.FunObj.idxRatio ((T ⊓ K).map (MulAut.conj t).toMonoidHom) (T ⊓ K) = 1 from hvol, mul_one] at hc
  rw [vol_eq_idxRatio, vol_eq_idxRatio]
  exact hc.symm

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem oTerm_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    (hvol : ∀ t ∈ twCent θ δ, vol (twCent θ δ ⊓ K) ((twCent θ δ ⊓ K).map (MulAut.conj t).toMonoidHom) = 1)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    oTerm θ K (twCent θ δ ⊓ K) δ f (t * x * k) = oTerm θ K (twCent θ δ ⊓ K) δ f x := by
  unfold oTerm
  rw [f_inv θ K δ f hf ht hk x, map_conj_mul_three_subgroup_of_mem K hk, inf_map_conj _ _ ht,
    vol_conj _ K hKo hKc ht (hvol t ht) x]

theorem oTerm_prod {G' : Type} [Group G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G')
    (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ) (x : G) (x' : G') :
    oTerm (θ.prodMap θ') (K.prod K') ((twCent θ δ).prod (twCent θ' δ') ⊓ K.prod K') (δ, δ')
        (fun y => f y.1 * f' y.2) (x, x') =
      oTerm θ K (twCent θ δ ⊓ K) δ f x * oTerm θ' K' (twCent θ' δ' ⊓ K') δ' f' x' := by
  unfold oTerm
  rw [twCent_prod, map_conj_prod, prod_inf_prod, prod_inf_prod, vol_prod]
  push_cast
  rw [mul_inv, mul_mul_mul_comm]
  rfl

end Term

theorem orbK_prod : ∀ {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [T2Space G₁] [T2Space G₂] (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ₁ : G₁) (δ₂ : G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), Continuous θ₁ → Continuous θ₂ → IsCompact (K₁ : Set G₁) → IsOpen (K₁ : Set G₁) → IsCompact (K₂ : Set G₂) → IsOpen (K₂ : Set G₂) → (∀ k ∈ K₁, ∀ y, f₁ (k⁻¹ * y * θ₁ k) = f₁ y) → (∀ k ∈ K₂, ∀ y, f₂ (k⁻¹ * y * θ₂ k) = f₂ y) → (∀ t ∈ GlobalTheory.BCT.twCent θ₁ δ₁, vol (GlobalTheory.BCT.twCent θ₁ δ₁ ⊓ K₁) ((GlobalTheory.BCT.twCent θ₁ δ₁ ⊓ K₁).map (MulAut.conj t).toMonoidHom) = 1) → (∀ t ∈ GlobalTheory.BCT.twCent θ₂ δ₂, vol (GlobalTheory.BCT.twCent θ₂ δ₂ ⊓ K₂) ((GlobalTheory.BCT.twCent θ₂ δ₂ ⊓ K₂).map (MulAut.conj t).toMonoidHom) = 1) → orbK (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (fun x => f₁ x.1 * f₂ x.2) = orbK θ₁ K₁ δ₁ f₁ * orbK θ₂ K₂ δ₂ f₂ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ θ₁ θ₂ K₁ K₂ δ₁ δ₂ f₁ f₂ _ _ hK₁c hK₁o hK₂c hK₂o hf₁ hf₂ hv₁ hv₂
  unfold orbK
  rw [orbC_eq, orbC_eq, orbC_eq, twCent_prod]
  have hz : ∀ z, oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2)
      (Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z)) =
      oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out z.1) *
        oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out z.2) := by
    intro z
    obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂)) (K₁.prod K₂)
      (Quotient.out z.1, Quotient.out z.2)
    rw [Subgroup.mem_prod] at ha hb
    have e2 : Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z) =
        (a.1 * Quotient.out z.1 * b.1, a.2 * Quotient.out z.2 * b.2) := e
    rw [e2, oTerm_prod, oTerm_inv θ₁ K₁ δ₁ f₁ hK₁c hK₁o hf₁ hv₁ ha.1 hb.1,
      oTerm_inv θ₂ K₂ δ₂ f₂ hK₂c hK₂o hf₂ hv₂ ha.2 hb.2]
  have hq := finsum_comp_equiv (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂))
    (f := fun q => oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2) (Quotient.out q))
  rw [← hq, finsum_congr hz]
  exact finsum_prod_mul (fun q => oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out q))
    (fun q => oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out q))

end GlobalTheory.LKCount.OrbKProd
