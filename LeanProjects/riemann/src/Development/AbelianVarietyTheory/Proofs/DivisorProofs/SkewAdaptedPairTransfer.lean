import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionPairFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSchwartzAdelicStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWChar

theorem exists_dbl_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {β : Type} [Fintype β] [DecidableEq β]
    (J : Matrix β β A) (g : UG c J) :
    ∃ gd : UG c (dbl J), ((gd : GL (β ⊕ β) A) : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks ((g : GL β A) : Matrix β β A) 0 0 1 := by
  let G : Matrix β β A := ((g : GL β A) : Matrix β β A)
  let Gi : Matrix β β A := (((g⁻¹ : UG c J) : GL β A) : Matrix β β A)
  have h1 : G * Gi = 1 := by
    show ((g : GL β A) : Matrix β β A) * (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : Gi * G = 1 := by
    show (((g : GL β A)⁻¹ : GL β A) : Matrix β β A) * ((g : GL β A) : Matrix β β A) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let u : GL (β ⊕ β) A := ⟨Matrix.fromBlocks G 0 0 1, Matrix.fromBlocks Gi 0 0 1, by
    rw [Matrix.fromBlocks_multiply]; simp [h1, Matrix.fromBlocks_one], by
    rw [Matrix.fromBlocks_multiply]; simp [h2, Matrix.fromBlocks_one]⟩
  have hg : Gᵀ * J * G.map c = J := g.2
  refine ⟨⟨u, ?_⟩, rfl⟩
  show (Matrix.fromBlocks G 0 0 1)ᵀ * dbl J * (Matrix.fromBlocks G 0 0 1).map c = dbl J
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hg, Matrix.map_one _ (map_zero c) (map_one c)]

theorem boxFun_ne_zero {R κ κ' : Type} {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) :
    boxFun φ₁ φ₂ ≠ 0 := by
  obtain ⟨x₁, hx₁⟩ := Function.ne_iff.mp h₁
  obtain ⟨x₂, hx₂⟩ := Function.ne_iff.mp h₂
  intro h
  have := congrFun h (Sum.elim x₁ x₂)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at this
  exact mul_ne_zero hx₁ hx₂ this

theorem eq_one_of_boxFun {R κ κ' : Type} {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) {a : ℂ}
    (h : boxFun (a • φ₁) φ₂ = boxFun φ₁ φ₂) : a = 1 := by
  obtain ⟨x₁, hx₁⟩ := Function.ne_iff.mp h₁
  obtain ⟨x₂, hx₂⟩ := Function.ne_iff.mp h₂
  have := congrFun h (Sum.elim x₁ x₂)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  have hne : φ₁ x₁ * φ₂ x₂ ≠ 0 := mul_ne_zero hx₁ hx₂
  have : (a - 1) * (φ₁ x₁ * φ₂ x₂) = 0 := by linear_combination this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)

theorem char_eq_one : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ c : UA σ W₁.J →* ℂˣ, Continuous c →
      (∀ h₁ m, IsLevi H' 1 h₁ m → ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = (c h₁ : ℂ) • om₁ (1, h₁) (e Φ)) → c = 1 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he c _hc hce
  obtain ⟨hUS, dd, omd, hDC, hSpl, hbox⟩ := hP.weil.1
  obtain ⟨-, dd₁, omd₁, hDC₁, hSpl₁, hbox₁⟩ := hP₁.weil.1
  obtain ⟨Ed, e₂, hEa, hEb, hEc, hEd, hEe, he₂s, Φ₂, hΦ₂, he₂Φ⟩ :=
    GlobalTheory.T.adapted_plane_restriction_pair_third hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he dd dd₁ hDC hDC₁
  obtain ⟨Φ₁, hΦ₁, heΦ⟩ := GlobalTheory.T.eigen_intertwiner_restriction F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  have hEne : ∃ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), Ed Φ ≠ 0 :=
    ⟨boxFun Φ₁ Φ₂, GlobalTheory.T.tensor_product_schwartz_adelic F _ _ Φ₁ Φ₂ hΦ₁ hΦ₂, by rw [hEe Φ₁ hΦ₁ Φ₂ hΦ₂]; exact boxFun_ne_zero heΦ he₂Φ⟩
  have key := GlobalTheory.T.restriction_omd_intertwines_of_fixes_incV hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ dd omd hDC hSpl
    dd₁ omd₁ hDC₁ hSpl₁ Ed hEa hEb hEc hEd hEne
  ext h₁
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.exists_unique_levi_element F E σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ (GlobalTheory.AdelicU.cm_conj_conj hP.base.cm) hP.skew hP₁.skew hH h₁
  obtain ⟨md, hmd⟩ := exists_dbl_left (cA σ) (incM F W.J) m
  obtain ⟨hd, hhd⟩ := exists_dbl_left (cA σ) (incM F W₁.J) h₁
  obtain ⟨hmx, hmy, hmι⟩ := hm
  have hmx' : mat m *ᵥ incV F H'.x = incV F H'.x := by rw [hmx, Units.val_one, one_smul]
  have hmy' : mat m *ᵥ incV F H'.y = incV F H'.y := by rw [hmy, inv_one, Units.val_one, map_one, one_smul]
  have hmd' : (md.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat m) 0 0 1 := hmd
  have hhd' : (hd.1.1 : Matrix (Fin d₁ ⊕ Fin d₁) (Fin d₁ ⊕ Fin d₁) (AE F E)) = Matrix.fromBlocks (mat h₁) 0 0 1 := hhd
  have k := key hd md
    (by
      rw [hmd', hhd', Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hmι])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp [hmx'])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp)
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp [hmy'])
    (by rw [hmd', Matrix.fromBlocks_mulVec]; simp)
    (boxFun Φ₁ Φ₂) (GlobalTheory.T.tensor_product_schwartz_adelic F _ _ Φ₁ Φ₂ hΦ₁ hΦ₂)
  have hpres : om (1, m) Φ₁ ∈ schA F (Fin n × Fin d) := by
    have := hUS.toIsSplitting.pres m Φ₁ hΦ₁
    exact this
  rw [hbox m md hmd Φ₁ hΦ₁ Φ₂ hΦ₂] at k
  rw [show (om.comp (MonoidHom.inr _ _)) m Φ₁ = om (1, m) Φ₁ from rfl, hEe _ hpres Φ₂ hΦ₂, hEe Φ₁ hΦ₁ Φ₂ hΦ₂,
    hbox₁ h₁ hd hhd (e Φ₁) (he.maps Φ₁ hΦ₁) (e₂ Φ₂) (he₂s Φ₂ hΦ₂), hce h₁ m ⟨hmx, hmy, hmι⟩ Φ₁ hΦ₁] at k
  have hA : om₁ (1, h₁) (e Φ₁) ≠ 0 := by
    intro h0
    apply heΦ
    have : om₁ (1, h₁⁻¹) (om₁ (1, h₁) (e Φ₁)) = e Φ₁ := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    rw [← this, h0, map_zero]
  rw [MonoidHom.one_apply, Units.val_one]
  exact eq_one_of_boxFun hA he₂Φ k

end GlobalTheory.MixWChar
