import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatDarboux

theorem exists_rat_matrix {F R V W ι : Type} [Field F] [CommRing R] [Nontrivial R] [Algebra F R] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    (j : V →+ W) (hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x) (hinj : Function.Injective j)
    (hc : Module.finrank F V = Fintype.card ι) (e₀ e₂ : W ≃ₗ[R] (ι → R))
    (h₀ : ∀ x, ∃ u : ι → F, e₀ (j x) = fun i => algebraMap F R (u i))
    (h₂ : ∀ x, ∃ u : ι → F, e₂ (j x) = fun i => algebraMap F R (u i)) :
    ∃ g : Matrix ι ι F, ∀ w, e₂ w = g.map (algebraMap F R) *ᵥ e₀ w := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective
  have hvec : ∀ a b : ι → F, (fun i => algebraMap F R (a i)) = (fun i => algebraMap F R (b i)) → a = b := by
    intro a b h
    funext i
    exact hφ (congrFun h i)

  have lin : ∀ (e : W ≃ₗ[R] (ι → R)) (u : V → ι → F), (∀ x, e (j x) = fun i => algebraMap F R (u x i)) →
      ∃ U : V →ₗ[F] (ι → F), ∀ x, U x = u x := by
    intro e u hu
    refine ⟨{ toFun := u, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      apply hvec
      rw [← hu, map_add, map_add, hu, hu]
      funext i
      simp
    · intro c x
      apply hvec
      rw [← hu, hj, map_smul, hu]
      funext i
      simp
  choose u₀ hu₀ using h₀
  choose u₂ hu₂ using h₂
  obtain ⟨U₀, hU₀⟩ := lin e₀ u₀ hu₀
  obtain ⟨U₂, hU₂⟩ := lin e₂ u₂ hu₂

  have inj : Function.Injective U₀ := by
    intro x y hxy
    apply hinj
    apply e₀.injective
    rw [hu₀, hu₀, ← hU₀, ← hU₀, hxy]
  have surj : Function.Surjective U₀ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [hc, Module.finrank_fintype_fun_eq_card]
  let E₀ : V ≃ₗ[F] (ι → F) := LinearEquiv.ofBijective U₀ ⟨inj, surj⟩
  refine ⟨LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap), ?_⟩
  set g := LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap) with hg

  have onForm : ∀ x, e₂ (j x) = g.map (algebraMap F R) *ᵥ e₀ (j x) := by
    intro x
    have h1 : g *ᵥ U₀ x = U₂ x := by
      rw [hg, LinearMap.toMatrix'_mulVec]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      congr 1
      exact E₀.symm_apply_apply x
    funext i
    rw [hu₂, hu₀, ← hU₂, ← h1, ← hU₀]
    exact RingHom.map_mulVec (algebraMap F R) g (U₀ x) i

  have onBasis : ∀ i, e₂ (e₀.symm (Pi.single i 1)) = g.map (algebraMap F R) *ᵥ Pi.single i 1 := by
    intro i
    obtain ⟨x, hx⟩ := surj (Pi.single i 1)
    have hs : e₀ (j x) = Pi.single i 1 := by
      rw [hu₀, ← hU₀, hx]
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [← hs, LinearEquiv.symm_apply_apply, onForm]
  have hL : (e₂.toLinearMap ∘ₗ e₀.symm.toLinearMap) = Matrix.mulVecLin (g.map (algebraMap F R)) := by
    apply (Pi.basisFun R ι).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Matrix.mulVecLin_apply]
    exact onBasis i
  intro w
  have := LinearMap.congr_fun hL (e₀ w)
  simpa using this

theorem std_form {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (a b : κ ⊕ κ → R) :
    a ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) *ᵥ b) =
      (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (b ∘ Sum.inl) ⬝ᵥ (a ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  conv_lhs => rw [← Sum.elim_comp_inl_inr a]
  rw [sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
    dotProduct_comm (a ∘ Sum.inr)]
  simp only [neg_dotProduct, sub_eq_add_neg]

theorem exists_rat_symplectic_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Nontrivial R] [Algebra F R] {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    {Bf : Matrix α β (R ⊗[F] E) → Matrix α β (R ⊗[F] E) → R} (d₀ d₂ : Darboux Bf κ)
    (inc : Matrix α β E → Matrix α β (R ⊗[F] E)) (hinc : ∀ x a b, inc x a b = (1 : R) ⊗ₜ[F] x a b)
    (hc : Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E)
    (h₀ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₀.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i)))
    (h₂ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₂.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) :
    ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective

  let j : Matrix α β E →+ Matrix α β (R ⊗[F] E) :=
    { toFun := inc
      map_zero' := by
        ext a b
        simp [hinc]
      map_add' := by
        intro x y
        ext a b
        simp [hinc, TensorProduct.tmul_add] }
  have hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x := by
    intro c x
    ext a b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc, Matrix.smul_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [Algebra.smul_def]
  have hinj : Function.Injective j := by
    intro x y hxy
    ext a b
    have h := congrFun (congrFun hxy a) b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc] at h
    apply Algebra.TensorProduct.includeRight_injective (A := R) (B := E) hφ
    simpa [Algebra.TensorProduct.includeRight_apply] using h

  let σ := (LinearEquiv.sumArrowLequivProdArrow κ κ R R).symm
  have hσ : ∀ p : (κ → R) × (κ → R), σ p = Sum.elim p.1 p.2 := fun p => rfl
  have hcard : Module.finrank F (Matrix α β E) = Fintype.card (κ ⊕ κ) := by
    rw [Module.finrank_matrix, Fintype.card_sum, ← hc]
    ring
  have rat : ∀ (d : Darboux Bf κ), (∀ x : Matrix α β E, ∃ u v : κ → F,
      d.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) →
      ∀ x, ∃ u : κ ⊕ κ → F, (d.e.trans σ) (j x) = fun i => algebraMap F R (u i) := by
    intro d hd x
    obtain ⟨u, v, huv⟩ := hd x
    refine ⟨Sum.elim u v, ?_⟩
    simp only [LinearEquiv.trans_apply, j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ, huv]
    funext i
    cases i <;> rfl
  obtain ⟨g, hg⟩ := GlobalTheory.RatDarboux.exists_rat_matrix j hj hinj hcard (d₀.e.trans σ) (d₂.e.trans σ)
    (rat d₀ h₀) (rat d₂ h₂)
  simp only [LinearEquiv.trans_apply, hσ] at hg
  set G := g.map (algebraMap F R) with hG
  set JR : Matrix (κ ⊕ κ) (κ ⊕ κ) R := Matrix.fromBlocks 0 1 (-1) 0 with hJR

  have form : ∀ (d : Darboux Bf κ) w w',
      Bf w w' = Sum.elim (d.e w).1 (d.e w).2 ⬝ᵥ (JR *ᵥ Sum.elim (d.e w').1 (d.e w').2) := by
    intro d w w'
    rw [hJR, GlobalTheory.RatDarboux.std_form, d.form]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have pres : ∀ y y' : κ ⊕ κ → R, y ⬝ᵥ (JR *ᵥ y') = y ⬝ᵥ ((Gᵀ * JR * G) *ᵥ y') := by
    intro y y'
    obtain ⟨w, hw⟩ := (d₀.e.trans σ).surjective y
    obtain ⟨w', hw'⟩ := (d₀.e.trans σ).surjective y'
    simp only [LinearEquiv.trans_apply, hσ] at hw hw'
    have h := (form d₀ w w').symm.trans (form d₂ w w')
    rw [hg, hg, hw, hw'] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose G y, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  refine ⟨g, ?_, ?_⟩
  ·
    have hJmap : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = JR := by
      ext i k
      rcases i with i | i <;> rcases k with k | k <;>
        simp [hJR, Matrix.one_apply, apply_ite (algebraMap F R)]
    have key : (gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g).map (algebraMap F R) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJmap, ← hG]
      ext i k
      have h := pres (Pi.single i 1) (Pi.single k 1)
      simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
      exact h.symm
    exact Matrix.map_injective hφ key
  · intro w
    unfold GlobalTheory.AdelicSvN.act
    rw [← hG, ← hg w]
    exact Prod.ext (Sum.elim_comp_inl (d₂.e w).1 (d₂.e w).2).symm (Sum.elim_comp_inr (d₂.e w).1 (d₂.e w).2).symm

theorem exists_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β κ : Type) [Fintype α] [Fintype β]
  [Fintype κ] [DecidableEq κ] (Bf : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d₀ d₂ : Darboux Bf κ),
  Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₀.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₂.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
    ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  intro F E _ _ _ _ _ α β κ _ _ _ _ Bf d₀ d₂ hc h₀ h₂

  have : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  exact exists_rat_symplectic_gen (R := AF F) d₀ d₂ (incM F)
    (fun x a b => rfl) hc h₀ h₂

end GlobalTheory.RatDarboux
