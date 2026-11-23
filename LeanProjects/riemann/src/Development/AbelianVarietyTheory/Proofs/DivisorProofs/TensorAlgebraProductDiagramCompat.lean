import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.KunnethOne

theorem tensor_eq_zero_of_forall {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : V ⊗[K] W)
    (h : ∀ l : W →ₗ[K] K, TensorProduct.rid K V (LinearMap.lTensor V l t) = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K W
  have key : ∀ (j : Module.Free.ChooseBasisIndex K W) (s : V ⊗[K] W),
      TensorProduct.equivFinsuppOfBasisRight b s j =
        TensorProduct.rid K V (LinearMap.lTensor V (b.coord j) s) := by
    intro j s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext j
  rw [key, h, map_zero, Finsupp.zero_apply]

section Contr

variable {K : Type} [Field K] {Q : Type} [Category.{0} Q] (G : Q ⥤ CommAlgCat.{0} K)
  [Fintype Q] [DecidableEq Q] [∀ T T' : Q, Fintype (T ⟶ T')] [∀ T T' : Q, DecidableEq (T ⟶ T')]

def coef (Λ : C1 G →ₗ[K] K) (T T' : Q) (φ : T ⟶ T') : G.obj T' →ₗ[K] K :=
  Λ ∘ₗ LinearMap.single K (fun T => ∀ (T' : Q) (_ : T ⟶ T'), G.obj T') T ∘ₗ
    LinearMap.single K (fun T' => (T ⟶ T') → G.obj T') T' ∘ₗ
    LinearMap.single K (fun _ : T ⟶ T' => G.obj T') φ

def contr (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) :
    (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') →ₗ[K] M :=
  ∑ T, ∑ T', ∑ φ : T ⟶ T', (TensorProduct.rid K M).toLinearMap ∘ₗ
    LinearMap.lTensor M (coef G Λ T T' φ) ∘ₗ
    LinearMap.proj (R := K) (φ := fun _ : T ⟶ T' => M ⊗[K] G.obj T') φ ∘ₗ
    LinearMap.proj (R := K) (φ := fun T' => (T ⟶ T') → M ⊗[K] G.obj T') T' ∘ₗ
    LinearMap.proj (R := K) (φ := fun T => ∀ (T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') T

theorem contr_apply (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G M Λ c = ∑ T, ∑ T', ∑ φ : T ⟶ T',
      TensorProduct.rid K M (LinearMap.lTensor M (coef G Λ T T' φ) (c T T' φ)) := by
  simp [contr, LinearMap.sum_apply]

theorem contr_tmul (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K) (z : M)
    (h : C1 G) : contr G M Λ (fun T T' φ => z ⊗ₜ[K] h T T' φ) = Λ h • z := by
  rw [contr_apply]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, ← Finset.sum_smul]
  congr 1
  simp only [coef, LinearMap.comp_apply, ← map_sum]
  congr 1
  simp only [LinearMap.single_apply, Finset.univ_sum_single]

theorem contr_natural (M N : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Λ : C1 G →ₗ[K] K) (h : M →ₗ[K] N) (c : ∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :
    contr G N Λ (fun T T' φ => LinearMap.rTensor (G.obj T') h (c T T' φ)) = h (contr G M Λ c) := by
  simp only [contr_apply, map_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ =>
    Finset.sum_congr rfl fun φ _ => ?_
  induction c T T' φ using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add u v hu hv => simp only [map_add, hu, hv]

theorem kunneth_contraction_d0_vanishes (M : Type) [AddCommGroup M] [Module K M] (Λ : C1 G →ₗ[K] K)
    (hΛ : ∀ g : C0 G, Λ (d0 G g) = 0) (w : ∀ T : Q, M ⊗[K] G.obj T) :
    contr G M Λ (fun T T' φ => LinearMap.lTensor M (mp G φ).toLinearMap (w T) - w T') = 0 := by
  let D : (∀ T : Q, M ⊗[K] G.obj T) →ₗ[K] (∀ (T T' : Q) (_ : T ⟶ T'), M ⊗[K] G.obj T') :=
    LinearMap.pi fun T => LinearMap.pi fun T' => LinearMap.pi fun φ =>
      LinearMap.lTensor M (mp G φ).toLinearMap ∘ₗ
        LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T -
      LinearMap.proj (R := K) (φ := fun T => M ⊗[K] G.obj T) T'
  have hD : contr G M Λ ∘ₗ D = 0 := by
    refine LinearMap.pi_ext fun T₀ x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      have e : D (Pi.single T₀ (z ⊗ₜ[K] u)) =
          fun T T' φ => z ⊗ₜ[K] (-d0 G (Pi.single T₀ u : C0 G) T T' φ) := by
        funext T T' φ
        simp only [D, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.proj_apply, amitsur_d0_apply, neg_sub, TensorProduct.tmul_sub]
        by_cases h1 : T = T₀ <;> by_cases h2 : T' = T₀
        · subst h1; subst h2; simp
        · subst h1; simp [Pi.single_eq_of_ne h2]
        · subst h2; simp [Pi.single_eq_of_ne h1]
        · simp [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
      have c := contr_tmul G M Λ z (-d0 G (Pi.single T₀ u : C0 G))
      simp only [Pi.neg_apply] at c
      rw [LinearMap.comp_apply, e, c, map_neg, hΛ, neg_zero, zero_smul, LinearMap.zero_apply]
    | add u v hu hv => simp only [Pi.single_add, map_add, hu, hv]
  exact LinearMap.congr_fun hD w

end Contr

end GlobalTheory.CatCoh.KunnethOne

namespace GlobalTheory.CatCoh.KunnethOne

theorem sum_tmul_eq_zero_of_cup : ∀ (K : Type) [Field K] (P Q : Type) [Category.{0} P] [Category.{0} Q] [Finite Q] [Quiver.IsThin Q] (F : P ⥤ CommAlgCat.{0} K) (G : Q ⥤ CommAlgCat.{0} K) (E : P × Q ⥤ CommAlgCat.{0} K) (i₁ : ∀ T : P × Q, F.obj T.1 →ₐ[K] E.obj T) (i₂ : ∀ T : P × Q, G.obj T.2 →ₐ[K] E.obj T), (∀ (T T' : P × Q) (a : T ⟶ T') (b : F.obj T.1), i₁ T' (mp F a.1 b) = mp E a (i₁ T b)) → (∀ (T T' : P × Q) (a : T ⟶ T') (b : G.obj T.2), i₂ T' (mp G a.2 b) = mp E a (i₂ T b)) → (∀ T, Function.Bijective (Algebra.TensorProduct.productMap (i₁ T) (i₂ T))) → ∀ (n : ℕ) (x : Fin n → Z1 F) (y : Fin n → Z1 G) (f : C1 E), (∀ (T T' T'' : P × Q) (a : T ⟶ T') (b : T' ⟶ T''), d1 E f T T' T'' a b = ∑ i, mp E b (i₁ T' ((x i).1 _ _ a.1)) * i₂ T'' ((y i).1 _ _ b.2)) → ∑ i, GlobalTheory.CatCoh.H1.mk F (x i) ⊗ₜ[K] GlobalTheory.CatCoh.H1.mk G (y i) = 0 := by
  intro K _ P Q _ _ _ _ F G E i₁ i₂ h₁ h₂ hb n x y f hf
  classical
  haveI := Fintype.ofFinite Q
  haveI : ∀ T T' : Q, Fintype (T ⟶ T') := fun _ _ => Fintype.ofFinite _
  apply tensor_eq_zero_of_forall
  intro l
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (l ∘ₗ H1.mk G)
  have hΛy : ∀ z : Z1 G, Λ z.1 = l (H1.mk G z) := fun z => LinearMap.congr_fun hΛ z
  have hΛd : ∀ g : C0 G, Λ (d0 G g) = 0 := fun g => by
    have e := hΛy ⟨d0 G g, commAlgFunctorCoboundaryZero_mem_cocyclesOne G g⟩
    rw [e, H1.mk_eq_zero.2 ⟨g, rfl⟩, map_zero]
  simp only [← hΛy, ← map_smul, ← map_sum]
  rw [H1.mk_eq_zero]
  let β : ∀ T : P × Q, F.obj T.1 ⊗[K] G.obj T.2 ≃ₐ[K] E.obj T :=
    fun T => AlgEquiv.ofBijective _ (hb T)
  have hβ : ∀ (T : P × Q) (z : F.obj T.1) (u : G.obj T.2), β T (z ⊗ₜ u) = i₁ T z * i₂ T u :=
    fun T z u => Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have natL : ∀ (p p' : P) (T : Q) (a : p ⟶ p') (t : F.obj p ⊗[K] G.obj T),
      β (p', T) (LinearMap.rTensor (G.obj T) (mp F a).toLinearMap t) =
        mp E ((a, 𝟙 T) : (p, T) ⟶ (p', T)) (β (p, T) t) := by
    intro p p' T a t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.rTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p', T), ← h₂ (p, T) (p', T)]
      simp [mp_id]
    | add u v hu hv => simp only [map_add, hu, hv]
  have natR : ∀ (p : P) (T T' : Q) (b : T ⟶ T') (t : F.obj p ⊗[K] G.obj T),
      β (p, T') (LinearMap.lTensor (F.obj p) (mp G b).toLinearMap t) =
        mp E ((𝟙 p, b) : (p, T) ⟶ (p, T')) (β (p, T) t) := by
    intro p T T' b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z u =>
      rw [LinearMap.lTensor_tmul, hβ, hβ, map_mul, ← h₁ (p, T) (p, T'), ← h₂ (p, T) (p, T')]
      simp [mp_id]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨fun p => contr G (F.obj p) Λ
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T')))), ?_⟩
  funext p p' a
  rw [amitsur_d0_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have step : ∀ (T T' : Q) (b : T ⟶ T'),
      (β (p', T')).symm (f (p', T) (p', T') ((𝟙 p', b) : (p', T) ⟶ (p', T'))) -
        LinearMap.rTensor (G.obj T') (mp F a).toLinearMap
          ((β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, b) : (p, T) ⟶ (p, T')))) =
      ∑ i, (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' b -
        (LinearMap.lTensor (F.obj p') (mp G b).toLinearMap
            ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
          (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T')))) := by
    intro T T' b
    apply (β (p', T')).injective
    have H1 := hf (p, T) (p', T) (p', T') (a, 𝟙 T) (𝟙 p', b)
    have H2 := hf (p, T) (p, T') (p', T') (𝟙 p, b) (a, 𝟙 T')
    rw [d1_apply] at H1 H2
    simp only [prod_comp, Category.comp_id, Category.id_comp] at H1 H2
    simp only [Z1.id, map_zero, zero_mul, Finset.sum_const_zero] at H2
    simp only [← h₁, mp_id] at H1
    simp only [map_sub, map_sum, AlgEquiv.apply_symm_apply, natL, natR, hβ]
    linear_combination H1 - H2
  have nat := contr_natural G (F.obj p) (F.obj p') Λ (mp F a).toLinearMap
    (fun T T' φ => (β (p, T')).symm (f (p, T) (p, T') ((𝟙 p, φ) : (p, T) ⟶ (p, T'))))
  rw [AlgHom.toLinearMap_apply] at nat
  rw [← nat, ← map_sub]
  trans contr G (F.obj p') Λ ((∑ i, fun T T' φ => (x i).1 p p' a ⊗ₜ[K] (y i).1 T T' φ) -
    fun T T' φ => LinearMap.lTensor (F.obj p') (mp G φ).toLinearMap
        ((β (p', T)).symm (f (p, T) (p', T) ((a, 𝟙 T) : (p, T) ⟶ (p', T)))) -
      (β (p', T')).symm (f (p, T') (p', T') ((a, 𝟙 T') : (p, T') ⟶ (p', T'))))
  · congr 1
    funext T T' b
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact step T T' b
  · rw [map_sub, kunneth_contraction_d0_vanishes _ _ _ hΛd, sub_zero, map_sum]
    simp only [contr_tmul]

end GlobalTheory.CatCoh.KunnethOne
