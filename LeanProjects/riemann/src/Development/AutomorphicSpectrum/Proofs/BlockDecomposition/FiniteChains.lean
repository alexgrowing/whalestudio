import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjectorStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfN

theorem QIsoAt.transport {R A₀ A₁ A₂ B₀ B₁ B₂ B₀' B₁' B₂' : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₀'] [AddCommGroup B₁']
    [AddCommGroup B₂'] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R B₀'] [Module R B₁'] [Module R B₂'] {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁}
    {b₁ : B₁ →ₗ[R] B₂} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'} {f : A₁ →ₗ[R] B₁}
    (v₀ : B₀ →ₗ[R] B₀') (v₁ : B₁ →ₗ[R] B₁') (v₂ : B₂ →ₗ[R] B₂')
    (s₀ : Function.Surjective v₀) (s₁ : Function.Bijective v₁) (s₂ : Function.Injective v₂)
    (c₀ : ∀ x, v₁ (b₀ x) = b₀' (v₀ x)) (c₁ : ∀ x, v₂ (b₁ x) = b₁' (v₁ x))
    (H : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀ a₁ b₀' b₁' (v₁ ∘ₗ f) := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := s₀ y
    exact H.1 x hx ⟨y, s₁.1 (by rw [c₀, hy]; rfl)⟩
  · obtain ⟨z, rfl⟩ := s₁.2 z
    obtain ⟨x, y, hx, hy⟩ := H.2 z (s₂ (by rw [c₁, hz, map_zero]))
    refine ⟨x, v₀ y, hx, ?_⟩
    rw [← c₀, ← hy, map_sub]; rfl

theorem finite_chains (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) := by
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun (c : Fin (n + 1) ⥤ Pᵒᵖ) (i : Fin (n + 1)) ↦ c.obj i) fun c c' h ↦ ?_
  exact CategoryTheory.Functor.ext (fun i ↦ congrFun h i) (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem flat_Cn {R : Type} [CommRing R] (P : Type) [PartialOrder P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
    (hF : ∀ T, Module.Flat R (F.obj T)) (n : ℕ) : Module.Flat R (Cn F n) := by
  have := finite_chains P n
  have := Fintype.ofFinite (Fin (n + 1) ⥤ Pᵒᵖ)
  classical
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R (Fin (n + 1) ⥤ Pᵒᵖ)
    (fun c ↦ F.obj (c.obj (Fin.last n)))).symm

theorem perfNoeth : CxSt → DictSt → PerfNoethSt := by
  intro hCx hD R _ P _ _ F hN hfl hf0 hfs
  obtain ⟨hd, -⟩ := hCx R Pᵒᵖ F
  obtain ⟨e₀, e₁, e₂, e₃, -, -, -, -, h0, h1, h2⟩ := hD R Pᵒᵖ F
  obtain ⟨e, h, B, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.chain_homotopy_finite_projector P F
  have := fun n ↦ flat_Cn P F hfl n
  obtain ⟨Q, ψ, f1, f2, f3, f4⟩ := GlobalTheory.T.homotopy_projector_complex_bounded (fun n ↦ Cn F n) (dn F) hd e h B i1 i2 i3 i4 i5 hf0 hfs
  have g₀ : ∀ x, e₁ (dn F 0 x) = d0 F (e₀ x) := h0
  have g₁ : ∀ x, e₂ (dn F 1 x) = d1 F (e₁ x) := h1
  have g₂ : ∀ x, e₃ (dn F 2 x) = d2 F (e₂ x) := h2
  have k : ∀ n x, ψ (n + 1) ((Q.d n (n + 1)).hom x) = dn F n (ψ n x) := fun n x ↦
    LinearMap.congr_fun (f3 n) x
  have lt : ∀ {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] [Module R A]
      [Module R B] [Module R A'] [Module R B'] (M : ModuleCat.{0} R) (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B')
      (b : A →ₗ[R] B) (b' : A' →ₗ[R] B'), (∀ x, v (b x) = b' (u x)) →
      ∀ x, (v : B →ₗ[R] B').lTensor M (b.lTensor M x) = b'.lTensor M ((u : A →ₗ[R] A').lTensor M x) := by
    intro A B A' B' _ _ _ _ _ _ _ _ M u v b b' h x
    have : (v : B →ₗ[R] B') ∘ₗ b = b' ∘ₗ (u : A →ₗ[R] A') := LinearMap.ext h
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, this]
  have bij : ∀ {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A'] (M : ModuleCat.{0} R)
      (u : A ≃ₗ[R] A'), Function.Bijective ((u : A →ₗ[R] A').lTensor M) := fun M u ↦
    (u.lTensor M).bijective
  refine ⟨Q.X 0, Q.X 1, Q.X 2, Q.X 3, (Q.d 0 1).hom, (Q.d 1 2).hom, (Q.d 2 3).hom, (e₀ : _ →ₗ[R] _) ∘ₗ ψ 0,
    (e₁ : _ →ₗ[R] _) ∘ₗ ψ 1, (e₂ : _ →ₗ[R] _) ∘ₗ ψ 2, ⟨f1 0, f2 0⟩, ⟨f1 1, f2 1⟩, ⟨f1 2, f2 2⟩, ⟨f1 3, f2 3⟩,
    ?_, ?_, ?_, ?_, ⟨(e₃ : _ →ₗ[R] _) ∘ₗ ψ 3, ?_⟩, fun M ↦ ?_⟩
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 0 1 2)
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 1 2 3)
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, k]
    exact g₀ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 1]; exact g₁ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 2]; exact g₂ _
  · obtain ⟨q0, qs⟩ := f4 M
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    exact ⟨QIsoAt.transport LinearMap.id _ _ Function.surjective_id (bij M e₀) (bij M e₁).1
        (fun x ↦ by simp) (lt M e₀ e₁ _ _ g₀) q0,
      QIsoAt.transport _ _ _ (bij M e₀).2 (bij M e₁) (bij M e₂).1 (lt M e₀ e₁ _ _ g₀) (lt M e₁ e₂ _ _ g₁) (qs 0),
      QIsoAt.transport _ _ _ (bij M e₁).2 (bij M e₂) (bij M e₃).1 (lt M e₁ e₂ _ _ g₁) (lt M e₂ e₃ _ _ g₂) (qs 1)⟩

end GlobalTheory.CompanionTheory.PerfN
