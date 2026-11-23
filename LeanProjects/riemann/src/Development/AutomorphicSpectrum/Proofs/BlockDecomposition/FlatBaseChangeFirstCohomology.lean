import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FlatBase

section Alg

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Bas {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M → M') : Prop :=
  ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ b, e (1 ⊗ₜ b) = f b

variable {R R'}

theorem Bas.pi {J : Type} [Finite J] {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i → M' i) (h : ∀ i, Bas R R' (f i)) :
    Bas R R' (fun (x : ∀ i, M i) i ↦ f i (x i)) := by
  classical
  haveI := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' M).trans (LinearEquiv.piCongrRight e), fun b ↦ ?_⟩
  funext i
  simp [he]

theorem flat_coh [Module.Flat R R'] {A₀ A₁ A₂ B₀ B₁ B₂ : Type} [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [Module R A₀] [Module R A₁] [Module R A₂] [AddCommGroup B₀] [AddCommGroup B₁]
    [AddCommGroup B₂] [Module R' B₀] [Module R' B₁] [Module R' B₂]
    (Z : Submodule R A₁) (Z' : Submodule R' B₁) (d₀ : A₀ →ₗ[R] Z) (d₁ : A₁ →ₗ[R] A₂)
    (d₀' : B₀ →ₗ[R'] Z') (d₁' : B₁ →ₗ[R'] B₂)
    (hZ : ∀ x, x ∈ Z ↔ d₁ x = 0) (hZ' : ∀ x, x ∈ Z' ↔ d₁' x = 0)
    (a₀ : A₀ → B₀) (a₁ : A₁ → B₁) (a₂ : A₂ → B₂)
    (h₀ : Bas R R' a₀) (h₁ : Bas R R' a₁) (h₂ : Bas R R' a₂)
    (c₀ : ∀ x, (d₀' (a₀ x)).1 = a₁ (d₀ x).1) (c₁ : ∀ x, d₁' (a₁ x) = a₂ (d₁ x))
    (p : (Z ⧸ LinearMap.range d₀) →ₛₗ[algebraMap R R'] (Z' ⧸ LinearMap.range d₀'))
    (hp : ∀ (z : Z) (z' : Z'), z'.1 = a₁ z.1 →
      p (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') :
    ∃ e : R' ⊗[R] (Z ⧸ LinearMap.range d₀) ≃ₗ[R'] (Z' ⧸ LinearMap.range d₀'),
      ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e₀, he₀⟩ := h₀
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  letI : Module R (Z' ⧸ LinearMap.range d₀') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (Z' ⧸ LinearMap.range d₀') :=
    ⟨fun r s x ↦ by
      change (r • s) • x = algebraMap R R' r • s • x
      rw [Algebra.smul_def, mul_smul]⟩
  let pl : (Z ⧸ LinearMap.range d₀) →ₗ[R] (Z' ⧸ LinearMap.range d₀') :=
    { toFun := p, map_add' := p.map_add, map_smul' := fun r x ↦ p.map_smulₛₗ r x }
  let L : R' ⊗[R] (Z ⧸ LinearMap.range d₀) →ₗ[R'] (Z' ⧸ LinearMap.range d₀') := pl.liftBaseChange R'
  have hL : ∀ c, L (1 ⊗ₜ c) = p c := fun c ↦ by
    simp only [L, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  have ta : ∀ (r : R') (x : A₁), e₁ (r ⊗ₜ x) = r • a₁ x := fun r x ↦ by
    rw [← he₁, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₀ : ∀ (r : R') (x : A₀), e₀ (r ⊗ₜ x) = r • a₀ x := fun r x ↦ by
    rw [← he₀, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₂ : ∀ (r : R') (x : A₂), e₂ (r ⊗ₜ x) = r • a₂ x := fun r x ↦ by
    rw [← he₂, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have a₂0 : a₂ 0 = 0 := by rw [← he₂, TensorProduct.tmul_zero, map_zero]

  have comm₁ : ∀ t, e₂ (d₁.baseChange R' t) = d₁' (e₁ t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₂, c₁]
    | add x y hx hy => simp only [map_add, hx, hy]
  have comm₀ : ∀ t, (d₀' (e₀ t)).1 = e₁ (Z.subtype.baseChange R' (d₀.baseChange R' t)) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₀, c₀]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  have mem : ∀ t, e₁ (Z.subtype.baseChange R' t) ∈ Z' := fun t ↦ by
    rw [hZ', ← comm₁]
    have : ∀ t, d₁.baseChange R' (Z.subtype.baseChange R' t) = 0 := fun t ↦ by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r x => simp [(hZ _).1 x.2]
      | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    rw [this, map_zero]
  let g : R' ⊗[R] Z →ₗ[R'] Z' :=
    LinearMap.codRestrict Z' (e₁.toLinearMap ∘ₗ Z.subtype.baseChange R') mem
  have hg : ∀ t, (g t).1 = e₁ (Z.subtype.baseChange R' t) := fun _ ↦ rfl
  have key : ∀ t, L ((LinearMap.range d₀).mkQ.baseChange R' t) = Submodule.Quotient.mk (g t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have hx : a₁ x.1 ∈ Z' := by
        rw [hZ', c₁, (hZ _).1 x.2, a₂0]
      rw [LinearMap.baseChange_tmul]
      simp only [L, LinearMap.liftBaseChange_tmul]
      have e1 : pl ((LinearMap.range d₀).mkQ x) = Submodule.Quotient.mk ⟨a₁ x.1, hx⟩ := hp x _ rfl
      rw [e1, ← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      simp [hg, ta]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]; rfl
  have hLs : Function.Surjective L := fun c' ↦ by
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
    have hex : Function.Exact Z.subtype d₁ := fun x ↦ by
      rw [← hZ]; simp
    have hex' := Module.Flat.lTensor_exact R' hex
    have h0 : d₁.lTensor R' (e₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply e₂.injective
      rw [comm₁, e₁.apply_symm_apply, map_zero]
      exact (hZ' _).1 z'.2
    obtain ⟨t, ht⟩ := (hex' _).1 h0
    rw [← LinearMap.baseChange_eq_ltensor] at ht
    refine ⟨(LinearMap.range d₀).mkQ.baseChange R' t, ?_⟩
    rw [key]
    congr 1
    apply Subtype.ext
    rw [hg, ht, e₁.apply_symm_apply]
  have hLi : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨t₀, rfl⟩ : ∃ t₀, (LinearMap.range d₀).mkQ.baseChange R' t₀ = t := by
      have := LinearMap.lTensor_surjective R' (g := (LinearMap.range d₀).mkQ)
        (Submodule.mkQ_surjective _)
      rw [← LinearMap.baseChange_eq_ltensor] at this
      exact this t
    rw [key, Submodule.Quotient.mk_eq_zero] at ht
    obtain ⟨y', hy'⟩ := ht
    have e1 : Z.subtype.baseChange R' (d₀.baseChange R' (e₀.symm y')) = Z.subtype.baseChange R' t₀ := by
      apply e₁.injective
      rw [← comm₀, e₀.apply_symm_apply, hy', hg]
    have inj : Function.Injective (Z.subtype.baseChange R') := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Z.injective_subtype
    rw [← inj e1]
    have : ∀ y, (LinearMap.range d₀).mkQ.baseChange R' (d₀.baseChange R' y) = 0 := fun y ↦ by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        have : (LinearMap.range d₀).mkQ (d₀ x) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
        simp [this]
      | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    exact this _
  exact ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩, hL⟩

end Alg

section Sys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'}

theorem flat_base_change_first_cohomology [Module.Flat R R'] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  have b : ∀ T, Bas R R' (m.α T) := m.bij
  have b₀ : Bas R R' (fun (x : C0 F) T ↦ m.α T (x T)) := Bas.pi _ b
  have b₁ : Bas R R' (fun (x : C1 F) T T' φ ↦ m.α T' (x T T' φ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F.obj T')
      (M' := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ _ : T ⟶ T', F.obj T') (M' := fun T' ↦ ∀ _ : T ⟶ T', F'.obj T') _ fun T' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ F.obj T') (M' := fun _ : T ⟶ T' ↦ F'.obj T') _ fun _ ↦ b T'
  have b₂ : Bas R R' (fun (x : C2 F) T T' T'' φ ψ ↦ m.α T'' (x T T' T'' φ ψ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T' ↦
    Bas.pi (M := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T'' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F.obj T'')
      (M' := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F'.obj T'') _ fun _ ↦
    Bas.pi (M := fun _ : T' ⟶ T'' ↦ F.obj T'') (M' := fun _ : T' ⟶ T'' ↦ F'.obj T'') _ fun _ ↦ b T''
  refine flat_coh (Z1 F) (Z1 F') ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (d1 F)
    ((d0 F').codRestrict (Z1 F') (commAlgFunctorCoboundaryZero_mem_cocyclesOne F')) (d1 F')
    (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) _ _ _ b₀ b₁ b₂ ?_ ?_
    m.coef.pull1 ?_
  · intro x
    funext T T' φ
    simp only [LinearMap.codRestrict_apply, amitsur_d0_apply, map_sub, m.naturality]
  · intro x
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add, m.naturality]
  · intro z z' h
    have : m.coef.pullbackOneCocycle z = z' := Subtype.ext h.symm
    rw [← this]
    rfl

end Sys

theorem flatBC : DescentSt → LowSt → SysBCSt → FlatBCSt := by
  intro hD hL hS R R' _ _ _ _ X X' s s' φ h hsep hqc
  haveI := hsep
  haveI := hqc
  haveI : CompactSpace X := by
    rw [← isCompact_univ_iff]
    simpa using QuasiCompact.isCompact_preimage (f := s) Set.univ isOpen_univ isCompact_univ
  obtain ⟨P, iP, fP, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys s
  obtain ⟨S', m, hm⟩ := hS R R' X X' s s' φ h hsep P S
  have hsep' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hsep
  obtain ⟨b, -, -⟩ := hL R _ _ _ _ _ (hD R X s hsep P S)
  obtain ⟨b', -, -⟩ := hL R' _ _ _ _ _ (hD R' X' s' hsep' P S')
  let E : HO1 s ≃ₗ[R] H1 (OSys s S) := LinearEquiv.ofBijective (resSys s S).pull1 b
  let E' : HO1 s' ≃ₗ[R'] H1 (OSys s' S') := LinearEquiv.ofBijective (resSys s' S').pull1 b'
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  obtain ⟨e, he⟩ := flat_base_change_first_cohomology m
  refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
    (e.trans E'.symm), fun c ↦ hm c _ ?_⟩
  have : E' ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
      (e.trans E'.symm) (1 ⊗ₜ c)) = e (1 ⊗ₜ E c) := by
    simp
  exact ((he _).symm.trans this.symm)

end GlobalTheory.CompanionTheory.Hodge.FlatBase
