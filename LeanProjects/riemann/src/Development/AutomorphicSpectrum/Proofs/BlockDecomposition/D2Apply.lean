import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfExt

section Gen

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Ext {N Q : Type} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R' Q] (c : N → Q) : Prop :=
  ∃ e : R' ⊗[R] N ≃ₗ[R'] Q, ∀ b, e (1 ⊗ₜ b) = c b

variable {R R'}

theorem Ext.pi {J : Type} [Finite J] {N Q : J → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module R' (Q i)] (c : ∀ i, N i → Q i) (h : ∀ i, Ext R R' (c i)) :
    Ext R R' (fun (f : ∀ i, N i) i ↦ c i (f i)) := by
  classical
  have := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' N).trans (LinearEquiv.piCongrRight e), fun b ↦ funext fun i ↦ ?_⟩
  simp [he]

variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]

variable (M) in

def tw (E : R' ⊗[R] N ≃ₗ[R'] Q) : M ⊗[R] N ≃+ M ⊗[R'] Q :=
  ((AlgebraTensorModule.cancelBaseChange R R' R' M N).symm.trans (LinearEquiv.lTensor M E)).toAddEquiv

theorem tw_tmul (E : R' ⊗[R] N ≃ₗ[R'] Q) (x : M) (n : N) : tw M E (x ⊗ₜ n) = x ⊗ₜ E (1 ⊗ₜ n) := by
  simp [tw]

theorem tw_nat (E : R' ⊗[R] N ≃ₗ[R'] Q) (E₂ : R' ⊗[R] N₂ ≃ₗ[R'] Q₂) (g : N →ₗ[R] N₂) (h : Q →ₗ[R'] Q₂)
    (H : ∀ n, h (E (1 ⊗ₜ n)) = E₂ (1 ⊗ₜ g n)) (t : M ⊗[R] N) :
    tw M E₂ (g.lTensor M t) = h.lTensor M (tw M E t) := by
  induction t with
  | zero => simp
  | tmul x n => simp [tw_tmul, H]
  | add a b ha hb => simp only [map_add, ha, hb]

end Gen

theorem QIsoAt.transport {R R' A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing R']
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R' A₀'] [Module R' A₁'] [Module R' A₂'] [Module R' B₀'] [Module R' B₁'] [Module R' B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R'] A₁'} {a₁' : A₁' →ₗ[R'] A₂'} {b₀' : B₀' →ₗ[R'] B₁'} {b₁' : B₁' →ₗ[R'] B₂'} {f' : A₁' →ₗ[R'] B₁'}
    (u₁ : A₁ ≃+ A₁') (u₂ : A₂ ≃+ A₂') (v₁ : B₁ ≃+ B₁') (v₂ : B₂ ≃+ B₂')
    (h₁ : ∀ x, u₂ (a₁ x) = a₁' (u₁ x)) (h₂ : ∀ z, v₂ (b₁ z) = b₁' (v₁ z)) (hf : ∀ x, v₁ (f x) = f' (u₁ x))
    (ha : ∀ y, ∃ y', a₀' y' = u₁ (a₀ y)) (hb : ∀ y, ∃ y', b₀' y' = v₁ (b₀ y)) (hb' : ∀ y', ∃ y, v₁ (b₀ y) = b₀' y')
    (q : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  obtain ⟨q₁, q₂⟩ := q
  refine ⟨fun x' hx ⟨y', hy⟩ ↦ ?_, fun z' hz ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := u₁.surjective x'
    obtain ⟨y, hy'⟩ := hb' y'
    obtain ⟨w, hw⟩ := q₁ x (u₂.injective (by rw [h₁, hx, map_zero]))
      ⟨y, v₁.injective (by rw [hy', hy, hf])⟩
    obtain ⟨w', hw'⟩ := ha w
    exact ⟨w', by rw [hw', hw]⟩
  · obtain ⟨z, rfl⟩ := v₁.surjective z'
    obtain ⟨x, y, hx, hy⟩ := q₂ z (v₂.injective (by rw [h₂, hz, map_zero]))
    obtain ⟨y', hy'⟩ := hb y
    exact ⟨u₁ x, y', by rw [← h₁, hx, map_zero], by rw [hy', ← hy, map_sub, hf]⟩

section Main

theorem bc_ext {R R' N Q : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R' Q] (g h : R' ⊗[R] N →ₗ[R'] Q) (H : ∀ n, g (1 ⊗ₜ n) = h (1 ⊗ₜ n)) : g = h := by
  refine LinearMap.ext fun t ↦ ?_
  induction t with
  | zero => simp
  | tmul r n =>
    have e : r ⊗ₜ[R] n = r • ((1 : R') ⊗ₜ[R] n) := by simp [TensorProduct.smul_tmul']
    rw [e, map_smul, map_smul, H]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem d2_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (z : C2 F)
    {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem ext0 (m : BC F F') : Ext R R' (fun (f : C0 F) T ↦ m.α T (f T) : C0 F → C0 F') :=
  Ext.pi (fun T b ↦ m.α T b) fun T ↦ m.bij T

theorem ext1 (m : BC F F') : Ext R R' (fun (f : C1 F) T T' φ ↦ m.α T' (f T T' φ) : C1 F → C1 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T')
    (fun T (g : ∀ (T' : C) (_ : T ⟶ T'), F.obj T') T' φ ↦ m.α T' (g T' φ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (_ : T ⟶ T'), F'.obj T')
    (fun T' (g : ∀ (_ : T ⟶ T'), F.obj T') φ ↦ m.α T' (g φ)) fun T' ↦
  Ext.pi (fun _ b ↦ m.α T' b) fun _ ↦ m.bij T'

theorem ext2 (m : BC F F') :
    Ext R R' (fun (f : C2 F) T T' T'' φ ψ ↦ m.α T'' (f T T' T'' φ ψ) : C2 F → C2 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T (g : ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T' T'' φ ψ ↦
      m.α T'' (g T' T'' φ ψ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T' (g : ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T'' φ ψ ↦
      m.α T'' (g T'' φ ψ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T'' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') φ ψ ↦ m.α T'' (g φ ψ)) fun T'' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T''), F'.obj T'')
    (fun φ (g : ∀ (_ : T' ⟶ T''), F.obj T'') ψ ↦ m.α T'' (g ψ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T'' b) fun _ ↦ m.bij T''

theorem ext3 (m : BC F F') :
    Ext R R' (fun (f : C3 F) T T' T'' T''' φ ψ χ ↦ m.α T''' (f T T' T'' T''' φ ψ χ) : C3 F → C3 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T (g : ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T' T'' T''' φ ψ χ ↦ m.α T''' (g T' T'' T''' φ ψ χ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T' (g : ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T'' T''' φ ψ χ ↦ m.α T''' (g T'' T''' φ ψ χ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T'' (g : ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T''' φ ψ χ ↦ m.α T''' (g T''' φ ψ χ)) fun T'' ↦
  Ext.pi (Q := fun T''' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T''' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') φ ψ χ ↦
      m.α T''' (g φ ψ χ)) fun T''' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun φ (g : ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') ψ χ ↦ m.α T''' (g ψ χ)) fun _ ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T'' ⟶ T'''), F'.obj T''')
    (fun ψ (g : ∀ (_ : T'' ⟶ T'''), F.obj T''') χ ↦ m.α T''' (g χ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T''' b) fun _ ↦ m.bij T'''

theorem perf_ext (m : BC F F') (h : Perf F) : Perf F' := by
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f₀, p₀⟩, ⟨f₁, p₁⟩, ⟨f₂, p₂⟩, ⟨f₃, p₃⟩, h₁₀, h₂₁, s₀, s₁,
    ⟨ψ₃, s₂⟩, hM⟩ := h
  obtain ⟨E₀, e₀⟩ := ext0 m
  obtain ⟨E₁, e₁⟩ := ext1 m
  obtain ⟨E₂, e₂⟩ := ext2 m
  obtain ⟨E₃, e₃⟩ := ext3 m
  have t₀ : ∀ x, d0 F' (E₀ (1 ⊗ₜ x)) = E₁ (1 ⊗ₜ d0 F x) := fun x ↦ by
    rw [e₀, e₁]
    funext T T' φ
    simp only [amitsur_d0_apply, map_sub, m.naturality]
  have t₁ : ∀ x, d1 F' (E₁ (1 ⊗ₜ x)) = E₂ (1 ⊗ₜ d1 F x) := fun x ↦ by
    rw [e₁, e₂]
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add, m.naturality]
  have t₂ : ∀ x, d2 F' (E₂ (1 ⊗ₜ x)) = E₃ (1 ⊗ₜ d2 F x) := fun x ↦ by
    rw [e₂, e₃]
    funext T T' T'' T''' φ ψ χ
    simp only [d2_apply, map_sub, map_add, m.naturality]
  refine ⟨.of R' (R' ⊗[R] P₀), .of R' (R' ⊗[R] P₁), .of R' (R' ⊗[R] P₂), .of R' (R' ⊗[R] P₃),
    a₀.baseChange R', a₁.baseChange R', a₂.baseChange R',
    E₀.toLinearMap ∘ₗ ψ₀.baseChange R', E₁.toLinearMap ∘ₗ ψ₁.baseChange R', E₂.toLinearMap ∘ₗ ψ₂.baseChange R',
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₀)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₀))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₁)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₁))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₂)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₂))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₃)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₃))⟩,
    ?_, ?_, ?_, ?_, ⟨E₃.toLinearMap ∘ₗ ψ₃.baseChange R', ?_⟩, fun M ↦ ?_⟩
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₁₀ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₂₁ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₀ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₀]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₁ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₁]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₂ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₂]
  · letI : Module R M := Module.compHom M (algebraMap R R')
    haveI : IsScalarTower R R' M := ⟨fun r s x ↦ by
      change (r • s) • x = (algebraMap R R' r) • (s • x)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨q₀, q₁, q₂⟩ := hM (ModuleCat.of R M)
    let r₀ : R' ⊗[R] P₀ ≃ₗ[R'] R' ⊗[R] P₀ := .refl _ _
    let r₁ : R' ⊗[R] P₁ ≃ₗ[R'] R' ⊗[R] P₁ := .refl _ _
    let r₂ : R' ⊗[R] P₂ ≃ₗ[R'] R' ⊗[R] P₂ := .refl _ _
    let r₃ : R' ⊗[R] P₃ ≃ₗ[R'] R' ⊗[R] P₃ := .refl _ _
    have nA₀ : ∀ t, tw M r₁ (a₀.lTensor M t) = (a₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ r₁ a₀ _ fun n ↦ by simp [r₀, r₁, LinearMap.baseChange_tmul]
    have nA₁ : ∀ t, tw M r₂ (a₁.lTensor M t) = (a₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ r₂ a₁ _ fun n ↦ by simp [r₁, r₂, LinearMap.baseChange_tmul]
    have nA₂ : ∀ t, tw M r₃ (a₂.lTensor M t) = (a₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ r₃ a₂ _ fun n ↦ by simp [r₂, r₃, LinearMap.baseChange_tmul]
    have nD₀ : ∀ t, tw M E₁ ((d0 F).lTensor M t) = (d0 F').lTensor M (tw M E₀ t) := tw_nat E₀ E₁ _ _ t₀
    have nD₁ : ∀ t, tw M E₂ ((d1 F).lTensor M t) = (d1 F').lTensor M (tw M E₁ t) := tw_nat E₁ E₂ _ _ t₁
    have nD₂ : ∀ t, tw M E₃ ((d2 F).lTensor M t) = (d2 F').lTensor M (tw M E₂ t) := tw_nat E₂ E₃ _ _ t₂
    have nP₀ : ∀ t, tw M E₀ (ψ₀.lTensor M t) =
        (E₀.toLinearMap ∘ₗ ψ₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ E₀ ψ₀ _ fun n ↦ by simp [r₀, LinearMap.baseChange_tmul]
    have nP₁ : ∀ t, tw M E₁ (ψ₁.lTensor M t) =
        (E₁.toLinearMap ∘ₗ ψ₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ E₁ ψ₁ _ fun n ↦ by simp [r₁, LinearMap.baseChange_tmul]
    have nP₂ : ∀ t, tw M E₂ (ψ₂.lTensor M t) =
        (E₂.toLinearMap ∘ₗ ψ₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ E₂ ψ₂ _ fun n ↦ by simp [r₂, LinearMap.baseChange_tmul]
    exact ⟨QIsoAt.transport (tw M r₀) (tw M r₁) (tw M E₀) (tw M E₁) nA₀ nD₀ nP₀
        (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) q₀,
      QIsoAt.transport (tw M r₁) (tw M r₂) (tw M E₁) (tw M E₂) nA₁ nD₁ nP₁
        (fun y ↦ ⟨tw M r₀ y, (nA₀ y).symm⟩) (fun y ↦ ⟨tw M E₀ y, (nD₀ y).symm⟩)
        (fun y ↦ ⟨(tw M E₀).symm y, by rw [nD₀, AddEquiv.apply_symm_apply]⟩) q₁,
      QIsoAt.transport (tw M r₂) (tw M r₃) (tw M E₂) (tw M E₃) nA₂ nD₂ nP₂
        (fun y ↦ ⟨tw M r₁ y, (nA₁ y).symm⟩) (fun y ↦ ⟨tw M E₁ y, (nD₁ y).symm⟩)
        (fun y ↦ ⟨(tw M E₁).symm y, by rw [nD₁, AddEquiv.apply_symm_apply]⟩) q₂⟩

end Main

theorem main : PerfBaseSt := by
  intro R _ P _ _ F h R' _ _ F' m
  haveI : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  exact perf_ext m h

end GlobalTheory.CompanionTheory.PerfExt
