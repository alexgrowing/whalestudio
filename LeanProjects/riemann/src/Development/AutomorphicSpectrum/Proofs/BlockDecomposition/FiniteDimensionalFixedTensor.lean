import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ExtTensorFixed

variable {G H V W X ι : Type} [DecidableEq ι] [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp

theorem coord_lTensor (b : Module.Basis ι ℂ X) (f : W →ₗ[ℂ] W) (y : X ⊗[ℂ] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (f.lTensor X y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b y i) := by
  induction y with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hx, hy]
  | tmul x w => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]

theorem mem_range_lTensor_fixed (σ : Representation ℂ G W) (K : Subgroup G) (y : X ⊗[ℂ] W)
    (hy : ∀ k : K, (σ (k : G)).lTensor X y = y) :
    y ∈ LinearMap.range ((fixed σ K).subtype.lTensor X) := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ X
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have hc : ∀ i, e y i ∈ fixed σ K := fun i => (mem_fixed_iff σ K _).2 fun k => by
    have h := coord_lTensor b (σ (k : G)) y i
    rw [hy k] at h
    exact h.symm
  have hy' : y = (e y).sum fun i n => b i ⊗ₜ[ℂ] n := by
    have h : e.symm (e y) = _ := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e y)
    exact (e.symm_apply_apply y).symm.trans h
  rw [hy']
  refine Submodule.sum_mem _ fun i _ => ⟨b i ⊗ₜ[ℂ] (⟨e y i, hc i⟩ : fixed σ K), ?_⟩
  simp

theorem fixed_le_range (ρ : Representation ℂ G V) (σ : Representation ℂ H W)
    (K₁ : Subgroup G) (K₂ : Subgroup H) :
    fixed (extTensor ρ σ) (K₁.prod K₂) ≤
      LinearMap.range (TensorProduct.map (fixed ρ K₁).subtype (fixed σ K₂).subtype) := by
  intro x hx
  have hx' := (mem_fixed_iff _ _ _).1 hx
  have act : ∀ (g : G × H) (z : V ⊗[ℂ] W),
      extTensor ρ σ g z = TensorProduct.map (ρ g.1) (σ g.2) z := by
    intro g z
    induction z with
    | zero => simp
    | add a c ha hc => simp [ha, hc]
    | tmul v w => simp

  have h1 : ∀ k : K₁, (ρ (k : G)).lTensor W (TensorProduct.comm ℂ V W x) =
      TensorProduct.comm ℂ V W x := by
    intro k
    have hk := hx' ⟨((k : G), 1), ⟨k.2, one_mem _⟩⟩
    rw [act] at hk
    conv_rhs => rw [← hk]
    simp only [map_one]
    generalize x = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨y', hy'⟩ := mem_range_lTensor_fixed ρ K₁ _ h1
  let y : (fixed ρ K₁) ⊗[ℂ] W := TensorProduct.comm ℂ W (fixed ρ K₁) y'
  have hy : (fixed ρ K₁).subtype.rTensor W y = x := by
    have : (fixed ρ K₁).subtype.rTensor W y =
        TensorProduct.comm ℂ W V ((fixed ρ K₁).subtype.lTensor W y') := by
      simp only [y]
      generalize y' = z
      induction z with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]
      | tmul v w => simp
    rw [this, hy']
    simp

  have hinj : Function.Injective ((fixed ρ K₁).subtype.rTensor W) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  have h2 : ∀ k : K₂, (σ (k : H)).lTensor (fixed ρ K₁) y = y := by
    intro k
    apply hinj
    have hk := hx' ⟨(1, (k : H)), ⟨one_mem _, k.2⟩⟩
    rw [act] at hk
    rw [hy]
    conv_rhs => rw [← hk, ← hy]
    simp only [map_one]
    generalize y = z
    induction z with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v w => simp
  obtain ⟨z, hz⟩ := mem_range_lTensor_fixed σ K₂ y h2
  refine ⟨z, ?_⟩
  rw [← hy, ← hz]
  generalize z = t
  induction t with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v w => simp

theorem finiteDimensional_fixed_extTensor : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H),
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) →
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  intro G H V W _ _ _ _ _ _ ρ σ K₁ K₂ h₁ h₂
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ σ K₁ K₂)

end GlobalTheory.CompanionTheory.ExtTensorFixed
